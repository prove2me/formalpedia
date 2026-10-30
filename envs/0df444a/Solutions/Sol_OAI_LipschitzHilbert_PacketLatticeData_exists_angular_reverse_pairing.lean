-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:16:25.337628+00:00
-- url     : https://prove2.me/submissions/e2d924e8-627a-435f-af76-08bd41dfb889

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_exists_ordinary_capped_removal_step

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteEnergySchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted energy summation for the smooth/dyadic comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_sum_norm_square {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    ‖∑ j, v j‖ ^ 2 ≤ (∑ j, w j) * ∑ j, ‖v j‖ ^ 2 / w j := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := w) (g := fun j => ‖v j‖ ^ 2 / w j) (r := fun j => ‖v j‖)
    (fun j _ => (hw j).le) (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
    (fun j _ => by rw [mul_div_cancel₀ _ (hw j).ne'])
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

theorem weighted_integral_sum_square {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] (μ : Measure Ω)
    (F : ι → Ω → E) (hF : ∀ j, MemLp (F j) 2 μ)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    (∫ x, ‖∑ j, F j x‖ ^ 2 ∂μ) ≤
      (∑ j, w j) * ∑ j, (∫ x, ‖F j x‖ ^ 2 ∂μ) / w j := by
  have hsum : MemLp (fun x => ∑ j, F j x) 2 μ := by
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun j _ => hF j)
  have hint (j : ι) : Integrable (fun x => ‖F j x‖ ^ 2 / w j) μ :=
    ((hF j).integrable_norm_pow (by decide : 2 ≠ 0)).div_const _
  calc
    _ ≤ ∫ x, (∑ j, w j) * ∑ j, ‖F j x‖ ^ 2 / w j ∂μ :=
      integral_mono (hsum.integrable_norm_pow (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun j _ => hint j)).const_mul _)
        (fun x => weighted_sum_norm_square (fun j => F j x) w hw)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact integral_div _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact energy orthogonality of the separated annuli used in the comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem norm_sum_square_of_disjoint {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (v : ι → E)
    (h : ∀ j k, j ≠ k → v j = 0 ∨ v k = 0) :
    ‖∑ j, v j‖ ^ 2 = ∑ j, ‖v j‖ ^ 2 := by
  classical
  by_cases hz : ∀ j, v j = 0
  · simp [hz]
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    have ho (k : ι) (hkj : k ≠ j) : v k = 0 := (h k j hkj).resolve_right hj
    rw [Finset.sum_eq_single j (fun k _ hkj => ho k hkj) (fun hj => (hj (Finset.mem_univ j)).elim)]
    rw [Finset.sum_eq_single j (fun k _ hkj => by rw [ho k hkj]; simp)
      (fun hj => (hj (Finset.mem_univ j)).elim)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CoordinateFourierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by the line coordinate preserves Fourier support for
Schwartz functions. This is the first step in polynomial localization of
the annular packet variation estimate. -/

noncomputable section

open MeasureTheory Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem coordinateProduct_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    coordinateProduct f x = (x : ℂ) * f x := by
  simpa only [coordinateProduct, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal f x

theorem fourier_coordinate_derivative (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (𝓕 f) =
      (-2 * Real.pi * Complex.I : ℂ) • 𝓕 (coordinateProduct f) := by
  have hxf : Integrable (fun x : ℝ => x • f x) := by
    have hcp : Integrable (coordinateProduct f : ℝ → ℂ) volume := (coordinateProduct f).integrable
    convert hcp using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    rw [coordinateProduct_apply, Complex.real_smul]
  have h := Real.deriv_fourier f.integrable hxf
  have hprod : (fun x : ℝ => (-2 * Real.pi * Complex.I * x : ℂ) • f x) =
      ((-2 * Real.pi * Complex.I : ℂ) • coordinateProduct f : SchwartzMap ℝ ℂ) := by
    funext x
    simp only [smul_apply, coordinateProduct_apply, smul_eq_mul]
    ring
  ext x
  change deriv (𝓕 (f : ℝ → ℂ)) x = _
  rw [h, hprod]
  simp only [← SchwartzMap.fourier_coe, fourier_smul, smul_apply]

theorem coordinateProduct_fourier_support (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (coordinateProduct f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hout
  have hz : deriv (𝓕 f : SchwartzMap ℝ ℂ) x = 0 := deriv_of_notMem_tsupport hout
  have hd := congrArg (fun g : SchwartzMap ℝ ℂ => g x) (fourier_coordinate_derivative f)
  simp only [SchwartzMap.derivCLM_apply, smul_apply, smul_eq_mul, hz] at hd
  have hc : (-2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hf0 : 𝓕 (coordinateProduct f) x = 0 := (mul_eq_zero.mp hd.symm).resolve_left hc
  exact hx hf0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive polynomial weights used to localize annular packets on a
reference line. Their construction and Fourier support preservation are
proved here for the actual Schwartz functions. -/

noncomputable section

open Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem fourier_support_add_subset (f g : SchwartzMap ℝ ℂ) {S : Set ℝ}
    (hS : IsClosed S)
    (hf : tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ S)
    (hg : tsupport ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ S) :
    tsupport ((𝓕 (f + g) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ S := by
  apply closure_minimal _ hS
  intro x hx
  by_contra hout
  have hf0 : 𝓕 f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hf h))
  have hg0 : 𝓕 g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hg h))
  apply hx
  have heq : (𝓕 (f + g) : SchwartzMap ℝ ℂ) = 𝓕 f + 𝓕 g := fourier_add f g
  rw [heq]
  change 𝓕 f x + 𝓕 g x = 0
  rw [hf0, hg0, add_zero]

theorem fourier_support_smul_subset (c : ℂ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (c • f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  rw [fourier_smul]
  exact tsupport_smul_subset_right (fun _ => c) _

theorem centeredCoordinateProduct_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    centeredCoordinateProduct a f x = ((x - a : ℝ) : ℂ) * f x := by
  simp only [centeredCoordinateProduct, add_apply, smul_apply, coordinateProduct_apply,
    smul_eq_mul, Complex.ofReal_sub]
  ring

theorem centeredCoordinateProduct_fourier_support (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (centeredCoordinateProduct a f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
  fourier_support_add_subset _ _ isClosed_closure
    (coordinateProduct_fourier_support f) (fourier_support_smul_subset _ f)

theorem quadraticLocalization_apply (a r : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    quadraticLocalization a r f x = ((1 + (x - a) ^ 2 / r ^ 2 : ℝ) : ℂ) * f x := by
  simp only [quadraticLocalization, add_apply, smul_apply, smul_eq_mul,
    centeredCoordinateProduct_apply, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_inv]
  ring

theorem quadraticLocalization_fourier_support (a r : ℝ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (quadraticLocalization a r f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  apply fourier_support_add_subset _ _ isClosed_closure (Set.Subset.refl _)
  exact (fourier_support_smul_subset _ _).trans
    ((centeredCoordinateProduct_fourier_support a _).trans
      (centeredCoordinateProduct_fourier_support a f))

theorem polynomialLocalization_apply (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    polynomialLocalization a r q f x = (polynomialWeight a r q x : ℂ) * f x := by
  induction q with
  | zero => simp [polynomialLocalization, polynomialWeight]
  | succ q ih =>
    rw [polynomialLocalization, quadraticLocalization_apply, ih]
    simp only [polynomialWeight, pow_succ, Complex.ofReal_mul]
    ring

theorem polynomialWeight_one_le (a r : ℝ) (q : ℕ) (x : ℝ) :
    1 ≤ polynomialWeight a r q x := by
  have hbase : 1 ≤ 1 + (x - a) ^ 2 / r ^ 2 := by
    have h := div_nonneg (sq_nonneg (x - a)) (sq_nonneg r)
    linarith
  exact one_le_pow₀ hbase

theorem polynomialLocalization_fourier_support (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (polynomialLocalization a r q f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  induction q with
  | zero => exact Set.Subset.refl _
  | succ q ih => exact (quadraticLocalization_fourier_support a r _).trans ih

theorem fourier_support_annulus (f : SchwartzMap ℝ ℂ) (lo hi : ℝ)
    (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) :
    tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      {ξ | lo ≤ |ξ| ∧ |ξ| ≤ hi} := by
  apply closure_minimal
  · intro ξ hξ
    exact ⟨le_of_not_gt (fun h => hξ (hlow ξ h)),
      le_of_not_gt (fun h => hξ (hhigh ξ h))⟩
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)

theorem polynomialLocalization_low (a r : ℝ) (q : ℕ) (f : SchwartzMap ℝ ℂ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (polynomialLocalization a r q f) ξ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_le_of_gt hξ) ((fourier_support_annulus f lo hi hlow hhigh)
    (polynomialLocalization_fourier_support a r q f hmem)).1

theorem polynomialLocalization_high (a r : ℝ) (q : ℕ) (f : SchwartzMap ℝ ℂ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (polynomialLocalization a r q f) ξ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_le_of_gt hξ) ((fourier_support_annulus f lo hi hlow hhigh)
    (polynomialLocalization_fourier_support a r q f hmem)).2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem polynomial_base_le (x s a l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    1 + (x - a) ^ 2 / r ^ 2 ≤ 4 * (1 + ((x - s) / l) ^ 2) := by
  have hu : |(x - s) / r| ≤ |(x - s) / l| := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hl]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl hlr
  have hv : |(s - a) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hsa
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  simp only [sq_abs, one_pow] at hu2 hv2
  have heq : (x - a) / r = (x - s) / r + (s - a) / r := by ring
  rw [← div_pow, heq]
  nlinarith [sq_nonneg ((x - s) / r - (s - a) / r), sq_nonneg ((x - s) / l)]

theorem polynomialWeight_sq_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    polynomialWeight a r q x ^ 2 * lineEnvelope s l (n + 2 * q) x ≤
      16 ^ q * lineEnvelope s l n x := by
  let B := 1 + ((x - s) / l) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase := polynomial_base_le x s a l r hl hr hlr hsa
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (x - a) ^ 2 / r ^ 2)
    hbase (2 * q)
  have hweight : polynomialWeight a r q x ^ 2 = (1 + (x - a) ^ 2 / r ^ 2) ^ (2 * q) := by
    simp only [polynomialWeight, ← pow_mul, Nat.mul_comm q 2]
  rw [hweight]
  calc
    _ ≤ (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 16 ^ q * lineEnvelope s l n x := by
      change (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ = 16 ^ q * (B ^ n)⁻¹
      rw [mul_pow, pow_add, mul_inv_rev, ← mul_assoc]
      have hz : B ^ (2 * q) ≠ 0 := pow_ne_zero _ hB.ne'
      have hc : (4 : ℝ) ^ (2 * q) = 16 ^ q := by rw [pow_mul]; norm_num
      rw [mul_assoc ((4 : ℝ) ^ (2 * q)), mul_inv_cancel₀ hz, mul_one, hc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem envelope_synthesis_square {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ι → ℂ) (f : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, w i ≤ D)
    (henv : ∀ i, ‖f i‖ ≤ C * w i) :
    ‖∑ i, c i • f i‖ ^ 2 ≤ D * C ^ 2 * ∑ i, ‖c i‖ ^ 2 * w i := by
  have hterm (i : ι) : ‖c i • f i‖ ^ 2 / w i ≤ C ^ 2 * (‖c i‖ ^ 2 * w i) := by
    rw [norm_smul, mul_pow]
    apply (div_le_iff₀ (hw i)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (henv i) 2
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖c i‖)
    nlinarith
  calc
    _ ≤ (∑ i, w i) * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      weighted_sum_norm_square _ w hw
    _ ≤ D * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      mul_le_mul_of_nonneg_right hover (Finset.sum_nonneg (fun i _ =>
        div_nonneg (sq_nonneg _) (hw i).le))
    _ ≤ D * ∑ i, C ^ 2 * (‖c i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hD
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

theorem polynomial_packetSynthesis_energy {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (s rho : ι → ℝ)
    (a l r C D : ℝ) (q : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hrho : ∀ i, 0 < rho i)
    (hcenter : ∀ i, |s i - a| ≤ r) (hD : 0 ≤ D)
    (hover : ∀ x, ∑ i, rho i * lineEnvelope (s i) l (1 + 2 * q) x ≤ D)
    (henv : ∀ i x, ‖f i x‖ ≤ C * (rho i * lineEnvelope (s i) l (1 + 2 * q) x)) :
    (∫ x, ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2) ≤
      D * C ^ 2 * 16 ^ q * (Real.pi * l) * ∑ i, ‖c i‖ ^ 2 * rho i := by
  have hE (i : ι) (x : ℝ) : 0 < rho i * lineEnvelope (s i) l (1 + 2 * q) x := by
    unfold lineEnvelope
    exact mul_pos (hrho i) (inv_pos.mpr (pow_pos (by positivity) _))
  have hpoint (x : ℝ) : ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2 ≤
      D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x := by
    have hsyn := envelope_synthesis_square c (fun i => f i x)
      (fun i => rho i * lineEnvelope (s i) l (1 + 2 * q) x)
      (fun i => hE i x) hD (hover x) (fun i => henv i x)
    have hn : ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2 =
        polynomialWeight a r q x ^ 2 * ‖∑ i, c i • f i x‖ ^ 2 := by
      rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans zero_le_one (polynomialWeight_one_le a r q x)),
        mul_pow, packetSynthesis_apply]
      simp only [smul_eq_mul]
    rw [hn]
    calc
      _ ≤ polynomialWeight a r q x ^ 2 * (D * C ^ 2 *
          ∑ i, ‖c i‖ ^ 2 * (rho i * lineEnvelope (s i) l (1 + 2 * q) x)) :=
        mul_le_mul_of_nonneg_left hsyn (sq_nonneg _)
      _ = D * C ^ 2 * ∑ i, (‖c i‖ ^ 2 * rho i) *
          (polynomialWeight a r q x ^ 2 * lineEnvelope (s i) l (1 + 2 * q) x) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (sq_nonneg C))
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left
          (polynomialWeight_sq_mul_envelope x (s i) a l r q 1 hl hr hlr (hcenter i))
          (mul_nonneg (sq_nonneg ‖c i‖) (hrho i).le)
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        ring
  have hi (i : ι) : Integrable
      (fun x => (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x) :=
    (integrable_lineEnvelope_one (s i) l hl).const_mul _
  calc
    _ ≤ ∫ x, D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x :=
      integral_mono (((polynomialLocalization a r q (packetSynthesis c f)).memLp 2 volume).integrable_norm_pow
        (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
      simp_rw [integral_const_mul, integral_lineEnvelope_one _ l hl]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring

theorem packetSynthesis_fourier {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (packetSynthesis c f) ξ = ∑ i, c i * 𝓕 (f i) ξ := by
  have heq : (𝓕 (packetSynthesis c f) : SchwartzMap ℝ ℂ) = ∑ i, c i • 𝓕 (f i) := by
    rw [packetSynthesis, fourier_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact fourier_smul (c i) (f i)
  rw [heq]
  simp only [sum_apply, smul_apply, smul_eq_mul]

theorem packetSynthesis_fourier_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ)
    (hf : ∀ i, 𝓕 (f i) ξ = 0) : 𝓕 (packetSynthesis c f) ξ = 0 := by
  rw [packetSynthesis_fourier]
  simp only [hf, mul_zero, Finset.sum_const_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineTiling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

theorem tiledLineGrid_root (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) :
    (tiledLineGrid origin H hH G N hG k).root =
      Ico (origin + k * H) (origin + (k + 1 : ℤ) * H) := by
  unfold FiniteLineGrid.root tiledLineGrid
  congr 1
  push_cast
  ring

theorem tiledLineGrid_pairwise_disjoint (origin H : ℝ) (hH : 0 < H) (G N : ℕ)
    (hG : 0 < G) :
    Pairwise fun i j => Disjoint (tiledLineGrid origin H hH G N hG i).root
      (tiledLineGrid origin H hH G N hG j).root := by
  intro i j hij
  simp only [tiledLineGrid_root]
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hi.2, hj.1]
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hj.2, hi.1]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite lattice overlap bound from the actual line integral of
the rational envelope. No cardinality factor or implicit lattice assumption
is used. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators

namespace LipschitzHilbert

theorem lineEnvelope_cell_comparison (x k y : ℝ) (hy : y ∈ Ico k (k + 1)) :
    lineEnvelope x 1 1 k ≤ 4 * lineEnvelope x 1 1 y := by
  have hdelta : (y - k) ^ 2 ≤ 1 := by
    have ha : |y - k| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha
    simpa only [sq_abs, one_pow] using hs
  have hb : 1 + (y - x) ^ 2 ≤ 4 * (1 + (k - x) ^ 2) := by
    nlinarith [sq_nonneg ((k - x) - (y - k)), sq_nonneg (k - x)]
  simp only [lineEnvelope, div_one, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hb)

theorem lineEnvelope_le_cell_integral (x k : ℝ) :
    lineEnvelope x 1 1 k ≤ 4 * ∫ y in Ico k (k + 1), lineEnvelope x 1 1 y := by
  have hint : IntegrableOn (lineEnvelope x 1 1) (Ico k (k + 1)) :=
    (integrable_lineEnvelope_one x 1 (by norm_num)).integrableOn
  have hfinite : volume (Ico k (k + 1)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have h := setIntegral_mono_on (integrableOn_const hfinite : IntegrableOn
      (fun _ : ℝ => lineEnvelope x 1 1 k) (Ico k (k + 1)) volume)
    (hint.const_mul 4) measurableSet_Ico (fun y hy => lineEnvelope_cell_comparison x k y hy)
  rw [integral_const_mul] at h
  simpa [setIntegral_const, Real.volume_Ico, measureReal_def] using h

theorem finite_line_lattice_overlap (x : ℝ) (s : Finset ℤ) :
    (∑ k ∈ s, lineEnvelope x 1 1 k) ≤ 4 * Real.pi := by
  classical
  have hint := integrable_lineEnvelope_one x 1 (by norm_num)
  have hd : (s : Set ℤ).Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) (k + 1)) := by
    intro i _ j _ hij
    have h := tiledLineGrid_pairwise_disjoint 0 1 (by norm_num) 2 0 (by norm_num) hij
    simpa only [tiledLineGrid_root, Int.cast_add, Int.cast_one, mul_one, zero_add] using h
  have hsum := integral_biUnion_finset s (fun _ _ => measurableSet_Ico) hd
    (fun _ _ => hint.integrableOn)
  calc
    _ ≤ ∑ k ∈ s, 4 * ∫ y in Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y :=
      Finset.sum_le_sum (fun k _ => lineEnvelope_le_cell_integral x k)
    _ = 4 * ∫ y in ⋃ k ∈ s, Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ 4 * ∫ y, lineEnvelope x 1 1 y := by
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
        (Filter.Eventually.of_forall (lineEnvelope_nonneg x 1 1))) (by norm_num)
    _ = 4 * Real.pi := by rw [integral_lineEnvelope_one x 1 (by norm_num), mul_one]

theorem lineEnvelope_lattice_rescale (a l x : ℝ) (hl : l ≠ 0) (k : ℤ) (n : ℕ) :
    lineEnvelope (a + l * k) l n x = lineEnvelope ((x - a) / l) 1 n k := by
  unfold lineEnvelope
  congr 3
  simp only [div_one]
  have h : (x - (a + l * k)) / l = -((k : ℝ) - (x - a) / l) := by
    field_simp
    ring
  rw [h, neg_sq]

theorem finite_plane_lattice_overlap (x y : ℝ) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2) ≤
      (4 * Real.pi) ^ 2 := by
  classical
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  calc
    _ ≤ ∑ p ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd),
        lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    _ = (∑ i ∈ s.image Prod.fst, lineEnvelope x 1 1 i) *
        ∑ j ∈ s.image Prod.snd, lineEnvelope y 1 1 j := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (4 * Real.pi) * (4 * Real.pi) :=
      mul_le_mul (finite_line_lattice_overlap x _) (finite_line_lattice_overlap y _)
        (Finset.sum_nonneg (fun j _ => lineEnvelope_nonneg _ _ _ _)) (by positivity)
    _ = _ := (pow_two _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TileLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform overlap for actual rectangular tile-center lattices, allowing
arbitrary horizontal and vertical scales and finite subfamilies. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finite_scaled_plane_lattice_overlap (a b l W x y : ℝ)
    (hl : l ≠ 0) (hW : W ≠ 0) (s : Finset (ℤ × ℤ)) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ p ∈ s, lineEnvelope (a + l * p.1) l m x *
      lineEnvelope (b + W * p.2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  calc
    _ ≤ ∑ p ∈ s, lineEnvelope ((x - a) / l) 1 1 p.1 *
        lineEnvelope ((y - b) / W) 1 1 p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [lineEnvelope_lattice_rescale a l x hl p.1 m,
        lineEnvelope_lattice_rescale b W y hW p.2 n]
      exact mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hn)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    _ ≤ _ := finite_plane_lattice_overlap _ _ s

theorem injective_tile_lattice_overlap {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y : ℝ) (hl : l ≠ 0) (hW : W ≠ 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ i, lineEnvelope (a + l * (index i).1) l m x *
      lineEnvelope (b + W * (index i).2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  classical
  have h := finite_scaled_plane_lattice_overlap a b l W x y hl hW
    (Finset.univ.image index) hm hn
  rw [Finset.sum_image (fun _ _ _ _ heq => hinj heq)] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_WeightedPacketEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially localized packet synthesis energy with arbitrary dual
coefficients. No local coefficient budget is assumed here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_component_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (rho : ι → ℝ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2 * rho i) = ∑ i, ‖c i‖ ^ 2 * rho i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]

theorem weighted_packet_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
    (a0 b0 a r W y C : ℝ) (hr : 0 < r) (hW : 0 < W)
    (hlen : ∀ j, 0 < len j) (hlenr : ∀ j, ∀ _ : ι j, len j ≤ r)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i = a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i = b0+W*(site j i).2)
    (hcenter : ∀ j i, |X j i-a| ≤ r)
    (hf : ∀ j i k x, ‖f j i k x‖ ≤ C *
      (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 3 y)) :
    (∑ j, ∑ k, ∫ x, ‖polynomialLocalization a r 1
      (packetSynthesis (fun i => c j i k) (fun i => f j i k)) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * C^2 * 16 * Real.pi) *
        ∑ j, len j * ∑ i, ‖c j i‖ ^ 2 * lineEnvelope (Z j i) W 3 y := by
  let D := (4 * Real.pi)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hscalar (j : Fin N) (k : κ) :
      (∫ x, ‖polynomialLocalization a r 1
        (packetSynthesis (fun i => c j i k) (fun i => f j i k)) x‖ ^ 2) ≤
        (D * C^2 * 16 * Real.pi) * len j *
          ∑ i, ‖c j i k‖ ^ 2 * lineEnvelope (Z j i) W 3 y := by
    classical
    by_cases hj : Nonempty (ι j)
    swap
    · let : IsEmpty (ι j) := ⟨fun i => hj ⟨i⟩⟩
      simp [packetSynthesis, polynomialLocalization_apply]
    have hrho (i : ι j) : 0 < lineEnvelope (Z j i) W 3 y := by unfold lineEnvelope; positivity
    have hover (x : ℝ) : (∑ i, lineEnvelope (Z j i) W 3 y * lineEnvelope (X j i) (len j) 3 x) ≤ D := by
      simp_rw [hX,hZ]
      simpa only [D, mul_comm] using injective_tile_lattice_overlap (site j) (hinj j)
        a0 b0 (len j) W x y (hlen j).ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3)
    have h := polynomial_packetSynthesis_energy (fun i => c j i k) (fun i => f j i k)
      (X j) (fun i => lineEnvelope (Z j i) W 3 y) a (len j) r C D 1
      (hlen j) hr (hlenr j (Classical.choice hj)) hrho (hcenter j) hD hover
      (fun i x => by simpa only [show 1 + 1 * 2 = (3 : ℕ) from rfl, mul_comm] using hf j i k x)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    _ ≤ ∑ j, ∑ k, (D * C^2 * 16 * Real.pi) * len j *
        ∑ i, ‖c j i k‖ ^ 2 * lineEnvelope (Z j i) W 3 y :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hscalar j k))
    _ = _ := by
      simp_rw [← Finset.mul_sum, weighted_component_energy]
      simp only [D, ← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hilbert duality for coefficients defined by actual analyzing
integrals. The self-pairing uses the same selected synthesizing packets. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ] [Fintype κ]

omit [Fintype σ] [Fintype κ] in
theorem analyzingCoefficient_mul_area (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0) (i : σ) (k : κ) :
    (area i : ℂ) * analyzingCoefficient μ area wave g i k =
      ∫ z, g z k * conj (wave i k z) ∂μ := by
  change (area i : ℂ) * (((area i)⁻¹ : ℂ) * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (show (area i : ℂ) ≠ 0 by exact_mod_cast ha i), one_mul]

theorem analyzingCoefficient_self_pairing (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0)
    (hint : ∀ i k, Integrable (fun z => g z k * conj (wave i k z)) μ) :
    ((∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 : ℝ) : ℂ) =
      ∫ z, inner ℂ (diagonalSynthesis wave (analyzingCoefficient μ area wave g) z) (g z) ∂μ := by
  let a := analyzingCoefficient μ area wave g
  have hterm (i : σ) : ((area i * ‖a i‖^2 : ℝ) : ℂ) =
      ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
    have hnorm : (‖a i‖ : ℂ)^2 = inner ℂ (a i) (a i) :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a i)).symm
    rw [Complex.ofReal_mul, Complex.ofReal_pow, hnorm]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← analyzingCoefficient_mul_area μ area wave g ha i k]
    ring
  have hInt (i : σ) (k : κ) :
      Integrable (fun z => conj (a i k) * (g z k * conj (wave i k z))) μ :=
    (hint i k).const_mul _
  calc
    _ = ∑ i, ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∫ z, ∑ i, ∑ k, conj (a i k) * (g z k * conj (wave i k z)) ∂μ := by
      simp_rw [← integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum _ (fun k _ => hInt i k))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [diagonalSynthesis, PiLp.inner_apply, RCLike.inner_apply,
        map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact four-term polarization of a cross packet coefficient and
synthesizing wave. Both packets may have different planar profiles. -/

noncomputable section
namespace LipschitzHilbert

theorem packet_cross_polarization (a b f g : ℂ) :
    (a+b)*(f+g) - (a-b)*(f-g) -
        Complex.I*((a-Complex.I*b)*(f+Complex.I*g)) +
        Complex.I*((a+Complex.I*b)*(f-Complex.I*g)) = 4*(a*g) := by
  ring_nf
  simp [Complex.I_sq]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CoefficientPolarization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Antilinearity of the actual analyzing integral supplies the
coefficients in the four-term packet polarization identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω]

theorem analyzingCoefficient_add_smul (μ : Measure Ω) (area : σ → ℝ)
    (f h : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (c : ℂ)
    (hf : ∀ s k, Integrable (fun z => g z k*conj (f s k z)) μ)
    (hh : ∀ s k, Integrable (fun z => g z k*conj (h s k z)) μ) (s : σ) :
    analyzingCoefficient μ area (fun s k z => f s k z+c*h s k z) g s =
      analyzingCoefficient μ area f g s + conj c • analyzingCoefficient μ area h g s := by
  ext k
  change ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z+c*h s k z) ∂μ) =
    ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z) ∂μ) +
      conj c*(((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (h s k z) ∂μ))
  have heq : (fun z => g z k*conj (f s k z+c*h s k z)) =
      (fun z => g z k*conj (f s k z)+conj c*(g z k*conj (h s k z))) := by
    funext z
    simp only [map_add,map_mul]
    ring
  rw [heq,integral_add (hf s k) ((hh s k).const_mul (conj c)),integral_const_mul]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlicedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From almost-everywhere line estimates to planar estimates, including
the area-preserving coordinates of a fixed reference slope. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem integral_slopeShear (s : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f (slopeShear s z) ∂volume.prod volume) = ∫ z, f z ∂volume.prod volume :=
  (slopeShear_measurePreserving s).integral_comp (slopeShear s).measurableEmbedding f

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem integral_planeDivide (f : ℝ × ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∫ z, f (planeDivide a b ha hb z) ∂volume.prod volume) =
      (|a| * |b|) * ∫ z, f z ∂volume.prod volume := by
  rw [← integral_map_equiv (planeDivide a b ha hb), map_planeDivide, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

/-- Exact area scaling: all dependence on the box and the dilation is
`K² * length * width`, while the remaining integral is a fixed constant. -/
theorem integral_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    (∫ z, T.weight K D z ∂volume.prod volume) =
      (2 ^ D * ∫ z, topProfile D z ∂volume.prod volume) *
        K ^ 2 * T.length * T.width := by
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq, integral_const_mul, integral_sub_right_eq_self]
  simp only [Function.comp_apply]
  rw [integral_slopeShear (-T.slope) (fun z => topProfile D
    (planeDivide (K * T.length) (K * T.width)
      (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)),
    integral_planeDivide, abs_of_pos (mul_pos hK T.length_pos),
    abs_of_pos (mul_pos hK T.width_pos)]
  ring

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual geometry behind the density keeper assignment: intersecting
angular cells give slope control, and intersecting slope boxes then give
the required spatial enlargement. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem density_angular_cell_slope {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k) (hinter : (DyadicLineGrid.cell q k i ∩ DyadicLineGrid.cell q l j).Nonempty)
    (hs : s ∈ DyadicLineGrid.cell q k i) (ht : t ∈ DyadicLineGrid.cell q l j) :
    |s-t| ≤ DyadicLineGrid.scale k := by
  have ht' := DyadicLineGrid.cell_subset_of_intersect hlk
    (by simpa only [inter_comm] using hinter) ht
  have hnext : DyadicLineGrid.left q k (i+1) =
      DyadicLineGrid.left q k i+DyadicLineGrid.scale k := by
    unfold DyadicLineGrid.left
    push_cast
    ring
  change DyadicLineGrid.left q k i ≤ s ∧ s < DyadicLineGrid.left q k (i+1) at hs
  change DyadicLineGrid.left q k i ≤ t ∧ t < DyadicLineGrid.left q k (i+1) at ht'
  rw [hnext] at hs ht'
  exact abs_le.mpr ⟨by linarith [hs.1,ht'.2],by linarith [hs.2,ht'.1]⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityScaledForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular grid has physical scale w/topLength. Keeping that scale
explicit allows arbitrary vertical band width and dyadic source lengths. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

theorem scaledAngularCell_measurable (unit : ℝ) (q k j : ℤ) :
    MeasurableSet (scaledAngularCell unit q k j) :=
  measurableSet_Ico.preimage (measurable_id.div_const unit)

theorem scaledAngularCell_slope {unit : ℝ} (hunit : 0 < unit) {q k l i j : ℤ} {s t : ℝ}
    (hlk : l ≤ k)
    (hinter : (scaledAngularCell unit q k i ∩ scaledAngularCell unit q l j).Nonempty)
    (hs : s ∈ scaledAngularCell unit q k i) (ht : t ∈ scaledAngularCell unit q l j) :
    |s-t| ≤ unit*DyadicLineGrid.scale k := by
  obtain ⟨v,hv,hv'⟩ := hinter
  have h := density_angular_cell_slope hlk ⟨v/unit,hv,hv'⟩ hs ht
  rw [←sub_div,abs_div,abs_of_pos hunit] at h
  simpa only [mul_comm] using (div_le_iff₀ hunit).mp h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlopeLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

theorem labelAtSlot_at {A : Type*} {B : ℕ} (e : A ↪ Fin B) (i : A) :
    labelAtSlot e (e i) = some i := by
  classical
  unfold labelAtSlot
  split_ifs with h
  · congr 1
    exact e.injective h.choose_spec
  · exact (h ⟨i, rfl⟩).elim

theorem labelAtSlot_eq_some {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    (b : Fin B) (i : A) : labelAtSlot e b = some i ↔ e i = b := by
  classical
  constructor
  · unfold labelAtSlot
    split_ifs with h
    · intro hi
      have heq : h.choose = i := Option.some.inj hi
      simpa only [heq] using h.choose_spec
    · simp
  · intro hi
    rw [← hi]
    exact labelAtSlot_at e i

theorem slotItem_label {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    {Item : A → Type*} {b : Fin B} (p : SlotItem e Item b) :
    labelAtSlot e b = some p.1.1 :=
  (labelAtSlot_eq_some e b p.1.1).mpr p.2

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedLattice
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual source lattices with several labels at each scale split into
the uniformly many slots constructed in `SourceSlopeLabels`. No packets
are inserted at an empty scale. The selected profiles, physical centers,
carrier frequencies and spectra are unchanged. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

/-- Splitting by slots is an exact identity for arbitrary finite packet
sums, not an estimate and not a change to the waves. -/
theorem sum_slotted {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E) :
    (∑ b : Fin B, ∑ p : P.SlotItem hcard b j, f p.1.1 p.1.2) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have h := Equiv.sum_comp (P.slotItemsEquiv hcard j)
    (fun p : Σ l : P.labels j, Item j l => f p.1 p.2)
  change (∑ p : Σ b : Fin B, P.SlotItem hcard b j, f p.2.1.1 p.2.1.2) =
    ∑ p : Σ l : P.labels j, Item j l, f p.1 p.2 at h
  simpa only [Fintype.sum_sigma] using h

theorem slotValue_item (b : Fin B) (j : Fin N) (f : P.labels j → ℝ)
    (p : P.SlotItem hcard b j) : P.slotValue hcard b j f = f p.1.1 := by
  unfold slotValue
  rw [SourceSlopeLabels.slotItem_label (P.slotEmbedding hcard j) p]
  rfl

@[simp] theorem slotted_actualX (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualX j p = P.actualX j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originX j) + P.length j * (P.site j p.1.1 p.1.2).1 = _
  rw [P.slotValue_item hcard b j (P.originX j) p]
  rfl

@[simp] theorem slotted_actualZ (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).actualZ j p = P.actualZ j p.1.1 p.1.2 := by
  change P.slotValue hcard b j (P.originZ j) +
    P.slotValue hcard b j (P.rowSlope j) * P.length j * (P.site j p.1.1 p.1.2).1 +
      P.width * (P.site j p.1.1 p.1.2).2 = _
  rw [P.slotValue_item hcard b j (P.originZ j) p,
    P.slotValue_item hcard b j (P.rowSlope j) p]
  rfl

theorem slotted_rowSlope (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    (P.slotted hcard b).rowSlope j = P.rowSlope j p.1.1 :=
  P.slotValue_item hcard b j (P.rowSlope j) p

@[simp] theorem slotted_raw (b : Fin B) (i : Fin 3) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) (y : ℝ) :
    (P.slotted hcard b).raw i j p k y = P.raw i j p.1.1 p.1.2 k y := by
  unfold SourceLatticePacket.raw raw
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

@[simp] theorem slotted_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    (P.slotted hcard b).physicalPacket t j p k = P.physicalPacket t j p.1.1 p.1.2 k := by
  unfold SourceLatticePacket.physicalPacket physicalPacket
  simp only [P.slotted_actualX hcard, P.slotted_actualZ hcard, P.slotted_length hcard,
    P.slotted_rowSlope hcard b j p]
  rfl

theorem slotted_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ j l u k ξ η,
      planarAngularFourier (P.physicalPacket t j l u k) (ξ, η) ≠ 0 →
        |ξ + (t + P.rowSlope j l) * η| ≤ cStar / P.length j ∧
          cEta ≤ w * η ∧ w * η ≤ CEta)
    (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) (k : κ) (ξ η : ℝ) :
    planarAngularFourier ((P.slotted hcard b).physicalPacket t j p k) (ξ, η) ≠ 0 →
      |ξ + (t + (P.slotted hcard b).rowSlope j) * η| ≤
          cStar / (P.slotted hcard b).length j ∧
        cEta ≤ w * η ∧ w * η ≤ CEta := by
  simpa only [P.slotted_physicalPacket hcard, P.slotted_rowSlope hcard b j p,
    P.slotted_length hcard] using hspectrum j p.1.1 p.1.2 k ξ η

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The density kernel has a quantitative tail outside a dilated slope
box. This turns a weighted density test into the unweighted witness used
by the finite keeper construction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace LipschitzHilbert
namespace SlopeBox

theorem densityKernel_nonneg (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    0 ≤ T.densityKernel D z := Real.rpow_nonneg (by linarith [T.radius_nonnegative z]) _

theorem densityKernel_eq_weight (T : SlopeBox) (D : ℝ) (z : ℝ×ℝ) :
    T.densityKernel D z = ((2:ℝ)^D)⁻¹*T.weight 1 D z := by
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [densityKernel,weight,div_one,←mul_assoc,inv_mul_cancel₀ htwo,one_mul]

theorem densityKernel_integrable (T : SlopeBox) {D : ℝ} (hD : 2 < D) :
    Integrable (T.densityKernel D) (volume.prod volume) := by
  have h := (T.weight_integrable (by norm_num : (0:ℝ)<1) hD).const_mul (((2:ℝ)^D)⁻¹)
  exact h.congr (Eventually.of_forall (fun z => (T.densityKernel_eq_weight D z).symm))

theorem integral_densityKernel (T : SlopeBox) (D : ℝ) :
    (∫ z, T.densityKernel D z ∂volume.prod volume) =
      (∫ z, topProfile D z ∂volume.prod volume)*T.area := by
  simp_rw [T.densityKernel_eq_weight D]
  rw [integral_const_mul,T.integral_weight (by norm_num : (0:ℝ)<1) D]
  have htwo : (2:ℝ)^D ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) D).ne'
  simp only [one_pow,mul_one,SlopeBox.area]
  field_simp [htwo]

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDensityModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary density is the supremum of the manuscript's actual
weighted box tests. Exceeding a threshold supplies a concrete test, which
can then be fed to the finite keeper construction. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem densityAverage_le (T : SlopeBox) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ)
    (omega : Set ℝ) : densityAverage T E u omega ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  unfold densityAverage
  apply (div_le_iff₀ T.area_pos).mpr
  have h := setIntegral_le_integral (s := E ∩ u ⁻¹' omega)
    (T.densityKernel_integrable (by norm_num : (2:ℝ)<203))
    (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
  exact h.trans_eq (T.integral_densityKernel 203)

namespace OrdinaryDensityTile

theorem densityValues_nonempty (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    (tile.densityValues ell0 w W tau q E u).Nonempty := ⟨0,Or.inl rfl⟩

theorem densityValues_bddAbove (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    BddAbove (tile.densityValues ell0 w W tau q E u) := by
  refine ⟨∫ z, topProfile 203 z ∂volume.prod volume,?_⟩
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

theorem density_le (tile : OrdinaryDensityTile) (ell0 w W tau : ℝ) (q : ℤ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) :
    tile.density ell0 w W tau q E u ≤ ∫ z, topProfile 203 z ∂volume.prod volume := by
  apply csSup_le (tile.densityValues_nonempty ell0 w W tau q E u)
  intro x hx
  rcases hx with rfl | ⟨test,rfl⟩
  · exact integral_nonneg (topProfile_nonnegative 203)
  · exact densityAverage_le test.top E u _

end OrdinaryDensityTile
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change the reference direction of an actual translated source
lattice. Profiles, sites and physical packets are preserved exactly.
The reference-cone and width hypotheses imply the new shear and carrier
bounds; the absolute raw envelope is independent of the carrier bound. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

variable (delta M : ℝ) (hM : 0 ≤ M)
  (hshear : ∀ j, |(P.rowSlope j+delta)*P.length j/P.width| ≤ 1)
  (hcarrier : ∀ j k, |P.frequency k*(P.rowSlope j+delta)*P.length j| ≤ M)

/-- Unlike derivative bounds, the raw absolute envelope has no carrier
factor, even when the reference cone is much wider than a main annulus. -/
theorem raw_absolute_envelope (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤
      ((2^P.order*P.profileBound)*P.ratioBound^2)*
        (lineEnvelope (P.actualX j u) (P.length j) P.order x*
          lineEnvelope (P.actualZ j u) P.width P.order y) := by
  let C := P.ratioBound^2*P.profileBound
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) P.profileBound_pos.le
  have hprofile : ∀ z, ‖planarProfileJet (P.profile j u k) (P.scale/P.width) i z‖ ≤ C*
      (lineEnvelope 0 1 (2*P.order) z.1*lineEnvelope 0 1 (2*P.order) z.2) := by
    intro z
    exact (planar_profile_envelope (P.profile j u k) (2*P.order) (P.scale/P.width)
      P.ratioBound P.ratioBound_ge_one P.scale_bound i z).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (P.profile_bound j u k) (sq_nonneg _))
        (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have h := modulatedPlanarSlice_envelope (planarProfileJet (P.profile j u k) (P.scale/P.width) i)
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
    y C (P.length_pos j).ne' P.order hC (P.raw_shear_bound j) hprofile x
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [raw,modulatedPlanarJet,div_eq_mul_inv,C])
  ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarFixedScaleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-length synthesis estimate in section 3. A single translated
box lattice has bounded overlap. Summing squared bin components gives a
constant independent of the number of packets and frequency bins. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem planarFixedSynthesis_memLp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (planarFixedSynthesis c f) 2 (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact memLp_finsetSum _ (fun i _ => ((f i k).memLp 2 (volume.prod volume)).const_mul (c i k))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceThreeGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal three-grid covering lemma for the nested alternating
one-third grids. It supplies the interval comparison in the maximal
kernel estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert.DyadicLineGrid

theorem shift_signed_third (k : ℤ) : shift (k.negOnePow:ℤ) k=1/3 := by
  simp only [shift,←Units.val_mul,Int.units_mul_self,Units.val_one,Int.cast_one]

theorem signed_third_in_range (k : ℤ) : (k.negOnePow:ℤ)∈Finset.Icc (-1) 1 := by
  rw [Finset.mem_Icc]
  exact abs_le.mp (le_of_eq (Int.abs_negOnePow k))

/-- A closed interval of radius less than one sixth of a grid cell
fits in a cell of one of the three fixed nested grids. -/
theorem exists_three_grid_cover (k : ℤ) (c r : ℝ) (_hr : 0 ≤ r)
    (hsmall : 6*r < scale k) :
    ∃ q∈Finset.Icc (-1) 1, ∃ j : ℤ, Icc (c-r) (c+r)⊆cell q k j := by
  let m := index 0 k c
  let a := left 0 k m
  have hc := mem_index_cell 0 k c
  have hright : left 0 k (m+1)=a+scale k := by
    dsimp [a,left,shift]
    push_cast
    ring
  change a ≤ c ∧ c<left 0 k (m+1) at hc
  rw [hright] at hc
  by_cases hleft : a ≤ c-r
  · by_cases hend : c+r<a+scale k
    · refine ⟨0,by simp, m,?_⟩
      intro x hx
      exact ⟨hleft.trans hx.1,hx.2.trans_lt (by simpa only [hright] using hend)⟩
    · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m,?_⟩
      intro x hx
      change left (k.negOnePow:ℤ) k m≤x ∧ x<left (k.negOnePow:ℤ) k (m+1)
      have hl : left (k.negOnePow:ℤ) k m=a+scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      have hu : left (k.negOnePow:ℤ) k (m+1)=a+4*scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      rw [hl,hu]
      constructor <;> linarith [hx.1,hx.2]
  · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m-1,?_⟩
    intro x hx
    change left (k.negOnePow:ℤ) k (m-1)≤x ∧
      x<left (k.negOnePow:ℤ) k (m-1+1)
    have hl : left (k.negOnePow:ℤ) k (m-1)=a-2*scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    have hu : left (k.negOnePow:ℤ) k (m-1+1)=a+scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    rw [hl,hu]
    constructor <;> linarith [hx.1,hx.2]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem gridChoice_card : Fintype.card GridChoice=3 := by
  simp [GridChoice]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceTransverseTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining transverse tail in the long-tree density estimate:
412 powers in squared energy absorb twice the density loss 203, leaving
the summable sixth power. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem transverseTailConstant_nonneg : 0≤transverseTailConstant :=
  tsum_nonneg (fun _ => by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarSeparatedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality of separated reference-frequency strips on the plane.
The proof uses the actual Fourier transform of each affine line slice,
then integrates the one-dimensional Plancherel identity. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert

theorem schwartz_energy_fourier_disjoint {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ)
    (hdisjoint : ∀ ξ i j, i ≠ j → 𝓕 (f i) ξ = 0 ∨ 𝓕 (f j) ξ = 0) :
    (∫ x, ‖∑ i, f i x‖^2) = ∑ i, ∫ x, ‖f i x‖^2 := by
  let F : SchwartzMap ℝ ℂ := ∑ i, f i
  have hsum (x : ℝ) : F x = ∑ i, f i x := by simp [F]
  have hfourier (ξ : ℝ) : 𝓕 F ξ = ∑ i, 𝓕 (f i) ξ := by
    change (SchwartzMap.fourierTransformCLM ℂ (∑ i, f i)) ξ = _
    rw [map_sum]
    simp
  calc
    _ = ∫ x, ‖F x‖^2 := by simp only [hsum]
    _ = ∫ ξ, ‖𝓕 F ξ‖^2 := (SchwartzMap.integral_norm_sq_fourier F).symm
    _ = ∫ ξ, ∑ i, ‖𝓕 (f i) ξ‖^2 := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [hfourier,norm_sum_square_of_disjoint _ (hdisjoint ξ)]
    _ = ∑ i, ∫ ξ, ‖𝓕 (f i) ξ‖^2 :=
      integral_finsetSum _ (fun i _ => ((𝓕 (f i)).memLp 2).integrable_norm_pow (by decide))
    _ = _ := by simp only [SchwartzMap.integral_norm_sq_fourier]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicAnnularSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed number of residue classes separates the dyadic annuli in
the ordinary synthesis estimate. The number depends only on the two
fixed annular constants, independently of the number of scales. -/

noncomputable section
namespace LipschitzHilbert

theorem exists_dyadic_annular_separation {lower upper : ℝ} (hlower : 0 < lower) :
    ∃ q : ℕ, 0 < q ∧ ∀ j k : ℕ, j < k → j % q = k % q →
      upper*(2:ℝ)^j < lower*(2:ℝ)^k := by
  obtain ⟨q,hq⟩ := pow_unbounded_of_one_lt (upper/lower) (by norm_num : (1:ℝ) < 2)
  let Q := max 1 q
  have hQ : 0 < Q := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
  have hbase : upper < lower*(2:ℝ)^Q := by
    have hpow : (2:ℝ)^q ≤ 2^Q :=
      pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    simpa only [mul_comm] using (div_lt_iff₀ hlower).mp (hq.trans_le hpow)
  refine ⟨Q,hQ,?_⟩
  intro j k hjk hmod
  have hdiv : Q ∣ k-j := Nat.ModEq.dvd' hmod
  have hle : Q ≤ k-j := Nat.le_of_dvd (Nat.sub_pos_of_lt hjk) hdiv
  have hindex : Q+j ≤ k := by omega
  calc
    upper*(2:ℝ)^j < (lower*2^Q)*2^j :=
      mul_lt_mul_of_pos_right hbase (by positivity)
    _ = lower*(2:ℝ)^(Q+j) := by rw [pow_add]; ring
    _ ≤ lower*(2:ℝ)^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hindex) hlower.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLatticeMultiscaleEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary multiscale energy estimate for the original physical
lattice packets. Residue coloring has a fixed cost determined only by
the annular constants, not the number of lengths or vector bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

/-- The cutoff at one retained coefficient needs only that packet's
selector separation; all other coefficients may vanish. -/
theorem raw_fourier_cutoffs_at (P : SourceLatticePacket N κ ι)
    (t w cStar cEta CEta cb Cb : ℝ) (hw : 0 < w)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (j : Fin N) (u : ι j) (k : κ)
    (hspectrum : ∀ ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η) ≠ 0 →
      |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧ cEta ≤ w*η ∧ w*η ≤ CEta)
    (hselector : cb*w/P.length j ≤ |P.rowSlope j| ∧ |P.rowSlope j| ≤ Cb*w/P.length j)
    (i : Fin 3) (y : ℝ) :
    (∀ ξ, |ξ| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 (P.raw i j u k y) ξ = 0) ∧
    (∀ ξ, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |ξ| →
      𝓕 (P.raw i j u k y) ξ = 0) := by
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j)| ∧
      |t-(t+P.rowSlope j)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j) = -P.rowSlope j := by ring
    simpa only [heq,abs_neg] using hselector
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j u k)
    y t (t+P.rowSlope j) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb hspectrum hsel (P.frequency k) P.scale i
  have hraw : P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale i) y t :=
    P.raw_eq_physical_slice i j u k y t
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [SourceLatticePacket.length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← hraw,heq,heq] at h
  exact h

/-- The qualitative L² assertion accompanies the numerical estimate. -/
theorem physicalMultiscaleSynthesis_memLp (P : SourceLatticePacket N κ ι)
    (t : ℝ) (c : ∀ j, ι j → EuclideanSpace ℂ κ) :
    MemLp (fun z => ∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z)
      2 (volume.prod volume) :=
  memLp_finsetSum _ (fun j _ => planarFixedSynthesis_memLp (c j) (P.physicalPacket t j))

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMultiscaleEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finitely labeled family inherits multiscale synthesis
through its exact slot partition. The only additional factor is the
explicit fixed label bound, with no scale or vector-dimension loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalLabeledSynthesis_memLp (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    MemLp (P.physicalLabeledSynthesis t c) 2 (volume.prod volume) :=
  memLp_finsetSum _ (fun _ _ => planarFixedSynthesis_memLp _ _)

theorem physicalLabeledSynthesis_eq_slots (P : SourceLabeledLattice N κ Label Item)
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ s : Fin B, ∑ j, planarFixedSynthesis
      (fun u : P.SlotItem hcard s j => c j u.1.1 u.1.2)
      ((P.slotted hcard s).physicalPacket t j) z) = P.physicalLabeledSynthesis t c z := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,planarFixedSynthesis,WithLp.ofLp_toLp,
    P.slotted_physicalPacket hcard]
  simpa only [Fintype.sum_sigma] using P.sum_slotted hcard j
    (fun l u => c j l u k*P.physicalPacket t j l u k z)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCarrierFreeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive error envelope must not inherit the large carrier bound
of the wide reference cone. The exact raw norm is independent of it. -/

noncomputable section
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem absoluteConstant_pos (P : SourceLatticePacket N κ ι) : 0 < P.absoluteConstant := by
  have hR : 0 < P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  have hB := P.profileBound_pos
  unfold absoluteConstant
  positivity

theorem raw_absolute_lattice_envelope (P : SourceLatticePacket N κ ι)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j u).1) (P.length j) P.order x*
        lineEnvelope (P.width*(P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_absolute_envelope i j u k y x).trans
  have hB := P.profileBound_pos
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by positivity
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x) hA
  simpa only [absoluteConstant,mul_assoc] using h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted separated synthesis on an actual source top.
The product polynomial is used only as a stronger convenient weight;
its reciprocal has an integral proportional to the top area. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert

private theorem schwartz_colored_energy {I : Type*} [Fintype I] {q : ℕ}
    (f : I → SchwartzMap ℝ ℂ) (color : I → Fin q)
    (hdisjoint : ∀ ξ i j, i ≠ j → color i=color j → 𝓕 (f i) ξ=0 ∨ 𝓕 (f j) ξ=0) :
    (∫ x, ‖∑ i, f i x‖^2) ≤ (q:ℝ)*∑ i, ∫ x, ‖f i x‖^2 := by
  classical
  let selected := fun (r : Fin q) (i : I) => if color i=r then f i else (0 : SchwartzMap ℝ ℂ)
  let G := fun r : Fin q => (∑ i, selected r i : SchwartzMap ℝ ℂ)
  have hg (r : Fin q) : (∫ x, ‖G r x‖^2) =
      ∑ i, if color i=r then (∫ x, ‖f i x‖^2) else 0 := by
    have hd (ξ : ℝ) (i j : I) (hij : i≠j) :
        𝓕 (selected r i) ξ=0 ∨ 𝓕 (selected r j) ξ=0 := by
      by_cases hi : color i=r
      · by_cases hj : color j=r
        · simpa only [selected,ite_eq_left hi,ite_eq_left hj] using hdisjoint ξ i j hij (hi.trans hj.symm)
        · right; simp [selected,hj]
      · left; simp [selected,hi]
    have h := schwartz_energy_fourier_disjoint (selected r) hd
    have hleft (x : ℝ) : G r x = ∑ i, selected r i x := by simp [G]
    simp_rw [hleft]
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : color i=r <;> simp [selected,hi]
  have hpart (x : ℝ) : (∑ r, G r x) = ∑ i, f i x := by
    simp only [G,sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (color i)]
    · simp [selected]
    · intro r _ hr; simp [selected,Ne.symm hr]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have h := weighted_integral_sum_square volume (fun r x => G r x)
    (fun r => (G r).memLp 2) (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [hpart,div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one] at h
  rw [show (∑ r, ∫ x, ‖G r x‖^2) = ∑ i, ∫ x, ‖f i x‖^2 by
    simp_rw [hg]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp] at h
  exact h

private theorem schwartz_colored_vector_energy {I K : Type*} [Fintype I] [Fintype K] {q : ℕ}
    (f : I → K → SchwartzMap ℝ ℂ) (color : I → Fin q)
    (hdisjoint : ∀ k ξ i j, i≠j → color i=color j → 𝓕 (f i k) ξ=0 ∨ 𝓕 (f j k) ξ=0) :
    (∫ x, ‖WithLp.toLp 2 (fun k => ∑ i, f i k x)‖^2) ≤
      (q:ℝ)*∑ i, ∑ k, ∫ x, ‖f i k x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  have hi (k : K) : Integrable (fun x => ‖∑ i, f i k x‖^2) := by
    let F : SchwartzMap ℝ ℂ := ∑ i, f i k
    have he (x : ℝ) : F x = ∑ i, f i k x := by simp [F]
    simpa only [he] using (F.memLp 2).integrable_norm_pow (by decide : 2≠0)
  rw [integral_finsetSum _ (fun k _ => hi k)]
  calc
    _ ≤ ∑ k, (q:ℝ)*∑ i, ∫ x, ‖f i k x‖^2 :=
      Finset.sum_le_sum fun k _ => schwartz_colored_energy (fun i => f i k) color (hdisjoint k)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

/-- Polynomial multiplication preserves the separation used in the
finite colored synthesis estimate. -/
theorem polynomial_colored_packet_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)] {q : ℕ}
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (color : Fin N → Fin q) (lo hi : Fin N → ℝ)
    (hsep : ∀ i j, i≠j → color i=color j → hi i<lo j ∨ hi j<lo i)
    (hlow : ∀ j u k ξ, |ξ|<lo j → 𝓕 (f j u k) ξ=0)
    (hhigh : ∀ j u k ξ, hi j < |ξ| → 𝓕 (f j u k) ξ=0)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ×ℤ) (len : Fin N → ℝ)
    (a0 b0 a r W y C : ℝ) (hr : 0 < r) (hW : 0<W)
    (hlen : ∀ j, 0<len j) (hlenr : ∀ j, ∀ _ : ι j, len j ≤ r)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j u, X j u=a0+len j*(site j u).1)
    (hZ : ∀ j u, Z j u=b0+W*(site j u).2)
    (hcenter : ∀ j u, |X j u-a| ≤ r)
    (hf : ∀ j u k x, ‖f j u k x‖≤C*
      (lineEnvelope (X j u) (len j) 3 x*lineEnvelope (Z j u) W 3 y)) :
    (∫ x, ‖WithLp.toLp 2 (fun k => ∑ j,
      polynomialLocalization a r 1 (packetSynthesis (fun u => c j u k) (fun u => f j u k)) x)‖^2) ≤
      (q:ℝ)*((4*Real.pi)^2*C^2*16*Real.pi)*
        ∑ j, len j*∑ u, ‖c j u‖^2*lineEnvelope (Z j u) W 3 y := by
  let F := fun j k => packetSynthesis (fun u => c j u k) (fun u => f j u k)
  have hl (j k ξ) (hξ : |ξ|<lo j) : 𝓕 (F j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ _ (fun u => hlow j u k ξ hξ)
  have hh (j k ξ) (hξ : hi j < |ξ|) : 𝓕 (F j k) ξ=0 :=
    packetSynthesis_fourier_zero _ _ _ (fun u => hhigh j u k ξ hξ)
  have hp := schwartz_colored_vector_energy
    (fun j k => polynomialLocalization a r 1 (F j k)) color (by
      intro k ξ i j hij hcolor
      rcases hsep i j hij hcolor with hs | hs
      · by_cases hj : |ξ|<lo j
        · right; exact polynomialLocalization_low a r 1 (F j k) (lo j) (hi j) (hl j k) (hh j k) ξ hj
        · left; exact polynomialLocalization_high a r 1 (F i k) (lo i) (hi i) (hl i k) (hh i k) ξ
            (hs.trans_le (le_of_not_gt hj))
      · by_cases hi' : |ξ|<lo i
        · left; exact polynomialLocalization_low a r 1 (F i k) (lo i) (hi i) (hl i k) (hh i k) ξ hi'
        · right; exact polynomialLocalization_high a r 1 (F j k) (lo j) (hi j) (hl j k) (hh j k) ξ
            (hs.trans_le (le_of_not_gt hi')))
  exact hp.trans (by
    have h := mul_le_mul_of_nonneg_left
      (weighted_packet_energy c f X Z site len a0 b0 a r W y C hr hW hlen hlenr hinj hX hZ hcenter hf)
      (Nat.cast_nonneg q)
    simpa only [mul_assoc] using h)


private theorem integral_le_of_slice_majorant (f : ℝ×ℝ → ℝ) (H : ℝ → ℝ)
    (hfm : AEStronglyMeasurable f (volume.prod volume)) (hf0 : ∀ z, 0≤f z)
    (hH : Integrable H) (hi : ∀ y, Integrable (fun x => f (x,y)))
    (hb : ∀ y, (∫ x, f (x,y))≤H y) :
    Integrable f (volume.prod volume) ∧ (∫ z, f z ∂volume.prod volume)≤∫ y, H y := by
  have hint : Integrable (fun y => ∫ x, f (x,y)) :=
    hH.mono' hfm.prod_swap.integral_prod_right' (Filter.Eventually.of_forall fun y => by
      have hn : 0 ≤ ∫ x, f (x,y) := integral_nonneg fun x => hf0 (x,y)
      simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hb y)
  have hnorm : Integrable (fun y => ∫ x, ‖f (x,y)‖) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 _)] using hint
  have hfi : Integrable f (volume.prod volume) :=
    (integrable_prod_iff' hfm).2 ⟨Filter.Eventually.of_forall hi,hnorm⟩
  refine ⟨hfi,?_⟩
  rw [integral_prod_symm _ hfi]
  exact integral_mono hint hH hb

theorem treeProductPolynomial_pos (a b r W t : ℝ) (z : ℝ×ℝ) :
    0 < treeProductPolynomial a b r W t z :=
  mul_pos (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
    (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

/-- The original source packets have polynomially weighted separated
energy on every containing top. Constants precede the finite families. -/
theorem exists_weighted_physical_tree_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (t w a b r : ℝ), 0<w → 0 < r →
    ∀ c : ∀ j, ι j → EuclideanSpace ℂ κ,
      (∀ j (_u : ι j), P.length j ≤ r) →
      (∀ j u, |P.actualX j u-a| ≤ r) →
      (∀ j u, |P.actualZ j u-b|≤P.width) →
      (∀ j u k ξ η, planarAngularFourier (P.physicalPacket t j u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (_u : ι j), cb*w/P.length j≤|P.rowSlope j| ∧
        |P.rowSlope j|≤Cb*w/P.length j) →
      let E := fun z => (treeProductPolynomial a b r P.width t z)^2 *
        ‖∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z‖^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume) ≤ C*P.absoluteConstant^2 *
        ∑ j, ∑ u, ‖c j u‖^2*P.length j*P.width := by
  let lower := (cEta*cb-cStar)/(2*Real.pi)
  let upper := (CEta*Cb+cStar)/(2*Real.pi)
  have hlower : 0<lower := div_pos (sub_pos.mpr hgap) (by positivity)
  obtain ⟨q,hq,hsep⟩ := exists_dyadic_annular_separation (upper := upper) hlower
  refine ⟨(q:ℝ)*(4*Real.pi)^2*256*Real.pi^2,by positivity,?_⟩
  intro N κ ι _ _ P t w a b r hw hr c hlen hX hZ hspectrum hselector
  let G := fun y x => (WithLp.toLp 2 (fun k => ∑ j,
    polynomialLocalization a (2*r) 1
      (packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)) x) : EuclideanSpace ℂ κ)
  let F := fun z => ∑ j, planarFixedSynthesis (c j) (P.physicalPacket t j) z
  let E := fun z => (treeProductPolynomial a b r P.width t z)^2 * ‖F z‖^2
  let M := fun y => (q:ℝ)*(4*Real.pi)^2*P.absoluteConstant^2*256*Real.pi *
    ∑ j, P.length j*∑ u, ‖c j u‖^2*
      lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y
  have hPx (j) (u : ι j) : |P.length j*(P.snappedSite j u).1-a|≤2*r := by
    have he := snappedLatticeSite_horizontal (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) (P.length_pos j) (P.site j u)
    change |P.actualX j u-P.length j*(P.snappedSite j u).1|≤P.length j at he
    calc
      _ ≤ |P.length j*(P.snappedSite j u).1-P.actualX j u|+|P.actualX j u-a| :=
        abs_sub_le _ _ _
      _ ≤ P.length j+r := add_le_add (by simpa only [abs_sub_comm] using he) (hX j u)
      _ ≤ 2*r := by linarith [hlen j u]
  have hPy (j) (u : ι j) : |P.width*(P.snappedSite j u).2-b|≤2*P.width := by
    have he := snappedLatticeSite_vertical (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) P.width_pos (P.site j u)
    change |P.actualZ j u-P.width*(P.snappedSite j u).2|≤P.width at he
    calc
      _ ≤ |P.width*(P.snappedSite j u).2-P.actualZ j u|+|P.actualZ j u-b| := abs_sub_le _ _ _
      _ ≤ P.width+P.width := add_le_add (by simpa only [abs_sub_comm] using he) (hZ j u)
      _ = _ := by ring
  have hraw (j) (u : ι j) (k) (y x : ℝ) :
      P.physicalPacket t j u k (x,y+t*x) = P.raw 0 j u k y x := by
    have hh : P.raw 0 j u k y = planarSchwartzSlice
        (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale 0) y t :=
      P.raw_eq_physical_slice 0 j u k y t
    simpa only [planarCovariantJet,ite_true, if_true,planarSchwartzSlice_apply] using
      (congrArg (fun f : SchwartzMap ℝ ℂ => f x) hh).symm
  have hG (y x : ℝ) : G y x = (polynomialWeight a (2*r) 1 x : ℂ) • F (x,y+t*x) := by
    ext k
    simp only [G,F,planarFixedSynthesis,WithLp.ofLp_sum,Finset.sum_apply,
      polynomialLocalization_apply,packetSynthesis_apply,PiLp.smul_apply,smul_eq_mul,
      Finset.mul_sum,hraw]
  have hGy (y) : MemLp (G y) 2 volume := by
    apply memLp_piLp_iff.mpr
    intro k
    change MemLp (fun x => ∑ j, polynomialLocalization a (2*r) 1
      (packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y)) x) 2 volume
    exact memLp_finsetSum _ (fun j _ =>
      (polynomialLocalization a (2*r) 1
        (packetSynthesis (fun u => c j u k) (fun u => P.raw 0 j u k y))).memLp 2)
  have hEq (x y : ℝ) : E (x,y+t*x) =
      polynomialWeight b (2*P.width) 1 y ^2 * ‖G y x‖^2 := by
    rw [hG,norm_smul,Complex.norm_real,Real.norm_of_nonneg
      (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))]
    dsimp only [E,treeProductPolynomial]
    have hy : y+t*x-t*x=y := by ring
    rw [hy]
    ring
  have hline (y : ℝ) : (∫ x, ‖G y x‖^2) ≤
      (q:ℝ)*((4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi)*
        ∑ j, P.length j*∑ u, ‖c j u‖^2*
          lineEnvelope (P.width*(P.snappedSite j u).2) P.width 3 y := by
    refine polynomial_colored_packet_energy c (fun j u k => P.raw 0 j u k y)
      (fun j => ⟨j.val % q,Nat.mod_lt _ hq⟩)
      (fun j => (lower/P.topLength)*(2:ℝ)^j.val)
      (fun j => (upper/P.topLength)*(2:ℝ)^j.val) ?_ ?_ ?_
      (fun j u => P.length j*(P.snappedSite j u).1)
      (fun j u => P.width*(P.snappedSite j u).2) P.snappedSite P.length
      0 0 a (2*r) P.width y P.absoluteConstant (by positivity) P.width_pos P.length_pos
      ?_ P.snappedSite_injective (by intros; ring) (by intros; ring) hPx ?_
    · intro i j hij hmod
      have hm : i.val % q=j.val % q := congrArg Fin.val hmod
      rcases lt_or_gt_of_ne hij with hij | hji
      · left
        have hh := div_lt_div_of_pos_right (hsep i.val j.val hij hm) P.topLength_pos
        simpa only [div_mul_eq_mul_div] using hh
      · right
        have hh := div_lt_div_of_pos_right (hsep j.val i.val hji hm.symm) P.topLength_pos
        simpa only [div_mul_eq_mul_div] using hh
    · intro j u k ξ hξ
      exact (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).1 ξ hξ
    · intro j u k ξ hξ
      exact (P.raw_fourier_cutoffs_at t w cStar cEta CEta cb Cb hw hcEta hcb hCb
        j u k (hspectrum j u k) (hselector j u) 0 y).2 ξ hξ
    · intro j u; linarith [hlen j u]
    · intro j u k x
      apply (P.raw_absolute_lattice_envelope 0 j u k y x).trans
      apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
      exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
        (lineEnvelope_antitone _ _ _ P.order_ge_three) (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  have hslice (y : ℝ) : Integrable (fun x => E (x,y+t*x)) := by
    simp_rw [hEq]
    exact (hGy y).integrable_norm_pow (by decide : 2≠0) |>.const_mul _
  have hbound (y : ℝ) : (∫ x, E (x,y+t*x))≤M y := by
    simp_rw [hEq]
    rw [integral_const_mul]
    apply (mul_le_mul_of_nonneg_left (hline y) (sq_nonneg _)).trans
    dsimp only [M]
    have he (j) (u : ι j) := polynomialWeight_sq_mul_envelope y
      (P.width*(P.snappedSite j u).2) b P.width (2*P.width) 1 1 P.width_pos
      (mul_pos (by norm_num) P.width_pos) (by linarith [P.width_pos]) (hPy j u)
    simp only [Nat.reduceAdd,Nat.reduceMul,pow_one] at he
    calc
      _ = ((q:ℝ)*(4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi) *
          ∑ j, P.length j*∑ u, ‖c j u‖^2*
            (polynomialWeight b (2*P.width) 1 y ^2*
              lineEnvelope (P.width*(P.snappedSite j u).2) P.width 3 y) := by
        simp only [Finset.mul_sum]; ring_nf
      _ ≤ ((q:ℝ)*(4*Real.pi)^2*P.absoluteConstant^2*16*Real.pi) *
          ∑ j, P.length j*∑ u, ‖c j u‖^2*
            (16*lineEnvelope (P.width*(P.snappedSite j u).2) P.width 1 y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (P.length_pos j).le
        exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (he j u) (sq_nonneg _)
      _ = _ := by simp only [Finset.mul_sum]; ring_nf
  have hM : Integrable M := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun u _ =>
      (integrable_lineEnvelope_one (P.width*(P.snappedSite j u).2) P.width P.width_pos).const_mul _
  have hF : MemLp F 2 (volume.prod volume) := P.physicalMultiscaleSynthesis_memLp t c
  have hpoly : Continuous (treeProductPolynomial a b r P.width t) := by
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hEm : AEStronglyMeasurable E (volume.prod volume) :=
    (hpoly.aestronglyMeasurable.pow 2).mul (hF.aestronglyMeasurable.norm.pow 2)
  obtain ⟨hEi,hEbound⟩ := integral_le_of_slice_majorant
    (fun z => E (slopeShear t z)) M
    (hEm.comp_measurePreserving (slopeShear_measurePreserving t))
    (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hM hslice hbound
  have hE : Integrable E (volume.prod volume) :=
    ((slopeShear_measurePreserving t).integrable_comp hEm).1 hEi
  refine ⟨hE,?_⟩
  rw [integral_slopeShear] at hEbound
  apply hEbound.trans_eq
  dsimp only [M]
  rw [integral_const_mul,integral_finsetSum _ (fun j _ =>
    (integrable_finsetSum _ fun u _ =>
      (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _).const_mul _)]
  simp_rw [integral_const_mul,integral_finsetSum _ (fun u _ =>
    (integrable_lineEnvelope_one _ P.width P.width_pos).const_mul _),
    integral_const_mul,integral_lineEnvelope_one _ P.width P.width_pos]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  ring

end SourceLatticePacket

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

/-- Exact slot decomposition preserves the tree weight. The only label
loss is the stated bound on labels per scale. -/
theorem exists_weighted_labeled_tree_energy
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a b r : ℝ), 0<w → 0 < r →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j (l : P.labels j) (_u : Item j l), P.length j ≤ r) →
      (∀ j l u, |P.actualX j l u-a| ≤ r) →
      (∀ j l u, |P.actualZ j l u-b|≤P.width) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j) (_u : Item j l), cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => (treeProductPolynomial a b r P.width t z)^2 *
        ‖P.physicalLabeledSynthesis t c z‖^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume) ≤ (B:ℝ)*C*P.absoluteConstant^2 *
        ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,henergy⟩ := SourceLatticePacket.exists_weighted_physical_tree_energy
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr c hlen hX hZ hspectrum hselector
  let weight := treeProductPolynomial a b r P.width t
  let F := fun s : Fin B => fun z => ∑ j, planarFixedSynthesis
    (fun u : P.SlotItem hcard s j => c j u.1.1 u.1.2)
    ((P.slotted hcard s).physicalPacket t j) z
  let mass := fun s : Fin B => ∑ j, ∑ u : P.SlotItem hcard s j,
    ‖c j u.1.1 u.1.2‖^2*P.length j*P.width
  have hslot (s : Fin B) :
      Integrable (fun z => weight z^2*‖F s z‖^2) (volume.prod volume) ∧
      (∫ z, weight z^2*‖F s z‖^2 ∂volume.prod volume)≤C*P.absoluteConstant^2*mass s := by
    apply henergy N κ (P.SlotItem hcard s) (P.slotted hcard s) t w a b r hw hr
      (fun j u => c j u.1.1 u.1.2)
    · intro j u; exact hlen j u.1.1 u.1.2
    · intro j u
      simpa only [P.slotted_actualX hcard] using hX j u.1.1 u.1.2
    · intro j u
      change |(P.slotted hcard s).actualZ j u-b|≤P.width
      simpa only [P.slotted_actualZ hcard] using hZ j u.1.1 u.1.2
    · exact P.slotted_spectrum hcard t w cStar cEta CEta hspectrum s
    · intro j u
      simpa only [P.slotted_length hcard,P.slotted_rowSlope hcard s j u] using
        hselector j u.1.1 u.1.2
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hF (s : Fin B) : MemLp (fun z => weight z • F s z) 2 (volume.prod volume) := by
    apply (memLp_two_iff_integrable_sq_norm
      (hwc.aestronglyMeasurable.smul
        ((P.slotted hcard s).physicalMultiscaleSynthesis_memLp t _).aestronglyMeasurable)).2
    simpa only [Pi.smul_apply',norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using (hslot s).1
  have hsum (z : ℝ×ℝ) : (∑ s, weight z • F s z)=
      weight z • P.physicalLabeledSynthesis t c z := by
    rw [←Finset.smul_sum]
    exact congrArg (fun v : EuclideanSpace ℂ κ => weight z • v)
      (P.physicalLabeledSynthesis_eq_slots hcard t c z)
  have htotal : MemLp (fun z => weight z • P.physicalLabeledSynthesis t c z) 2
      (volume.prod volume) := by
    simpa only [hsum] using memLp_finsetSum Finset.univ (fun s _ => hF s)
  have hcost := weighted_integral_sum_square (volume.prod volume)
    (fun s z => weight z • F s z) hF (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_one,hsum,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hcost
  have hmass : (∑ s, mass s)=
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    dsimp only [mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_slotted hcard j (fun l u => ‖c j l u‖^2*P.length j*P.width)
  refine ⟨?_,hcost.trans ?_⟩
  · simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using
      htotal.integrable_norm_pow (by decide : 2≠0)
  · calc
      _ ≤ (B:ℝ)*∑ s, C*P.absoluteConstant^2*mass s :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => (hslot s).2) (Nat.cast_nonneg B)
      _ = _ := by rw [←Finset.mul_sum,hmass]; ring

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVectorPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial localization preserves the actual coordinate frequency
cutoffs of Hilbert-valued Schwartz packets. -/
noncomputable section
open FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

@[simp] theorem vectorPolynomialLocalization_apply (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorPolynomialLocalization a r q f x=(polynomialWeight a r q x:ℂ) • f x := by
  ext k
  simp only [vectorPolynomialLocalization,vectorSchwartz_apply,polynomialLocalization_apply,
    SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,PiLp.smul_apply,smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteRemovalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite iteration of proved removal steps, with exact telescoping
packet sums. The step is supplied by the density and size selections. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem iterate_finite_removal {ι V : Type*} [NormedAddCommGroup V]
    (v : ι → ℝ×ℝ → V) (E : Set (ℝ×ℝ)) (P : ℤ → Finset ι → Prop) (B : ℤ → ℝ)
    (step : ∀ k S, P k S → ∃ T, T⊆S ∧ P (k-1) T ∧
      IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume) ∧
      (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤B k)
    (n : ℕ) (k : ℤ) (S : Finset ι) (hS : P k S) :
    ∃ T, T⊆S ∧ P (k-(n:ℤ)) T ∧
      IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume) ∧
      (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤
        ∑ i∈Finset.range n, B (k-(i:ℤ)) := by
  induction n generalizing k S with
  | zero =>
    refine ⟨S,Finset.Subset.refl _,?_,?_,?_⟩
    · simpa only [Nat.cast_zero,sub_zero] using hS
    · simpa only [sub_self] using (integrableOn_zero :
        IntegrableOn (fun _ : ℝ×ℝ => (0:V)) E (volume.prod volume))
    · simp only [sub_self,norm_zero,integral_zero,Finset.range_zero,Finset.sum_empty,le_refl]
  | succ n ih =>
    obtain ⟨U,hUS,hU,hIU,hBU⟩ := step k S hS
    obtain ⟨T,hTU,hT,hIT,hBT⟩ := ih (k-1) U hU
    have heq (z : ℝ×ℝ) : finitePacketSum v S z-finitePacketSum v T z=
        (finitePacketSum v S z-finitePacketSum v U z)+
        (finitePacketSum v U z-finitePacketSum v T z) := by abel
    have hI : IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E
        (volume.prod volume) := (hIU.add hIT).congr (Filter.Eventually.of_forall fun z => (heq z).symm)
    refine ⟨T,hTU.trans hUS,?_,hI,?_⟩
    · convert hT using 1
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring
    · calc
        _ ≤ ∫ z in E, ‖finitePacketSum v S z-finitePacketSum v U z‖+
            ‖finitePacketSum v U z-finitePacketSum v T z‖ ∂volume.prod volume :=
          integral_mono hI.norm (hIU.norm.add hIT.norm) (fun z => by rw [heq]; exact norm_add_le _ _)
        _ = (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v U z‖ ∂volume.prod volume)+
            (∫ z in E, ‖finitePacketSum v U z-finitePacketSum v T z‖ ∂volume.prod volume) :=
          integral_add hIU.norm hIT.norm
        _ ≤ B k+∑ i∈Finset.range n, B ((k-1)-(i:ℤ)) := add_le_add hBU hBT
        _ = ∑ i∈Finset.range (n+1), B (k-(i:ℤ)) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero,sub_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          push_cast
          ring

theorem finite_removal_zero_remainder {ι V : Type*} [NormedAddCommGroup V]
    (v : ι → ℝ×ℝ → V) (E : Set (ℝ×ℝ)) (S T : Finset ι)
    (hI : IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume))
    (hzero : finitePacketSum v T=ᵐ[(volume.prod volume).restrict E] 0) (B : ℝ)
    (hB : (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤B) :
    IntegrableOn (finitePacketSum v S) E (volume.prod volume) ∧
      (∫ z in E, ‖finitePacketSum v S z‖ ∂volume.prod volume)≤B := by
  have heq : (fun z => finitePacketSum v S z-finitePacketSum v T z)
      =ᵐ[(volume.prod volume).restrict E] finitePacketSum v S := by
    filter_upwards [hzero] with z hz
    rw [hz,Pi.zero_apply,sub_zero]
  refine ⟨hI.congr heq,?_⟩
  have hn : (fun z => ‖finitePacketSum v S z-finitePacketSum v T z‖)
      =ᵐ[(volume.prod volume).restrict E] fun z => ‖finitePacketSum v S z‖ := by
    filter_upwards [heq] with z hz
    rw [hz]
  exact (integral_congr_ae hn).symm.le.trans hB

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntGeometricSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric bound used on the two sides of a dyadic crossover. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem int_geometric_summable {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    Summable (fun k : ℤ => r^k.natAbs) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  apply Summable.of_nat_of_neg
  · simpa only [Int.natAbs_natCast] using h
  · simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h

theorem int_geometric_tsum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1) :
    (∑' k : ℤ, r^k.natAbs)≤2/(1-r) := by
  have h := summable_geometric_of_abs_lt_one (r:=r) (by simpa only [abs_of_nonneg hr] using hr1)
  have hnat : Summable (fun n : ℕ => r^(n:ℤ).natAbs) := by simpa only [Int.natAbs_natCast] using h
  have hneg : Summable (fun n : ℕ => r^(-n:ℤ).natAbs) := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using h
  have heq : (∑' k : ℤ, r^k.natAbs)=(∑' n : ℕ, r^n)+(∑' n : ℕ, r^n)-1 := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_zero,pow_zero] using
      (hnat.tsum_of_nat_of_neg (f:=fun k : ℤ => r^k.natAbs) hneg)
  rw [heq,tsum_geometric_of_abs_lt_one (r:=r)
    (by simpa only [abs_of_nonneg hr] using hr1),div_eq_mul_inv]
  linarith

theorem int_geometric_shift_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r<1)
    (S : Finset ℤ) (a : ℤ) :
    (∑ k∈S, r^(k-a).natAbs)≤2/(1-r) := by
  classical
  have he : (∑ k∈S.image (fun k => k-a), r^k.natAbs)=∑ k∈S, r^(k-a).natAbs :=
    Finset.sum_image (g:=fun k : ℤ => k-a) (fun i _ j _ hij => by
      change i-a=j-a at hij
      omega)
  rw [←he]
  exact ((int_geometric_summable hr hr1).sum_le_tsum _ (fun k _ => pow_nonneg hr k.natAbs)).trans
    (int_geometric_tsum_le hr hr1)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSizeTest
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual unsigned size tests for unrestricted packet families. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem unsignedSizeTestEnergy_mono (w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    {R S : Finset P.PacketIndex} (hRS : R⊆S) (T : SlopeBox) :
    P.unsignedSizeTestEnergy w cb cell grid c R T≤P.unsignedSizeTestEnergy w cb cell grid c S T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hRS
  intro q _ _
  split_ifs
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos q.1).le) P.width_pos.le
  · exact le_rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_NormalizedBandSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized coordinates and support geometry in the packet
representation of the annular band multiplier (§2). -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

/-- The wave slopes stay in a fixed multiple of the angular scale
around the lattice label. -/
theorem frequency_slope_margin (l w xi eta theta c C : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0 < c) (hC : 0≤C)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C) :
    |(-xi/eta)-theta|≤(C/c)*(w/l) := by
  have heta : 0<eta := pos_of_mul_pos_right (hc.trans_le hV) hw.le
  have hscale : |(-xi/eta)-theta|=|symbolX l xi eta theta|/(l*eta) := by
    unfold symbolX
    rw [abs_mul, abs_of_pos hl]
    have hid : -xi/eta-theta=-(xi+theta*eta)/eta := by field_simp; ring
    rw [hid, abs_div, abs_neg, abs_of_pos heta]
    field_simp
  rw [hscale]
  apply (div_le_iff₀ (mul_pos hl heta)).2
  calc
    _ ≤ C := hX
    _ ≤ (C/c)*(w/l)*(l*eta) := by
      have hb : C≤(C/c)*(w*eta) := by
        calc
          C = (C/c)*c := by field_simp
          _ ≤ (C/c)*(w*eta) := mul_le_mul_of_nonneg_left hV (div_nonneg hC hc.le)
      convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-scale angular cells containing both the packet spectrum and
its selector support. The three nested grids are the existing literal
alternating one-third grids. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

theorem exists_scaled_three_grid_cover (unit : ℝ) (hu : 0<unit)
    (k : ℤ) (c r : ℝ) (hr : 0 ≤ r)
    (hsmall : 6*r<unit*DyadicLineGrid.scale k) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      Icc (c-r) (c+r) ⊆ scaledAngularCell unit grid k cell := by
  have hs : 6*(r/unit)<DyadicLineGrid.scale k := by
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hu).2
    simpa only [mul_comm] using hsmall
  obtain ⟨grid,hg,cell,hc⟩ := DyadicLineGrid.exists_three_grid_cover k
    (c/unit) (r/unit) (div_nonneg hr hu.le) hs
  refine ⟨grid,hg,cell,?_⟩
  intro x hx
  apply hc
  constructor
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.1
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem frequency_margin_subset {S : Set ℝ} (l w xi eta theta c C margin : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0 < c) (hC : 0≤C) (_hm : 0 ≤ margin)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C)
    (hcell : Icc (theta-(C/c+margin)*(w/l))
      (theta+(C/c+margin)*(w/l)) ⊆ S) :
    Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆ S := by
  have hs := abs_le.mp (frequency_slope_margin l w xi eta theta c C hl hw hc hC hV hX)
  intro s hs'
  apply hcell
  constructor <;> nlinarith only [hs.1,hs.2,hs'.1,hs'.2]

/-- A single selected angular cell contains the selector support and the
entire spectrum with the requested margin. -/
theorem exists_packet_angular_cell (unit : ℝ) (hu : 0<unit) (k : ℤ)
    (l w theta c C margin radius : ℝ) (hl : 0<l) (hw : 0<w)
    (hc : 0 < c) (hC : 0≤C) (hm : 0 ≤ margin) (hr : 0 ≤ radius)
    (hprecision : w/l=unit*DyadicLineGrid.scale k)
    (hsmall : 6*max radius (C/c+margin)<1) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      (∀ s, |s-theta| ≤ radius*(w/l) → s∈scaledAngularCell unit grid k cell) ∧
      (∀ xi eta, c≤w*eta → |symbolX l xi eta theta|≤C →
        Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆
          scaledAngularCell unit grid k cell) := by
  have hd : 0<w/l := div_pos hw hl
  let R := max radius (C/c+margin)
  have hR : 0≤R := hr.trans (le_max_left _ _)
  obtain ⟨grid,hg,cell,hcell⟩ := exists_scaled_three_grid_cover unit hu k theta
    (R*(w/l)) (mul_nonneg hR hd.le) (by
      rw [←hprecision]
      have h := mul_lt_mul_of_pos_right hsmall hd
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring)
  refine ⟨grid,hg,cell,?_,?_⟩
  · intro s hs
    apply hcell
    have hs' := abs_le.mp hs
    have hle := mul_le_mul_of_nonneg_right (le_max_left radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith
  · intro xi eta hV hX
    apply frequency_margin_subset l w xi eta theta c C margin hl hw hc hC hm hV hX
    intro s hs
    apply hcell
    have hle := mul_le_mul_of_nonneg_right (le_max_right radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith only [hs.1,hs.2,hle]

end LipschitzHilbert.PacketRepresentation

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularAssignment
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous choice of one of three angular grids for every
label. Its cells carry both the selector and the spectral margin. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem precision_eq_scaled_grid (w : ℝ) (j : Fin N) :
    w/P.length j = (w/P.topLength)*DyadicLineGrid.scale (j.val:ℤ) := by
  rw [length,DyadicLineGrid.scale,zpow_natCast]
  field_simp [P.topLength_pos.ne',pow_ne_zero _ (by norm_num : (2:ℝ)≠0)]

theorem exists_angular_assignment (w cStar cEta margin radius : ℝ)
    (hw : 0<w) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hm : 0 ≤ margin) (hr : 0 ≤ radius)
    (hsmall : 6*max radius (cStar/cEta+margin)<1) :
    ∃ grid : ∀ j, P.labels j → DyadicLineGrid.GridChoice,
    ∃ cell : ∀ j, P.labels j → ℤ,
      ∀ j (l : P.labels j),
        (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) := by
  classical
  have h (j : Fin N) (l : P.labels j) :
      ∃ g : DyadicLineGrid.GridChoice, ∃ cell : ℤ,
        (∀ s, |s-P.rowSlope j l| ≤ radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) g.val j.val cell) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta| ≤ cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) g.val j.val cell) := by
    obtain ⟨g,hg,cell,hsel,hspec⟩ := PacketRepresentation.exists_packet_angular_cell
      (w/P.topLength) (div_pos hw P.topLength_pos) j.val
      (P.length j) w (P.rowSlope j l) cEta cStar margin radius
      (P.length_pos j) hw hcEta hcStar hm hr (P.precision_eq_scaled_grid w j) hsmall
    refine ⟨⟨g,hg⟩,cell,hsel,?_⟩
    intro xi eta hV hX
    apply hspec xi eta hV
    rw [PacketRepresentation.symbolX,abs_mul,abs_of_pos (P.length_pos j)]
    have hh := (le_div_iff₀ (P.length_pos j)).mp hX
    simpa only [mul_comm] using hh
  choose grid cell hcell using h
  exact ⟨grid,cell,hcell⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem physical_multiplier_analyzing_integrable (t : ℝ) (m : ℝ×ℝ → ℂ)
    (hm : Measurable m) (hm1 : ∀ z, ‖m z‖ ≤ 1)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    Integrable (fun z => g z k*conj (m z*P.physicalPacket t j l u k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalPacket t j l u k).integrable.norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (hm.mul (P.physicalPacket t j l u k).continuous.measurable))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖g z k*conj (m z*P.physicalPacket t j l u k z)‖ ≤ ‖P.physicalPacket t j l u k z‖
  rw [norm_mul,Complex.norm_conj,norm_mul]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  calc
    _ ≤ 1*(1*‖P.physicalPacket t j l u k z‖) := mul_le_mul hgk
      (mul_le_mul_of_nonneg_right (hm1 z) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedReference
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected tree from an unrestricted packet lattice has a genuine
bounded reference lattice. Only the selected packets are present, and
their original physical waves are preserved. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex)

variable (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)

local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

theorem selectedReference_actualZ (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) :
    (Q).actualZ j l u=P.actualZ j (P.selectedOriginalLabel S j l) u.val-
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val := by
  dsimp [SourceLabeledLattice.actualZ,SourceLabeledLattice.actualX,actualX,actualZ,
    selectedReference,SourceLabeledLattice.length,length]
  ring

theorem selectedReference_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : P.SelectedItem S j l) (k : κ) :
    (Q).physicalPacket t j l u k=P.physicalPacket 0 j (P.selectedOriginalLabel S j l) u.val k := by
  have hx := P.selectedReference_actualX S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  have hz := P.selectedReference_actualZ S t Cb w F hw hCb hF hwide hfrequency hnear j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx,hz]
  change physicalPlanarPacket (P.profile j (P.selectedOriginalLabel S j l) u.val k)
    (P.actualX j (P.selectedOriginalLabel S j l) u.val)
    (P.actualZ j (P.selectedOriginalLabel S j l) u.val-
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val+
      t*P.actualX j (P.selectedOriginalLabel S j l) u.val)
    (P.length j) P.width (t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t))
    (P.frequency k) (P.length_pos j).ne' P.width_pos.ne' = _
  have hs : t+(P.rowSlope j (P.selectedOriginalLabel S j l)-t)=
      P.rowSlope j (P.selectedOriginalLabel S j l) := by ring
  rw [sub_add_cancel,hs]
  simp only [zero_mul,add_zero,zero_add]


theorem selectedReference_sum {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ r : (Q).PacketIndex,
      f (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear r).val) =
        ∑ q∈S, f q := by
  have h := Equiv.sum_comp
    (P.selectedReferenceEquiv S t Cb w F hw hCb hF hwide hfrequency hnear)
    (fun q : S => f q.val)
  exact h.trans (Finset.sum_subtype S (p := fun q => q∈S) (by simp) f).symm

theorem selectedReference_card (M R : ℕ) (hR : Cb≤R)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M) (j : Fin N) :
    ((Q).labels j).card≤(2*R+1)*M := by
  let W := SourceSlopeLabels.window Finset.univ (P.rowSlope j) t (w/P.length j) Cb
  let embed : P.selectedLabels S j ↪ W :=
    { toFun := fun l => ⟨P.selectedOriginalLabel S j l,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by
          simpa only [mul_div_assoc] using P.selectedLabel_near S t Cb w hnear j l⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : W => z.val.val) hab }
  have hcount : (P.selectedLabels S j).card≤W.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed embed.injective
  exact hcount.trans (SourceSlopeLabels.window_card_le Finset.univ (P.rowSlope j)
    (div_pos hw (P.length_pos j)) (hlocal j) hR)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem referenceEnvelopeConstant_pos :
    0<P.referenceEnvelopeConstant := by
  have hp := P.profileBound_pos
  have hr : 0<P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  unfold referenceEnvelopeConstant
  positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataTopReferenceGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A selected top supplies the exact reference-cone and center bounds
for the ordinary tree estimate. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem selected_top_cone (w : ℝ) (hw : 0<w)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (q : P.PacketIndex) (T : SlopeBox)
    (_hlen : P.length q.1≤T.length)
    (hrow : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (htop : T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    |P.rowSlope q.1 q.2.1-T.slope|≤w/P.length q.1 := by
  have hs := scaledAngularCell_slope (div_pos hw P.topLength_pos)
    (le_refl (q.1.val:ℤ)) ⟨P.rowSlope q.1 q.2.1,hrow,hrow⟩ hrow htop
  have heq : (w/P.topLength)*DyadicLineGrid.scale (q.1.val:ℤ) = w/P.length q.1 := by
    simp only [DyadicLineGrid.scale,zpow_natCast,PacketLatticeData.length]
    field_simp [P.topLength_pos.ne',ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) q.1.val)]
  rw [heq] at hs
  exact hs

theorem selected_top_centers (T : SlopeBox) (A : ℝ) (q : P.PacketIndex)
    (hwidth : T.width=P.width)
    (hcenter : (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T A) :
    |P.actualX q.1 q.2.1 q.2.2-T.x|≤A*T.length ∧
    |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
      (T.y-T.slope*T.x)|≤A*P.width := by
  change |P.actualX q.1 q.2.1 q.2.2-T.x|≤A*T.length ∧
    |(P.actualZ q.1 q.2.1 q.2.2-T.y)-T.slope*(P.actualX q.1 q.2.1 q.2.2-T.x)|≤A*T.width at hcenter
  refine ⟨hcenter.1,?_⟩
  rw [hwidth] at hcenter
  convert hcenter.2 using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStepArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the two ordinary removal budgets at the common size
threshold sigma² = eta times energy / area. -/
noncomputable section
namespace LipschitzHilbert

theorem normalized_size_identity (eta energyNorm area : ℝ) (harea : 0<area) (heta : 0≤eta) :
    (Real.sqrt eta*energyNorm/Real.sqrt area)^2*area=eta*energyNorm^2 := by
  rw [div_pow,mul_pow,Real.sq_sqrt heta,Real.sq_sqrt harea.le]
  field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceModelThresholdScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The size threshold used at each dyadic density level. -/
noncomputable section
namespace LipschitzHilbert

theorem modelSizeThreshold_pos {energyNorm area : ℝ}
    (hN : 0<energyNorm) (hA : 0<area) (k : ℤ) :
    0 < modelSizeThreshold energyNorm area k := by
  unfold modelSizeThreshold
  positivity

theorem modelSizeThreshold_identity (energyNorm area : ℝ) (hA : 0<area) (k : ℤ) :
    (modelSizeThreshold energyNorm area k)^2*area=(2:ℝ)^k*energyNorm^2 :=
  normalized_size_identity _ _ _ hA (zpow_pos (by norm_num) k).le

theorem modelSizeThreshold_successive (energyNorm area : ℝ) (hA : 0<area) (k : ℤ) :
    (modelSizeThreshold energyNorm area k)^2=
      (Real.sqrt 2*modelSizeThreshold energyNorm area (k-1))^2 := by
  apply (mul_right_cancel₀ hA.ne')
  rw [modelSizeThreshold_identity energyNorm area hA k,mul_pow,Real.sq_sqrt (by norm_num),mul_assoc,
    modelSizeThreshold_identity energyNorm area hA (k-1)]
  rw [zpow_sub₀ (by norm_num),zpow_one]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelConfig
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and selector data for the ordinary model. None of
these parameters depends on the input function or the tested set. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceTreeConstant_nonneg (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip : ℝ) (hLip : 0≤Lip) : 0≤P.referenceTreeConstant C B K Lip := by
  have ht := transverseTailConstant_nonneg
  have hp := P.profileBound_pos
  dsimp [referenceTreeConstant,referenceEnvelopeConstant]
  positivity

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem sizeAreaConstant_nonneg (d : OrdinaryModelConfig P initial) (CS : ℝ) :
    0≤d.sizeAreaConstant CS := by
  dsimp [sizeAreaConstant,selectedNearConstant]
  positivity

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelDegenerateCases
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero-energy input functions have zero literal analyzing coefficients. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem input_ae_zero_of_energy_zero {V : Type*} [NormedAddCommGroup V]
    (g : ℝ×ℝ → V) (hg : MemLp g 2 (volume.prod volume))
    (hzero : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0) :
    g=ᵐ[volume.prod volume] 0 := by
  have hsq : (fun z => ‖g z‖^2)=ᵐ[volume.prod volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖g z‖)
      (hg.integrable_norm_pow (by norm_num : (2:ℕ)≠0))).mp hzero
  filter_upwards [hsq] with z hz
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinaryCoefficient_zero_of_energy_zero (P : PacketLatticeData N κ Label Item)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume))
    (hzero : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0)
    (j : Fin N) (l : P.labels j) (a : Item j l) : P.ordinaryCoefficient g j l a=0 := by
  have h := input_ae_zero_of_energy_zero g hg hzero
  apply WithLp.ofLp_injective
  funext k
  have hi : (∫ z, g z k*conj (P.physicalPacket 0 j l a k z) ∂volume.prod volume)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h] with z hz
    simp only [hz,Pi.zero_apply,WithLp.ofLp_zero,zero_mul]
  simp only [ordinaryCoefficient,analyzingCoefficient,WithLp.ofLp_toLp,WithLp.ofLp_zero,
    Pi.zero_apply,hi,mul_zero]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataFiniteSizeBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite packet collection has a finite initial unsigned size.
This starts the threshold algorithm without an additional size premise. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem unsignedSizeTestEnergy_le_coefficient_sum (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (packets : Finset P.PacketIndex) (T : SlopeBox) (hwidth : T.width=P.width) :
    P.unsignedSizeTestEnergy w cb cell grid c packets T≤
      (∑ q∈packets, ‖c q.1 q.2.1 q.2.2‖^2)*T.area := by
  classical
  unfold unsignedSizeTestEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q _
  split_ifs with h
  · rw [SlopeBox.area,hwidth]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h.1 (sq_nonneg _)) P.width_pos.le
  · exact mul_nonneg (sq_nonneg _) T.area_pos.le

theorem exists_finite_unsigned_size_bound (w cb : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (packets : Finset P.PacketIndex) :
    ∃ sigma : ℝ, 0 ≤ sigma ∧ ∀ T : SlopeBox, T.width=P.width →
      P.unsignedSizeTestEnergy w cb cell grid c packets T ≤ sigma^2*T.area := by
  let B := ∑ q∈packets, ‖c q.1 q.2.1 q.2.2‖^2
  have hB : 0≤B := Finset.sum_nonneg (fun q _ => sq_nonneg _)
  refine ⟨Real.sqrt B,Real.sqrt_nonneg B,?_⟩
  intro T hT
  rw [Real.sq_sqrt hB]
  exact P.unsignedSizeTestEnergy_le_coefficient_sum w cb cell grid c packets T hT

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataZeroDensity
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A zero-density packet contributes zero on the tested set. This is
the exact finite-remainder assertion used by the threshold iteration. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem selector_zero_of_density_zero
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ) (q : P.PacketIndex)
    (hlen : P.length q.1≤tau)
    (hslope : P.rowSlope q.1 q.2.1∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (hdensity : P.ordinaryDensity 0 cell grid w tau E u q≤0)
    (selector : κ → ℝ → ℂ)
    (hsupport : ∀ k s, selector k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) (k : κ) :
    ∀ᵐ z ∂(volume.prod volume).restrict E, selector k (u z)=0 := by
  let test := P.ownDensityTest 0 cell grid w tau q hlen (by simpa only [zero_add] using hslope)
  let A := E ∩ u ⁻¹' scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)
  have hA : MeasurableSet A := hE.inter (hu (scaledAngularCell_measurable _ _ _ _))
  have havg : densityAverage test.top E u
      (scaledAngularCell (w/P.topLength) grid test.level test.cell)≤0 := by
    apply le_trans (le_csSup ((P.densityTile 0 cell q).densityValues_bddAbove
      P.topLength w P.width tau grid E u) (Or.inr ⟨test,rfl⟩)) hdensity
  have hzero : (∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume)=0 := by
    have hn : 0≤(∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume) :=
      integral_nonneg (fun z => test.top.densityKernel_nonneg 203 z)
    have hl : (∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume)≤0 := by
      have h := (div_le_iff₀ test.top.area_pos).mp havg
      simpa only [zero_mul,A,test,ownDensityTest] using h
    exact le_antisymm hl hn
  have hzeroAE : (test.top.densityKernel 203)=ᵐ[(volume.prod volume).restrict A] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => test.top.densityKernel_nonneg 203 z)
      (test.top.densityKernel_integrable (by norm_num)).integrableOn).mp hzero
  have hout : ∀ᵐ z ∂volume.prod volume, z∈A → test.top.densityKernel 203 z=0 :=
    (ae_restrict_iff' hA).mp hzeroAE
  filter_upwards [ae_restrict_of_ae hout,self_mem_ae_restrict hE] with z hz hzE
  by_contra hn
  have hmem : z∈A := ⟨hzE,hsupport k (u z) hn⟩
  have hp : 0<test.top.densityKernel 203 z := Real.rpow_pos_of_pos
    (by linarith [test.top.radius_nonnegative z]) _
  exact hp.ne' (hz hmem)

theorem packet_sum_zero_of_density_zero
    (packets : Finset P.PacketIndex) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (hlength : ∀ q∈packets, P.length q.1≤tau)
    (hrow : ∀ q∈packets, P.rowSlope q.1 q.2.1∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (hdensity : ∀ q∈packets, P.ordinaryDensity 0 cell grid w tau E u q≤0)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l)) :
    (fun z => ∑ q∈packets, WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
      selector q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z))
      =ᵐ[(volume.prod volume).restrict E] 0 := by
  have hq (q : packets) : ∀ᵐ z ∂(volume.prod volume).restrict E,
      ∀ k, selector q.val.1 q.val.2.1 k (u z)=0 :=
    ae_all_iff.mpr (fun k => P.selector_zero_of_density_zero cell grid w tau q.val
      (hlength q.val q.property) (hrow q.val q.property) E hE u hu
      (hdensity q.val q.property) (selector q.val.1 q.val.2.1) (hsupport _ _) k)
  filter_upwards [ae_all_iff.mpr hq] with z hz
  apply Finset.sum_eq_zero
  intro q hq
  apply WithLp.ofLp_injective
  funext k
  simp only [WithLp.ofLp_zero,Pi.zero_apply,hz ⟨q,hq⟩ k,mul_zero,zero_mul]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceFiniteThresholdLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite collection has a dyadic level below all its positive
densities, and a level above any prescribed initial size or density. -/
noncomputable section
namespace LipschitzHilbert

theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (d : ι → ℝ) :
    ∃ delta : ℝ, 0<delta ∧ ∀ q∈S, 0<d q → delta≤d q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨delta,hdelta,hlower⟩ := ih
    by_cases hd : 0<d a
    · refine ⟨min delta (d a),lt_min hdelta hd,?_⟩
      intro q hq hqpos
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hlower q hq hqpos)
    · refine ⟨delta,hdelta,?_⟩
      intro q hq hqpos
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (hd hqpos).elim
      · exact hlower q hq hqpos

theorem exists_dyadic_zero_detection {ι : Type*} (S : Finset ι) (d : ι → ℝ) :
    ∃ k : ℤ, ∀ q∈S, d q≤(2:ℝ)^k → d q≤0 := by
  obtain ⟨delta,hdelta,hlower⟩ := finite_positive_lower_bound S d
  obtain ⟨k,hk⟩ := exists_mem_Ioc_zpow hdelta (by norm_num : (1:ℝ)<2)
  refine ⟨k,?_⟩
  intro q hq hsmall
  by_contra hn
  have hpos : 0<d q := lt_of_not_ge hn
  exact (not_le_of_gt hk.1) (hsmall.trans' (hlower q hq hpos))

theorem exists_dyadic_upper_level (B : ℝ) : ∃ k : ℤ, B<(2:ℝ)^k := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1:ℝ)<2)
  exact ⟨n,by simpa only [zpow_natCast] using hn⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataModelCostPolynomial
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial dependence of the explicit model cost on the two packet
adaptation bounds. All remaining factors involve fixed geometric data. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceTreeConstant_le_unit (P : PacketLatticeData N κ Label Item)
    (C : ℝ) (B K : ℕ) (Lip bound : ℝ) (hLip : 0≤Lip)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    P.referenceTreeConstant C B K Lip≤ordinaryTreeUnitCost C B K Lip*bound := by
  have ht := transverseTailConstant_nonneg
  dsimp only [referenceTreeConstant,ordinaryTreeUnitCost]
  calc
    _ ≤ 27*288*(4*Real.pi)^2*(B:ℝ)*32*3^203*bound+
      Real.sqrt (C*(B:ℝ))*bound+
      32^106*(B:ℝ)*bound*(2+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4)*
        (32*2^203)*9*transverseTailConstant := by gcongr
    _ = _ := by ring

namespace OrdinaryModelConfig
variable {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem sizeAreaConstant_le_unit (d : OrdinaryModelConfig P initial) (CS bound : ℝ)
    (hCS : 0≤CS)
    (hprofile : P.profileBound≤bound) (habsolute : P.referenceEnvelopeConstant≤bound) :
    d.sizeAreaConstant CS≤d.unitSizeAreaCost CS*bound^2 := by
  have hp := P.profileBound_pos.le
  have ha := P.referenceEnvelopeConstant_pos.le
  let U := selectedFarUnitCost d.cb (Real.sqrt 2) CS d.packGap d.M d.Q
  have hU : 0≤U := by dsimp only [U,selectedFarUnitCost]; positivity
  have heFar : selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q=
      U*P.profileBound^2*P.referenceEnvelopeConstant^2 := by
    dsimp only [selectedFarConstant,U,selectedFarUnitCost]
    ring
  have hFar : 2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q≤(2*U)*(bound^2)^2 := by
    rw [heFar]
    calc
      _ ≤ 2*(U*bound^2*bound^2) := by gcongr
      _ = _ := by ring
  have hNear : selectedNearConstant P d.gap d.M d.Q ≤ selectedNearUnitCost d.gap d.M d.Q*bound^2 := by
    dsimp only [selectedNearConstant,selectedNearUnitCost]
    calc
      _ = (((2*d.gap+1:ℕ):ℝ)*(((2*d.Q+1)*d.M:ℕ):ℝ)*((4*Real.pi)^2*Real.pi^2))*P.profileBound^2 := by ring
      _ ≤ _ := by gcongr
  have hSqrt : Real.sqrt (2*selectedFarConstant P d.cb (Real.sqrt 2) CS d.packGap d.M d.Q)≤
      Real.sqrt (2*U)*bound^2 := by
    calc
      _ ≤ Real.sqrt ((2*U)*(bound^2)^2) := Real.sqrt_le_sqrt hFar
      _ = _ := by rw [Real.sqrt_mul (by positivity : 0≤2*U),Real.sqrt_sq (sq_nonneg bound)]
  calc
    _ ≤ 4*(selectedNearUnitCost d.gap d.M d.Q*bound^2+2*(Real.sqrt (2*U)*bound^2)) := by
      dsimp only [sizeAreaConstant]
      gcongr
    _ = _ := by dsimp only [unitSizeAreaCost,U]; ring

end OrdinaryModelConfig
end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundedTreeSize
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded test functions have uniformly bounded coefficient size on a
separated source tree. The proof uses the actual analyzing integrals,
polynomially weighted synthesis and an integrable reciprocal weight. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert

/-- Weighted synthesis duality needs only a bounded test function. -/
theorem analyzingCoefficient_bounded_energy_le
    {X I K : Type*} [MeasurableSpace X] [Fintype I] [Fintype K]
    (μ : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (weight : X → ℝ) (A V M : ℝ)
    (hA : 0≤A) (hV : 0≤V) (hM : 0≤M)
    (ha : ∀ i, 0<area i) (hw : ∀ x, 0<weight x)
    (hrec : MemLp (fun x => (weight x)⁻¹) 2 μ)
    (hinv : (∫ x, ((weight x)⁻¹)^2 ∂μ)≤V)
    (hg : ∀ x, ‖g x‖≤M)
    (hint : ∀ i k, Integrable (fun x => g x k * conj (wave i k x)) μ)
    (hsyn : ∀ c, MemLp (fun x => weight x • diagonalSynthesis wave c x) 2 μ)
    (hbound : ∀ c, (∫ x, ‖weight x • diagonalSynthesis wave c x‖^2 ∂μ) ≤
      A * ∑ i, area i * ‖c i‖^2) :
    (∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2) ≤ M^2*A*V := by
  let a := analyzingCoefficient μ area wave g
  let S := ∑ i, area i*‖a i‖^2
  let F := diagonalSynthesis wave a
  let H := fun x => weight x • F x
  have hS : 0≤S := Finset.sum_nonneg fun i _ => mul_nonneg (ha i).le (sq_nonneg _)
  have hH : MemLp H 2 μ := hsyn a
  have heq (x : X) : ‖H x‖*‖(weight x)⁻¹‖=‖F x‖ := by
    simp only [H,norm_smul,Real.norm_eq_abs,abs_of_pos (hw x),
      abs_of_pos (inv_pos.mpr (hw x))]
    field_simp [(hw x).ne']
  have hprod : Integrable (fun x => ‖H x‖*‖(weight x)⁻¹‖) μ :=
    hH.norm.integrable_mul hrec.norm
  have hFnorm : Integrable (fun x => ‖F x‖) μ := by
    simpa only [heq] using hprod
  have hp : (S : ℂ)=∫ x, inner ℂ (F x) (g x) ∂μ :=
    analyzingCoefficient_self_pairing μ area wave g (fun i => (ha i).ne') hint
  have hcs : S ≤ M*(Real.sqrt (∫ x, ‖H x‖^2 ∂μ)*
      Real.sqrt (∫ x, ((weight x)⁻¹)^2 ∂μ)) := by
    calc
      S = ‖∫ x, inner ℂ (F x) (g x) ∂μ‖ := by
        rw [←hp,Complex.norm_real,Real.norm_of_nonneg hS]
      _ ≤ ∫ x, ‖inner ℂ (F x) (g x)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, M*‖F x‖ ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hFnorm.const_mul M) (Filter.Eventually.of_forall fun x =>
            (norm_inner_le_norm (F x) (g x)).trans (by
              simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hg x) (norm_nonneg (F x))))
      _ = M*∫ x, ‖H x‖*‖(weight x)⁻¹‖ ∂μ := by rw [integral_const_mul]; simp only [heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        have hn (x : X) : ‖(weight x)⁻¹‖=(weight x)⁻¹ :=
          Real.norm_of_nonneg (inv_nonneg.mpr (hw x).le)
        simpa only [Real.rpow_two,←Real.sqrt_eq_rpow,hn] using
          integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
            (Filter.Eventually.of_forall fun x => norm_nonneg (H x))
            (Filter.Eventually.of_forall fun x => inv_nonneg.mpr (hw x).le)
            (by simpa using hH.norm) (by simpa using hrec)) hM
  have hE : 0≤∫ x, ‖H x‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hI : 0≤∫ x, ((weight x)⁻¹)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hsq := pow_le_pow_left₀ hS hcs 2
  rw [mul_pow,mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hI] at hsq
  have henergy : (∫ x, ‖H x‖^2 ∂μ)≤A*S := hbound a
  have hmul : M^2*((∫ x, ‖H x‖^2 ∂μ)*(∫ x, ((weight x)⁻¹)^2 ∂μ))≤M^2*(A*S*V) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
    exact mul_le_mul henergy hinv hI (mul_nonneg hA hS)
  change S≤M^2*A*V
  by_cases hz : S=0
  · rw [hz]; positivity
  · have hpos : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    apply le_of_mul_le_mul_left (a := S) _ hpos
    nlinarith [hsq,hmul]

/-- The reciprocal polynomial square is integrable with only the top
area as its scale. The slope shear has Jacobian one. -/
theorem treeProductPolynomial_reciprocal (a b r W t : ℝ) (hr : 0 < r) (hW : 0<W) :
    MemLp (fun z => (treeProductPolynomial a b r W t z)⁻¹) 2 (volume.prod volume) ∧
    (∫ z, ((treeProductPolynomial a b r W t z)⁻¹)^2 ∂volume.prod volume) ≤
      4*Real.pi^2*r*W := by
  let E := fun z : ℝ×ℝ => lineEnvelope a (2*r) 1 z.1 *
    lineEnvelope b (2*W) 1 (z.2-t*z.1)
  have hwc : Continuous (treeProductPolynomial a b r W t) := by
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hrc : Continuous (fun z => (treeProductPolynomial a b r W t z)⁻¹) :=
    hwc.inv₀ (fun z => (treeProductPolynomial_pos a b r W t z).ne')
  have he (z : ℝ×ℝ) : E z=(treeProductPolynomial a b r W t z)⁻¹ := by
    simp only [E,treeProductPolynomial,polynomialWeight,lineEnvelope,pow_one,
      ←div_pow,mul_inv_rev,mul_comm]
  have hEi : Integrable E (volume.prod volume) := by
    have hi := (integrable_lineEnvelope_one a (2*r) (by positivity)).mul_prod
      (integrable_lineEnvelope_one b (2*W) (by positivity))
    have hm : AEStronglyMeasurable E (volume.prod volume) := by
      have heq : E=(fun z => (treeProductPolynomial a b r W t z)⁻¹) := funext he
      rw [heq]
      exact hrc.aestronglyMeasurable
    apply ((slopeShear_measurePreserving t).integrable_comp hm).1
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    dsimp [E,slopeShear]
    congr 2; ring
  have hInt : (∫ z, E z ∂volume.prod volume)=4*Real.pi^2*r*W := by
    rw [←integral_slopeShear t E]
    have he (z : ℝ×ℝ) : E (slopeShear t z)=
        lineEnvelope a (2*r) 1 z.1*lineEnvelope b (2*W) 1 z.2 := by
      dsimp [E,slopeShear]; congr 2; ring
    simp_rw [he]
    rw [integral_prod_mul,integral_lineEnvelope_one a (2*r) (by positivity),
      integral_lineEnvelope_one b (2*W) (by positivity)]
    ring
  have hm : AEStronglyMeasurable (fun z => ((treeProductPolynomial a b r W t z)⁻¹)^2)
      (volume.prod volume) := by
    exact (hrc.pow 2).aestronglyMeasurable
  have hpoint (z : ℝ×ℝ) : ((treeProductPolynomial a b r W t z)⁻¹)^2≤E z := by
    have hx : 1≤polynomialWeight a (2*r) 1 z.1 := polynomialWeight_one_le _ _ _ _
    have hy : 1≤polynomialWeight b (2*W) 1 (z.2-t*z.1) := polynomialWeight_one_le _ _ _ _
    have hxy : 1≤treeProductPolynomial a b r W t z := by
      exact one_le_mul_of_one_le_of_one_le hx hy
    have hp : 0<(treeProductPolynomial a b r W t z)⁻¹ := inv_pos.mpr (treeProductPolynomial_pos _ _ _ _ _ _)
    have hi : (treeProductPolynomial a b r W t z)⁻¹≤1 := inv_le_one_of_one_le₀ hxy
    rw [he]
    nlinarith
  have hi : Integrable (fun z => ((treeProductPolynomial a b r W t z)⁻¹)^2)
      (volume.prod volume) := hEi.mono' hm (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((treeProductPolynomial a b r W t z)⁻¹))] using hpoint z)
  refine ⟨?_,(integral_mono hi hEi hpoint).trans_eq hInt⟩
  apply (memLp_two_iff_integrable_sq ?_).2 hi
  exact hrc.aestronglyMeasurable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

/-- A bounded test has bounded size on a separated physical source tree.
The constant is independent of the finite scale, packet and vector types. -/
theorem exists_physical_bounded_tree_size
    (cStar cEta CEta cb Cb : ℝ) (hcEta : 0 < cEta)
    (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a b r : ℝ), 0<w → 0 < r →
    ∀ (beta : P.PacketIndex → κ → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (M : ℝ),
      0≤M → (∀ q k, ‖beta q k‖≤1) → Measurable g → (∀ z, ‖g z‖≤M) →
      (∀ j (l : P.labels j) (_u : Item j l), P.length j ≤ r) →
      (∀ j l u, |P.actualX j l u-a| ≤ r) →
      (∀ j l u, |P.actualZ j l u-b|≤P.width) →
      (∀ j l u k ξ η, planarAngularFourier (P.physicalPacket t j l u k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j) (_u : Item j l), cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      (∑ q : P.PacketIndex, P.length q.1*P.width*‖P.physicalFrozenCoefficient t beta g q‖^2) ≤
        (B:ℝ)*C*P.absoluteConstant^2*M^2*(r*P.width) := by
  obtain ⟨C,hC,henergy⟩ := exists_weighted_labeled_tree_energy
    cStar cEta CEta cb Cb hcEta hcb hCb hgap
  refine ⟨C*(4*Real.pi^2),by positivity,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr beta g M hM hbeta hg hgM
    hlen hX hZ hspectrum hselector
  let weight := treeProductPolynomial a b r P.width t
  let wave := fun q : P.PacketIndex => fun k z =>
    beta q k * P.physicalPacket t q.1 q.2.1 q.2.2 k z
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let d := fun c : P.PacketIndex → EuclideanSpace ℂ κ =>
    fun j (l : P.labels j) (u : Item j l) =>
      WithLp.toLp 2 (fun k => c ⟨j,⟨l,u⟩⟩ k * beta ⟨j,⟨l,u⟩⟩ k)
  have hdiag (c : P.PacketIndex → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
      diagonalSynthesis wave c z=P.physicalLabeledSynthesis t (d c) z := by
    ext k
    simp only [diagonalSynthesis,physicalLabeledSynthesis,planarFixedSynthesis,wave,d,
      WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp,Fintype.sum_sigma,mul_assoc]
  have hweighted (c : P.PacketIndex → EuclideanSpace ℂ κ) :
      Integrable (fun z => weight z^2*‖diagonalSynthesis wave c z‖^2) (volume.prod volume) ∧
      (∫ z, weight z^2*‖diagonalSynthesis wave c z‖^2 ∂volume.prod volume) ≤
        ((B:ℝ)*C*P.absoluteConstant^2)*∑ q, area q*‖c q‖^2 := by
    have h := henergy N κ Label Item P B hcard t w a b r hw hr (d c)
      hlen hX hZ hspectrum hselector
    simp_rw [←hdiag] at h
    refine ⟨h.1,h.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hn (j) (l : P.labels j) (u : Item j l) : ‖d c j l u‖≤‖c ⟨j,⟨l,u⟩⟩‖ := by
      simpa only [d,one_mul] using diagonal_packet_norm (c ⟨j,⟨l,u⟩⟩) (beta ⟨j,⟨l,u⟩⟩)
        (show (0:ℝ)≤1 by norm_num) (hbeta ⟨j,⟨l,u⟩⟩)
    simp only [Fintype.sum_sigma,area]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro u _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn j l u) 2
    convert mul_le_mul_of_nonneg_right hsq
      (mul_nonneg (P.length_pos j).le P.width_pos.le) using 1 <;> ring
  have hwc : Continuous weight := by
    dsimp only [weight]
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hsyn (c : P.PacketIndex → EuclideanSpace ℂ κ) :
      MemLp (fun z => weight z • diagonalSynthesis wave c z) 2 (volume.prod volume) := by
    have hdm : AEStronglyMeasurable (diagonalSynthesis wave c) (volume.prod volume) := by
      have he : diagonalSynthesis wave c=P.physicalLabeledSynthesis t (d c) := funext (hdiag c)
      rw [he]
      exact (P.physicalLabeledSynthesis_memLp t _).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm (hwc.aestronglyMeasurable.smul hdm)).2
    simpa only [Pi.smul_apply',norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using (hweighted c).1
  have hint (q : P.PacketIndex) (k : κ) :
      Integrable (fun z => g z k*conj (wave q k z)) (volume.prod volume) := by
    have hgm : Measurable (fun z => g z k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    have hwm : Measurable (wave q k) :=
      measurable_const.mul (P.physicalPacket t q.1 q.2.1 q.2.2 k).continuous.measurable
    have hwi : Integrable (wave q k) (volume.prod volume) :=
      (P.physicalPacket t q.1 q.2.1 q.2.2 k).integrable.const_mul _
    apply (hwi.norm.const_mul M).mono' (hgm.mul (continuous_star.measurable.comp hwm)).aestronglyMeasurable
    filter_upwards [] with z
    change ‖g z k*conj (wave q k z)‖≤M*‖wave q k z‖
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (g z) k).trans (hgM z)) (norm_nonneg _)
  obtain ⟨hrec,hinv⟩ := treeProductPolynomial_reciprocal a b r P.width t hr P.width_pos
  have h := analyzingCoefficient_bounded_energy_le (volume.prod volume) area wave g weight
    ((B:ℝ)*C*P.absoluteConstant^2) (4*Real.pi^2*r*P.width) M (by positivity)
    (mul_nonneg (mul_nonneg (by positivity) hr.le) P.width_pos.le) hM
    (fun q => mul_pos (P.length_pos q.1) P.width_pos)
    (treeProductPolynomial_pos a b r P.width t) hrec hinv hgM hint hsyn
    (fun c => by
      simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] using (hweighted c).2)
  change (∑ q, area q*‖analyzingCoefficient (volume.prod volume) area wave g q‖^2)≤_
  convert h using 1 <;> first | rfl | ring

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataRecenteredBoundedSize
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded inputs control the original analyzing coefficients in an
arbitrary reference tree, using only the occupied angular rows. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_recentered_bounded_size (cStar cEta CEta cb : ℝ)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M : ℕ) (Q : Finset P.PacketIndex)
      (t a b r w F G : ℝ), 0 < r → 0<w → w≤P.width → 0≤F → 0≤G →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
      (∀ q∈Q, P.length q.1 ≤ r) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a| ≤ r) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width) →
      (∀ q∈Q, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| ∧
        |P.rowSlope q.1 q.2.1-t|≤w/P.length q.1) →
      (∀ q∈Q, ∀ k xi eta, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0 →
        |xi+P.rowSlope q.1 q.2.1*eta| ≤ cStar/P.length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta) →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤G) →
      (∑ q∈Q, P.length q.1*P.width*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2)≤
        ((3*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2*G^2*(r*P.width) := by
  obtain ⟨C,hC,hBound⟩ := SourceLabeledLattice.exists_physical_bounded_tree_size cStar cEta CEta cb 1
    hcEta hcb (by norm_num) hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q t a b r w F G hr hw hW hF hG hfreq hlocal hlen hX hZ hcone hspectrum g hg hgG
  have hnear : ∀ q ∈ Q, |P.rowSlope q.1 q.2.1-t| ≤ 1*w/P.length q.1 := by
    intro q hq
    simpa only [one_mul] using (hcone q hq).2
  have hwide : 1*w ≤ P.width := by simpa only [one_mul] using hW
  let T := P.selectedReference Q t 1 w F hw zero_le_one hF hwide hfreq hnear
  have hcard (j : Fin N) : (T.labels j).card ≤ 3*M := by
    simpa only [show (2*1+1:ℕ)=3 by norm_num] using
      P.selectedReference_card Q t 1 w F hw zero_le_one hF hwide hfreq hnear M 1
        (by norm_num) hlocal j
  have hpacket (j : Fin N) (l : T.labels j) (v : P.SelectedItem Q j l) (k : κ) :
      (T.physicalPacket t j l v k : ℝ×ℝ → ℂ)=
        P.physicalPacket 0 j (P.selectedOriginalLabel Q j l) v.val k := by
    funext z
    exact congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
      (P.selectedReference_physicalPacket Q t 1 w F hw zero_le_one hF hwide hfreq hnear j l v k)
  have h := hBound N κ Label (P.SelectedItem Q) T (3*M) hcard t w a b r hw hr
    (fun _ _ => 1) g G hG (by intro q k; simp) hg hgG
    (fun j l v => hlen ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v))
    (fun j l v => hX ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v))
    (by
      intro j l v
      have he := P.selectedReference_actualZ Q t 1 w F hw zero_le_one hF hwide hfreq hnear j l v
      have ha := congrArg (fun x : ℝ => |x-b|) he
      exact ha.le.trans (hZ ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v)))
    (by
      intro j l v k xi eta hn
      rw [hpacket] at hn
      have hp := hspectrum ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩
        (P.selectedItem_mem Q j l v) k xi eta hn
      change |xi+(t+(P.rowSlope j (P.selectedOriginalLabel Q j l)-t))*eta| ≤ cStar/P.length j ∧
        cEta≤w*eta ∧ w*eta≤CEta
      simpa only [add_sub_cancel] using hp)
    (by
      intro j l v
      have hp := hcone ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v)
      change cb*w/P.length j≤|P.rowSlope j (P.selectedOriginalLabel Q j l)-t| ∧
        |P.rowSlope j (P.selectedOriginalLabel Q j l)-t|≤1*w/P.length j
      simpa only [one_mul] using hp)
  have hc (q : T.PacketIndex) : T.physicalFrozenCoefficient t (fun _ _ => 1) g q=
      P.ordinaryCoefficient g q.1 (P.selectedOriginalLabel Q q.1 q.2.1) q.2.2.val := by
    apply WithLp.ofLp_injective
    funext k
    simp only [SourceLabeledLattice.physicalFrozenCoefficient,ordinaryCoefficient,analyzingCoefficient,
      WithLp.ofLp_toLp,one_mul,hpacket]
    rfl
  simp_rw [hc] at h
  have hs := P.selectedReference_sum Q t 1 w F hw zero_le_one hF hwide hfreq hnear (fun q =>
    P.length q.1*P.width*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2)
  exact hs.symm.le.trans h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformBoundedSize
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-input constant is chosen before the packet lattice, its
translation, and its finite collection. Its remaining dependence is explicit. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_uniform_bounded_unsigned_size (cStar cEta CEta cb : ℝ)
    (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ) (G : ℝ),
      0≤G → Measurable g → (∀ z, ‖g z‖≤G) →
    ∀ T : SlopeBox, T.width=P.width → T.length≤d.tau →
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) initial T≤
        (1+((3*d.M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2)*G^2*T.area := by
  obtain ⟨C,hC,hBound⟩ := exists_recentered_bounded_size cStar cEta CEta cb hcEta hcb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄
  rw [←heq₁,←heq₂,←heq₃,←heq₄] at hBound
  let B := ((3*d.M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2
  have hB : 0≤B := by dsimp only [B]; positivity
  intro g G hG hg hgG T hwidth htime
  let Q := initial.filter fun q => P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1) ∧
    d.cb*d.w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1|
  have hmem (q : P.PacketIndex) (hq : q∈Q) := Finset.mem_filter.mp hq
  have hX (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualX q.1 q.2.1 q.2.2-T.x|≤T.length := by
    have h := (P.selected_top_centers T (1/2) q hwidth (hmem q hq).2.2.1).1
    nlinarith [T.length_pos]
  have hZ (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|≤P.width := by
    have h := (P.selected_top_centers T (1/2) q hwidth (hmem q hq).2.2.1).2
    nlinarith [P.width_pos]
  have hcone (q : P.PacketIndex) (hq : q∈Q) :
      d.cb*d.w/P.length q.1≤|P.rowSlope q.1 q.2.1-T.slope| ∧
      |P.rowSlope q.1 q.2.1-T.slope|≤d.w/P.length q.1 := by
    refine ⟨?_,P.selected_top_cone d.w d.hw d.cell d.grid q T (hmem q hq).2.1
      (d.hrow q (hmem q hq).1) (hmem q hq).2.2.2.1⟩
    simpa only [abs_sub_comm] using (hmem q hq).2.2.2.2
  have h := hBound N κ Label Item P d.M Q T.slope T.x (T.y-T.slope*T.x) T.length d.w d.F G
    T.length_pos d.hw d.hW d.hF hG d.hfreq d.hlocal (fun q hq => (hmem q hq).2.1)
    hX hZ hcone (fun q _ k xi eta hn => d.spectrum q.1 q.2.1 q.2.2 k xi eta hn) g hg hgG
  have he : P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) initial T=
      ∑ q∈Q, P.length q.1*P.width*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2 := by
    dsimp only [Q,unsignedSizeTestEnergy]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ B*G^2*T.area := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [B,SlopeBox.area]
      rw [hwidth]
    _ ≤ (1+B)*G^2*T.area := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : B≤1+B) (sq_nonneg G)) T.area_pos.le

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical weights for the bounded-input, unequal-measure estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem reverseThresholdRatio_pos : 0 < reverseThresholdRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem reverseThresholdRatio_lt_one : reverseThresholdRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem reverse_density_factor {eta : ℝ} (heta : 0<eta) :
    min 1 eta*(1+eta^(-(1/20:ℝ)))/eta≤2*eta^(-(1/20:ℝ)) := by
  by_cases h : eta≤1
  · rw [min_eq_right h,mul_div_cancel_left₀ _ heta.ne']
    have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos heta h (by norm_num : -(1/20:ℝ)≤0)
    linarith
  · have h1 : 1≤eta := le_of_not_ge h
    rw [min_eq_left h1,one_mul]
    calc
      _ ≤ 2/eta := div_le_div_of_nonneg_right
        (by linarith [Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : -(1/20:ℝ)≤0)]) heta.le
      _ = 2*eta^(-(1:ℝ)) := by rw [Real.rpow_neg_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : -(1:ℝ)≤ -(1/20:ℝ))) (by norm_num)

theorem reverseThresholdWeight_le_shape {ratio eta : ℝ} (heta : 0<eta) :
    reverseThresholdWeight ratio eta≤
      2*(min 1 (Real.sqrt (eta/ratio))*eta^(-(1/20:ℝ))) := by
  have h := mul_le_mul_of_nonneg_left (reverse_density_factor heta)
    (le_min zero_le_one (Real.sqrt_nonneg (eta/ratio)))
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try unfold reverseThresholdWeight) <;> ring)

theorem reverse_shape_small {x : ℝ} (hx : 0<x) (hsmall : x≤1) :
    min 1 (Real.sqrt x)*x^(-(1/20:ℝ))≤x^(1/20:ℝ) := by
  calc
    _ ≤ Real.sqrt x*x^(-(1/20:ℝ)) := mul_le_mul_of_nonneg_right
      (min_le_right _ _) (Real.rpow_nonneg hx.le _)
    _ = x^(9/20:ℝ) := by
      rw [Real.sqrt_eq_rpow,←Real.rpow_add hx]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hx hsmall (by norm_num)

theorem reverse_shape_dyadic (k : ℤ) :
    min 1 (Real.sqrt ((2:ℝ)^k))*((2:ℝ)^k)^(-(1/20:ℝ)) ≤ reverseThresholdRatio^k.natAbs := by
  cases k with
  | ofNat n =>
    have h : min 1 (Real.sqrt ((2:ℝ)^n))*((2:ℝ)^n)^(-(1/20:ℝ))≤
        ((2:ℝ)^n)^(-(1/20:ℝ)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (min_le_left 1 (Real.sqrt ((2:ℝ)^n))) (Real.rpow_nonneg (by positivity) (-(1/20:ℝ)))
    change min 1 (Real.sqrt ((2:ℝ)^n))*((2:ℝ)^n)^(-(1/20:ℝ)) ≤ reverseThresholdRatio^n
    exact h.trans_eq (Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2) _ _).symm
  | negSucc n =>
    have he : (2:ℝ)^Int.negSucc n=((2:ℝ)^(n+1))⁻¹ := zpow_negSucc _ _
    have hsmall : (2:ℝ)^Int.negSucc n≤1 := by
      rw [he]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h := reverse_shape_small (zpow_pos (by norm_num : (0:ℝ)<2) _) hsmall
    have hp : ((2:ℝ)^Int.negSucc n)^(1/20:ℝ)=reverseThresholdRatio^(n+1) := by
      rw [he,←Real.rpow_neg_eq_inv_rpow,←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
      rfl
    simpa only [hp,Int.natAbs_negSucc] using h

theorem reverse_scale_power_le {ratio scale : ℝ} (hr : 0 < ratio) (hs : 0 < scale)
    (hupper : ratio≤2*scale) :
    scale^(-(1/20:ℝ))≤2*ratio^(-(1/20:ℝ)) := by
  have hp : (2*scale)^(-(1/20:ℝ)) ≤ ratio^(-(1/20:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr hupper (by norm_num)
  have htwo : (2:ℝ)^(1/20:ℝ)≤2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤2) (by norm_num : (1/20:ℝ)≤1)
  have heq : scale^(-(1/20:ℝ))=(2:ℝ)^(1/20:ℝ)*(2*scale)^(-(1/20:ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hs.le,Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    rw [←mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos (by norm_num) (1/20:ℝ)).ne',one_mul]
  calc
    _ = _ := heq
    _ ≤ (2:ℝ)^(1/20:ℝ)*ratio^(-(1/20:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hr.le _)

theorem reverseThresholdWeight_scale {ratio scale x : ℝ}
    (hr : 0 < ratio) (hs : 0 < scale) (hx : 0<x)
    (hlo : scale ≤ ratio) (hhi : ratio≤2*scale) :
    reverseThresholdWeight ratio (scale*x)≤
      4*ratio^(-(1/20:ℝ))*(min 1 (Real.sqrt x)*x^(-(1/20:ℝ))) := by
  have heta : 0 < scale*x := mul_pos hs hx
  have hdiv : scale*x/ratio≤x := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hm : min 1 (Real.sqrt (scale*x/ratio)) ≤ min 1 (Real.sqrt x) :=
    min_le_min_left 1 (Real.sqrt_le_sqrt hdiv)
  have hpow : (scale*x)^(-(1/20:ℝ))≤2*ratio^(-(1/20:ℝ))*x^(-(1/20:ℝ)) := by
    rw [Real.mul_rpow hs.le hx.le]
    exact mul_le_mul_of_nonneg_right (reverse_scale_power_le hr hs hhi) (Real.rpow_nonneg hx.le _)
  calc
    _ ≤ 2*(min 1 (Real.sqrt (scale*x/ratio))*(scale*x)^(-(1/20:ℝ))) :=
      reverseThresholdWeight_le_shape heta
    _ ≤ 2*(min 1 (Real.sqrt x)*(2*ratio^(-(1/20:ℝ))*x^(-(1/20:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul hm hpow (Real.rpow_nonneg heta.le _) (le_min zero_le_one (Real.sqrt_nonneg x))
    _ = _ := by ring

theorem reverseThreshold_dyadic_majorant {ratio : ℝ} (hr : 0 < ratio) :
    ∃ a : ℤ, ∀ k : ℤ, reverseThresholdWeight ratio ((2:ℝ)^k)≤
      4*ratio^(-(1/20:ℝ))*reverseThresholdRatio^(k-a).natAbs := by
  obtain ⟨a,ha⟩ := exists_mem_Ico_zpow hr (by norm_num : (1:ℝ)<2)
  have hs : (0:ℝ)<2^a := zpow_pos (by norm_num) a
  have hupper : ratio≤2*(2:ℝ)^a := by
    have h := ha.2.le
    rw [zpow_add₀ (by norm_num),zpow_one] at h
    nlinarith
  refine ⟨a,?_⟩
  intro k
  have hsplit : (2:ℝ)^k=(2:ℝ)^a*(2:ℝ)^(k-a) := by
    rw [←zpow_add₀ (by norm_num)]
    congr 1
    omega
  rw [hsplit]
  exact (reverseThresholdWeight_scale hr hs (zpow_pos (by norm_num) (k-a)) ha.1 hupper).trans
    (mul_le_mul_of_nonneg_left (reverse_shape_dyadic (k-a)) (by positivity))

theorem reverseThreshold_finite_sum {ratio : ℝ} (hr : 0 < ratio) (S : Finset ℤ) :
    (∑ k∈S, reverseThresholdWeight ratio ((2:ℝ)^k))≤
      (8/(1-reverseThresholdRatio))*ratio^(-(1/20:ℝ)) := by
  obtain ⟨a,ha⟩ := reverseThreshold_dyadic_majorant hr
  calc
    _ ≤ ∑ k∈S, (4*ratio^(-(1/20:ℝ)))*reverseThresholdRatio^(k-a).natAbs :=
      Finset.sum_le_sum (fun k _ => ha k)
    _ = (4*ratio^(-(1/20:ℝ)))*∑ k∈S, reverseThresholdRatio^(k-a).natAbs := by rw [Finset.mul_sum]
    _ ≤ (4*ratio^(-(1/20:ℝ)))*(2/(1-reverseThresholdRatio)) :=
      mul_le_mul_of_nonneg_left (int_geometric_shift_sum_le reverseThresholdRatio_pos.le
        reverseThresholdRatio_lt_one S a) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCappedStepArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize removal budgets while keeping the independent size cap. -/
noncomputable section
namespace LipschitzHilbert

theorem combine_capped_removal_budgets
    (A B Q cap sigma density eta area energy : ℝ)
    (hB : 0≤B) (hQ : 0≤Q) (hcap : 0 ≤ cap) (hsigma : 0 < sigma)
    (hdensity : 0≤density) (heta : 0<eta) (harea : 0≤area)
    (hscale : sigma^2*area=eta*energy) :
    A*cap*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
      B*cap*density*((Q/sigma^2)*energy) ≤
    (2*A+B*Q)*cap*density*(1+eta^(-(1/20:ℝ)))*area/eta := by
  have hratio : (Q/sigma^2)*energy=Q*area/eta := by
    field_simp
    nlinarith [congrArg (fun x : ℝ => Q*x) hscale]
  rw [hratio]
  have hfac : 1≤1+eta^(-(1/20:ℝ)) := le_add_of_nonneg_right (Real.rpow_nonneg heta.le _)
  have hb : 0≤B*cap*density*(Q*area/eta) := by positivity
  calc
    _ ≤ A*cap*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
        (B*cap*density*(Q*area/eta))*(1+eta^(-(1/20:ℝ))) :=
      add_le_add le_rfl (le_mul_of_one_le_right hb hfac)
    _ = _ := by ring

theorem min_scaled_le (a b x : ℝ) (hx : 0≤x) :
    min a (b*x) ≤ max a b*min 1 x := by
  by_cases h : x≤1
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (le_max_left _ _)

theorem capped_density_weight_le (cap density eta ratio K U : ℝ)
    (heta : 0<eta) (hK : 0≤K) (hdensity : 0≤density)
    (hcapBound : cap≤K*min 1 (Real.sqrt (eta/ratio)))
    (hdensityBound : density≤U*min 1 eta) :
    cap*density*(1+eta^(-(1/20:ℝ)))/eta≤K*U*reverseThresholdWeight ratio eta := by
  have hmult := mul_le_mul hcapBound hdensityBound hdensity
    (mul_nonneg hK (le_min zero_le_one (Real.sqrt_nonneg _)))
  have h := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmult (by positivity : 0≤1+eta^(-(1/20:ℝ)))) heta.le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold reverseThresholdWeight
  ring

theorem modelSizeThreshold_eq_sqrt_ratio {energyNorm area : ℝ}
    (hN : 0<energyNorm) (hA : 0<area) (k : ℤ) :
    modelSizeThreshold energyNorm area k=Real.sqrt ((2:ℝ)^k/(area/energyNorm^2)) := by
  have hleft := modelSizeThreshold_pos hN hA k
  have heta := zpow_pos (by norm_num : (0:ℝ)<2) k
  have hid := modelSizeThreshold_identity energyNorm area hA k
  apply (sq_eq_sq₀ hleft.le (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  exact hid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformCappedStep
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform dyadic removal: all non-geometric constants are chosen before
the translated packet lattice and finite collection. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_uniform_normalized_capped_step (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (densityUpper : ℝ), 1≤densityUpper →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
      Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (energyNorm : ℝ), 0<energyNorm →
      energyNorm^2=(∫ z, ‖g z‖^2 ∂volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
      0<(volume.prod volume).real E →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma → gamma≤densityUpper → ∀ (k : ℤ) (S : Finset P.PacketIndex), S⊆initial →
      (∀ T : SlopeBox, T.width=P.width → T.length≤d.tau →
        P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S T≤
          (Real.sqrt 2*modelSizeThreshold energyNorm ((volume.prod volume).real E) k)^2*T.area) →
      (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q ≤ min gamma (2*(2:ℝ)^k)) →
    ∃ T : Finset P.PacketIndex, T⊆S ∧
      (∀ q∈T, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q ≤ min gamma ((2:ℝ)^k)) ∧
      (∀ U : SlopeBox, U.width=P.width → U.length≤d.tau →
        P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) T U≤
          (modelSizeThreshold energyNorm ((volume.prod volume).real E) k)^2*U.area) ∧
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => (∑ q∈S, V q z)-(∑ q∈T, V q z)) E (volume.prod volume) ∧
      (∫ z in E, ‖(∑ q∈S, V q z)-(∑ q∈T, V q z)‖ ∂volume.prod volume)≤
        d.reverseStepCost CD CS CT CZ densityUpper*((volume.prod volume).real E)*
          reverseThresholdWeight (((volume.prod volume).real E)/energyNorm^2) ((2:ℝ)^k) := by
  obtain ⟨CD,CS,CT,hCD,hCS,hCT,hStep⟩ := exists_ordinary_capped_removal_step hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  obtain ⟨CZ,hCZ,hBoundedAll⟩ := exists_uniform_bounded_unsigned_size
    cStar cEta CEta cb hcEta hcb.le hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ densityUpper hUpper
  have hBounded := hBoundedAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄
  rw [←heq₁,←heq₂,←heq₃,←heq₄,←heq₅] at hStep
  let Z := d.boundedSizeCost CZ
  have hZ : 0<Z := by dsimp [Z,OrdinaryModelConfig.boundedSizeCost]; positivity
  let A := 625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip
  let B := (((4*d.D0+1)^2:ℕ):ℝ)*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip
  let Q := d.sizeAreaConstant CS
  let K := max (Real.sqrt Z) (Real.sqrt 2)
  let U := max densityUpper 2
  let C := (2*A+B*Q)*K*U
  have hA : 0≤A := by
    dsimp only [A]
    exact mul_nonneg (by positivity) (P.referenceTreeConstant_nonneg _ _ _ _ d.hLip)
  have hB : 0≤B := mul_nonneg (Nat.cast_nonneg _) (P.referenceTreeConstant_nonneg _ _ _ _ d.hLip)
  have hQ : 0≤Q := d.sizeAreaConstant_nonneg CS
  have hK : 0≤K := (Real.sqrt_nonneg Z).trans (le_max_left _ _)
  have hU : 0≤U := (zero_le_one.trans hUpper).trans (le_max_left _ _)
  intro g hg hgm hgb energyNorm hN henergy E hE hEfin harea u hu gamma hgamma hgammaU k S hS hsize hden
  let area := (volume.prod volume).real E
  let eta := (2:ℝ)^k
  let sigma := modelSizeThreshold energyNorm area k
  let density := min gamma (2*eta)
  let cap := min (Real.sqrt Z) (Real.sqrt 2*sigma)
  have heta : 0<eta := zpow_pos (by norm_num) k
  have hsigma : 0 < sigma := modelSizeThreshold_pos hN harea k
  have hdensity : 0≤density := le_min hgamma.le (by positivity)
  have hcap : 0 ≤ cap := le_min (Real.sqrt_nonneg Z) (by positivity)
  have hsizeCap (T : SlopeBox) (hwT : T.width=P.width) (htT : T.length≤d.tau) :
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S T ≤ cap^2*T.area := by
    by_cases hsmall : Real.sqrt Z≤Real.sqrt 2*sigma
    · dsimp only [cap]
      rw [min_eq_left hsmall,Real.sq_sqrt hZ.le]
      have hz := (P.unsignedSizeTestEnergy_mono d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) hS T).trans
        (hBounded g 1 zero_le_one hgm hgb T hwT htT)
      simpa only [one_pow,mul_one,Z,OrdinaryModelConfig.boundedSizeCost] using hz
    · dsimp only [cap]
      rw [min_eq_right (le_of_not_ge hsmall)]
      exact hsize T hwT htT
  obtain ⟨T,hTS,hTD,hsizeT,hI,hBound⟩ := hStep N κ Label Item P d.M d.Q d.gap d.packGap d.R d.K d.D0
    d.w d.tau sigma (Real.sqrt 2) d.epsilon d.A d.margin d.F d.radius d.Lip eta density cap
    hsigma (Real.sqrt_nonneg 2) hcap d.hepsilon heta hdensity d.hLip d.hw d.hW d.hF d.hfreq
    d.hgap d.hpack d.hmargin d.hA d.hQ d.hQnear d.hR d.horder d.hD0 d.htime d.hwide d.hK d.hlocal
    d.cell d.grid g hg (P.ordinaryCoefficient g) rfl S hsize hsizeCap
    (fun q hq => d.hrow q (hS hq)) (fun q hq => d.heps q (hS hq)) d.spectrum
    (fun q hq => d.margin_spectrum q (hS hq)) (fun q hq => d.bin q (hS hq))
    d.selector d.measurable d.bounded d.away d.support d.radius_bound d.near E hE hEfin u hu hden
  refine ⟨T,hTS,fun q hq => le_min ((hden q (hTS hq)).trans (min_le_left _ _)) (hTD q hq),hsizeT,hI,?_⟩
  have hscale : sigma^2*area=eta*(∫ z, ‖g z‖^2 ∂volume.prod volume) := by
    rw [←henergy]
    exact modelSizeThreshold_identity energyNorm area harea k
  have hn := combine_capped_removal_budgets A B Q cap sigma density eta area
    (∫ z, ‖g z‖^2 ∂volume.prod volume) hB hQ hcap hsigma hdensity heta harea.le hscale
  have hcBound : cap≤K*min 1 (Real.sqrt (eta/(area/energyNorm^2))) := by
    calc
      cap ≤ K*min 1 sigma := min_scaled_le (Real.sqrt Z) (Real.sqrt 2) sigma hsigma.le
      _ = _ := by
        have he : sigma=Real.sqrt (eta/(area/energyNorm^2)) := modelSizeThreshold_eq_sqrt_ratio hN harea k
        rw [he]
  have hdBound : density≤U*min 1 eta :=
    (min_le_min hgammaU le_rfl).trans (min_scaled_le densityUpper 2 eta heta.le)
  have hw := capped_density_weight_le cap density eta (area/energyNorm^2) K U
    heta hK hdensity hcBound hdBound
  have hwNonneg : 0 ≤ reverseThresholdWeight (area/energyNorm^2) eta := by
    dsimp only [reverseThresholdWeight]
    positivity
  apply hBound.trans
  change A*cap*density*(1+eta^(-(1/20:ℝ)))*(2*area/eta)+
    B*cap*density*((Q/sigma^2)*(∫ z, ‖g z‖^2 ∂volume.prod volume))≤_
  calc
    _ ≤ (2*A+B*Q)*cap*density*(1+eta^(-(1/20:ℝ)))*area/eta := hn
    _ = ((2*A+B*Q)*area)*(cap*density*(1+eta^(-(1/20:ℝ)))/eta) := by ring
    _ ≤ ((2*A+B*Q)*area)*(K*U*reverseThresholdWeight (area/energyNorm^2) eta) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = C*area*reverseThresholdWeight (area/energyNorm^2) eta := by dsimp only [C]; ring
    _ ≤ (1+C)*area*reverseThresholdWeight (area/energyNorm^2) eta :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C≤1+C) harea.le) hwNonneg

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformReverseModel
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reverse estimate from actual finite removals. The four input
constants are independent of packet count, translation and the scale interval. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
namespace OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem reverseStepCost_pos (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) :
    0<d.reverseStepCost CD CS CT CZ U := by
  have hD := P.referenceTreeConstant_nonneg CD ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hT := P.referenceTreeConstant_nonneg CT ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hS := d.sizeAreaConstant_nonneg CS
  have hU : 0 < max U 2 := lt_max_of_lt_right (by norm_num)
  have hK : 0 ≤ max (Real.sqrt (d.boundedSizeCost CZ)) (Real.sqrt 2) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  unfold reverseStepCost
  positivity

theorem reverseModelCost_pos (d : OrdinaryModelConfig P initial) (CD CS CT CZ U : ℝ) :
    0<d.reverseModelCost CD CS CT CZ U := by
  have hA := d.reverseStepCost_pos CD CS CT CZ U
  have hG : 0<8/(1-reverseThresholdRatio) :=
    div_pos (by norm_num) (sub_pos.mpr reverseThresholdRatio_lt_one)
  unfold reverseModelCost
  positivity

end OrdinaryModelConfig

theorem exists_uniform_reverse_model_bound (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (densityUpper : ℝ), 1≤densityUpper →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), MemLp g 2 (volume.prod volume) →
      Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (energyNorm : ℝ), 0<energyNorm →
      energyNorm^2=(∫ z, ‖g z‖^2 ∂volume.prod volume) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
      0<(volume.prod volume).real E →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (gamma : ℝ), 0<gamma → gamma≤densityUpper →
      (∀ q∈initial, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤gamma) →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈initial, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈initial, V q z‖ ∂volume.prod volume)≤
          d.reverseModelCost CD CS CT CZ densityUpper*((volume.prod volume).real E)*
            (((volume.prod volume).real E)/energyNorm^2)^(-(1/20:ℝ)) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_normalized_capped_step hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ densityUpper hUpper
  have hStep := hAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄ heq₅ densityUpper hUpper
  let A := d.reverseStepCost CD CS CT CZ densityUpper
  have hApos : 0<A := d.reverseStepCost_pos CD CS CT CZ densityUpper
  let G := 8/(1-reverseThresholdRatio)
  have hA : 0≤A := hApos.le
  have hG : 0<G := div_pos (by positivity) (sub_pos.mpr reverseThresholdRatio_lt_one)
  intro g hg hgm hgb energyNorm hN henergy E hE hEfin harea u hu gamma hgamma hgammaUpper hden V
  let area := (volume.prod volume).real E
  let State := fun (k : ℤ) (S : Finset P.PacketIndex) => S⊆initial ∧
    (∀ q∈S, P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q ≤ min gamma ((2:ℝ)^k)) ∧
    (∀ U : SlopeBox, U.width=P.width → U.length≤d.tau →
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) S U≤
        (modelSizeThreshold energyNorm area k)^2*U.area)
  let v := fun (q : P.PacketIndex) (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
    P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
      P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
  let ratio := area/energyNorm^2
  have hratioPos : 0 < ratio := div_pos harea (sq_pos_of_pos hN)
  let L := A*area
  let B := fun k : ℤ => L*reverseThresholdWeight ratio ((2:ℝ)^(k-1))
  have hLnonneg : 0≤L := by dsimp only [L]; positivity
  have step (k : ℤ) (S : Finset P.PacketIndex) (hS : State k S) :
      ∃ T, T⊆S ∧ State (k-1) T ∧
        IntegrableOn (fun z => finitePacketSum v S z-finitePacketSum v T z) E (volume.prod volume) ∧
        (∫ z in E, ‖finitePacketSum v S z-finitePacketSum v T z‖ ∂volume.prod volume)≤B k := by
    have hsize (U : SlopeBox) (hwU : U.width=P.width) (htU : U.length≤d.tau) := hS.2.2 U hwU htU
    simp only [modelSizeThreshold_successive energyNorm area harea k] at hsize
    have hpow : 2*(2:ℝ)^(k-1)=(2:ℝ)^k := by
      rw [zpow_sub₀ (by norm_num),zpow_one]
      ring
    obtain ⟨T,hTS,hTD,hTZ,hI,hBound⟩ := hStep g hg hgm hgb energyNorm hN henergy E hE hEfin harea
      u hu gamma hgamma hgammaUpper (k-1) S hS.1 hsize (by simpa only [hpow] using hS.2.1)
    exact ⟨T,hTS,⟨hTS.trans hS.1,hTD,hTZ⟩,hI,hBound⟩
  obtain ⟨s0,hs0,hsize0⟩ := P.exists_finite_unsigned_size_bound d.w d.cb d.cell d.grid
    (P.ordinaryCoefficient g) initial
  obtain ⟨k0,hk0⟩ := exists_dyadic_upper_level (max densityUpper (s0^2*area/energyNorm^2))
  have hInitial : State k0 initial := by
    refine ⟨Finset.Subset.refl _,?_,?_⟩
    · intro q hq
      exact le_min (hden q hq) ((hden q hq).trans
        (hgammaUpper.trans ((le_max_left _ _).trans hk0.le)))
    · intro U hwU htU
      have hratio : s0^2*area/energyNorm^2<(2:ℝ)^k0 := (le_max_right _ _).trans_lt hk0
      have hprod := (div_lt_iff₀ (sq_pos_of_pos hN)).mp hratio
      have hid := modelSizeThreshold_identity energyNorm area harea k0
      have hs : s0^2≤(modelSizeThreshold energyNorm area k0)^2 := by nlinarith
      exact (hsize0 U hwU).trans (mul_le_mul_of_nonneg_right hs U.area_pos.le)
  obtain ⟨kend,hend⟩ := exists_dyadic_zero_detection initial
    (P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u)
  let n := (k0-min k0 kend).toNat
  have hn : (n:ℤ)=k0-min k0 kend := Int.toNat_of_nonneg (sub_nonneg.mpr (min_le_left _ _))
  have hlast : k0-(n:ℤ)≤kend := by rw [hn]; omega
  obtain ⟨T,hT,hState,hI,hBound⟩ := iterate_finite_removal v E State B step n k0 initial hInitial
  have hzeroDensity (q : P.PacketIndex) (hq : q∈T) :
      P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤0 :=
    hend q (hT hq) (((hState.2.1 q hq).trans (min_le_right _ _)).trans
      (zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hlast))
  have hzero : finitePacketSum v T=ᵐ[(volume.prod volume).restrict E] 0 :=
    P.packet_sum_zero_of_density_zero T d.cell d.grid d.w d.tau
      (fun q hq => d.hlength q (hT hq)) (fun q hq => d.hrow q (hT hq)) E hE u hu
      hzeroDensity (P.ordinaryCoefficient g) d.selector d.support
  let indices := (Finset.range n).image (fun i : ℕ => k0-(i:ℤ)-1)
  have hindices : (∑ j∈indices, reverseThresholdWeight ratio ((2:ℝ)^j))=
      ∑ i∈Finset.range n, reverseThresholdWeight ratio ((2:ℝ)^(k0-(i:ℤ)-1)) := by
    apply Finset.sum_image (g:=fun i : ℕ => k0-(i:ℤ)-1)
    intro i _ j _ hij
    change k0-(i:ℤ)-1=k0-(j:ℤ)-1 at hij
    omega
  have hsum : (∑ i∈Finset.range n, B (k0-(i:ℤ)))≤L*(G*ratio^(-(1/20:ℝ))) := by
    change (∑ i∈Finset.range n, L*reverseThresholdWeight ratio ((2:ℝ)^((k0-(i:ℤ))-1)))≤_
    rw [←Finset.mul_sum,←hindices]
    exact mul_le_mul_of_nonneg_left (reverseThreshold_finite_sum hratioPos indices) hLnonneg
  obtain ⟨hFull,hFullBound⟩ := finite_removal_zero_remainder v E initial T hI hzero _ (hBound.trans hsum)
  refine ⟨hFull,hFullBound.trans ?_⟩
  change L*(G*ratio^(-(1/20:ℝ)))≤(1+G*A)*area*ratio^(-(1/20:ℝ))
  calc
    _ = (G*A)*(area*ratio^(-(1/20:ℝ))) := by dsimp only [L]; ring
    _ ≤ (1+G*A)*(area*ratio^(-(1/20:ℝ))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReverseCost
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial dependence of the reverse estimate on packet adaptation.
Its remaining constants use only the fixed geometric parameters. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
  {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}

theorem reverseStepCost_le_quartic (d : OrdinaryModelConfig P initial)
    (CD CS CT CZ U bound : ℝ) (hCS : 0≤CS) (hCZ : 0≤CZ) (hb : 1≤bound)
    (hp : P.profileBound≤bound) (ha : P.referenceEnvelopeConstant≤bound) :
    d.reverseStepCost CD CS CT CZ U≤d.unitReverseStepCost CD CS CT CZ U*bound^4 := by
  have hbp : 0≤bound := zero_le_one.trans hb
  have hb2 : 1≤bound^2 := one_le_pow₀ hb
  have hb4 : 1≤bound^4 := one_le_pow₀ hb
  have hz : d.boundedSizeCost CZ≤(1+((3*d.M:ℕ):ℝ)*CZ)*bound^2 := by
    unfold boundedSizeCost
    calc
      _ ≤ bound^2+((3*d.M:ℕ):ℝ)*CZ*bound^2 := by
        gcongr
        exact P.referenceEnvelopeConstant_pos.le
      _ = _ := by ring
  have hsqrt : Real.sqrt (d.boundedSizeCost CZ)≤
      Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)*bound := by
    apply (Real.sqrt_le_sqrt hz).trans_eq
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hbp]
  have hk : max (Real.sqrt (d.boundedSizeCost CZ)) (Real.sqrt 2)≤
      max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*bound := by
    rw [max_mul_of_nonneg _ _ hbp]
    exact max_le_max hsqrt (le_mul_of_one_le_right (Real.sqrt_nonneg _) hb)
  let td := ordinaryTreeUnitCost CD ((2*d.R+1)*d.M) d.K d.Lip
  let tt := ordinaryTreeUnitCost CT ((2*d.R+1)*d.M) d.K d.Lip
  let sz := d.unitSizeAreaCost CS
  let sp := (((4*d.D0+1)^2:ℕ):ℝ)
  have ht := transverseTailConstant_nonneg
  have hLip := d.hLip
  have htd : 0≤td := by dsimp only [td,ordinaryTreeUnitCost]; positivity
  have htt : 0≤tt := by dsimp only [tt,ordinaryTreeUnitCost]; positivity
  have hsz : 0 ≤ sz := by dsimp only [sz,unitSizeAreaCost,selectedNearUnitCost]; positivity
  have hsp : 0 ≤ sp := Nat.cast_nonneg _
  have htdb := P.referenceTreeConstant_le_unit CD ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hp ha
  have httb := P.referenceTreeConstant_le_unit CT ((2*d.R+1)*d.M) d.K d.Lip bound d.hLip hp ha
  have hsize := d.sizeAreaConstant_nonneg CS
  have hszb := d.sizeAreaConstant_le_unit CS bound hCS hp ha
  have hb3 : bound≤bound^3 := by
    have h := mul_nonneg (sub_nonneg.mpr hb) (by positivity : 0≤bound^2+bound)
    nlinarith
  have hcore :
      2*(625*densityRadiusConstant^2*P.referenceTreeConstant CD ((2*d.R+1)*d.M) d.K d.Lip)+
        sp*P.referenceTreeConstant CT ((2*d.R+1)*d.M) d.K d.Lip*d.sizeAreaConstant CS≤
      d.reverseCoreUnitCost CD CS CT*bound^3 := by
    calc
      _ ≤ 2*(625*densityRadiusConstant^2*(td*bound))+sp*(tt*bound)*(sz*bound^2) := by
        gcongr
      _ = (2*625*densityRadiusConstant^2*td)*bound+(sp*tt*sz)*bound^3 := by ring
      _ ≤ (2*625*densityRadiusConstant^2*td)*bound^3+(sp*tt*sz)*bound^3 :=
        add_le_add (mul_le_mul_of_nonneg_left hb3 (by positivity)) le_rfl
      _ = _ := by dsimp only [reverseCoreUnitCost,td,tt,sz,sp]; ring
  have hD := P.referenceTreeConstant_nonneg CD ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hT := P.referenceTreeConstant_nonneg CT ((2*d.R+1)*d.M) d.K d.Lip d.hLip
  have hU : 0 ≤ max U 2 := le_max_of_le_right (by norm_num)
  have hcore0 : 0≤d.reverseCoreUnitCost CD CS CT := by
    change 0≤2*(625*densityRadiusConstant^2*td)+sp*tt*sz
    positivity
  unfold reverseStepCost unitReverseStepCost
  calc
    _ ≤ 1+(d.reverseCoreUnitCost CD CS CT*bound^3)*
        (max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*bound)*max U 2 := by
      gcongr
    _ ≤ bound^4+(d.reverseCoreUnitCost CD CS CT*bound^3)*
        (max (Real.sqrt (1+((3*d.M:ℕ):ℝ)*CZ)) (Real.sqrt 2)*bound)*max U 2 :=
      add_le_add hb4 le_rfl
    _ = _ := by ring

theorem reverseModelCost_le_quartic (d : OrdinaryModelConfig P initial)
    (CD CS CT CZ U bound : ℝ) (hCS : 0≤CS) (hCZ : 0≤CZ) (hb : 1≤bound)
    (hp : P.profileBound≤bound) (ha : P.referenceEnvelopeConstant≤bound) :
    d.reverseModelCost CD CS CT CZ U≤d.unitReverseModelCost CD CS CT CZ U*bound^4 := by
  have hG : 0≤8/(1-reverseThresholdRatio) :=
    (div_pos (by norm_num) (sub_pos.mpr reverseThresholdRatio_lt_one)).le
  have hstep := d.reverseStepCost_le_quartic CD CS CT CZ U bound hCS hCZ hb hp ha
  unfold reverseModelCost unitReverseModelCost
  calc
    _ ≤ 1+(8/(1-reverseThresholdRatio))*(d.unitReverseStepCost CD CS CT CZ U*bound^4) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep hG)
    _ ≤ bound^4+(8/(1-reverseThresholdRatio))*(d.unitReverseStepCost CD CS CT CZ U*bound^4) :=
      add_le_add (one_le_pow₀ hb) le_rfl
    _ = _ := by ring

end LipschitzHilbert.PacketLatticeData.OrdinaryModelConfig

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrdinaryModelConstructionCost
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cost of the constructed ordinary models is a fixed number.
In particular it has no dependence on the finite lattice or translation. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData

theorem OrdinaryModelConfig.unitReverseModelCost_of_numeric_fields
    {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
    [Fintype κ] [∀ j l, Fintype (Item j l)]
    {P : PacketLatticeData N κ Label Item} {initial : Finset P.PacketIndex}
    (d : OrdinaryModelConfig P initial) (cStar cEta cb radius : ℝ)
    (num : OrdinaryModelNumerics cStar cEta cb radius) (M : ℕ) (CD CS CT CZ : ℝ)
    (hcb : d.cb=cb) (hM : d.M=M) (hQ : d.Q=1) (hR : d.R=1)
    (hgap : d.gap=num.gap) (hpack : d.packGap=num.packGap)
    (hK : d.K=num.K) (hD0 : d.D0=5) (hLip : d.Lip=1) :
    d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper=num.reverseUnitCost M CD CS CT CZ := by
  simp only [OrdinaryModelConfig.unitReverseModelCost,OrdinaryModelConfig.unitReverseStepCost,
    OrdinaryModelConfig.reverseCoreUnitCost,OrdinaryModelConfig.unitSizeAreaCost,
    hcb,hM,hQ,hR,hgap,hpack,hK,hD0,hLip]
  rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SupportedInnerIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded tests supported on a measurable set turn local norm bounds
into literal global pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem supported_inner_integral_le {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (mu : Measure X) (E : Set X) (hE : MeasurableSet E)
    (F g : X → EuclideanSpace ℂ κ) (hF : IntegrableOn F E mu)
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖≤1) (hgs : ∀ x, x∉E → g x=0) :
    Integrable (fun x => inner ℂ (F x) (g x)) mu ∧
      ‖∫ x, inner ℂ (F x) (g x) ∂mu‖≤∫ x in E, ‖F x‖ ∂mu := by
  have hp (x : X) : ‖inner ℂ (F x) (g x)‖≤‖F x‖ :=
    (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hg1 x))
  have hlocal : IntegrableOn (fun x => inner ℂ (F x) (g x)) E mu :=
    hF.norm.mono' (hF.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall hp)
  have he (x : X) : E.indicator (fun x => inner ℂ (F x) (g x)) x=inner ℂ (F x) (g x) := by
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,hgs x hx,inner_zero_right]
  have hglobal := ((integrable_indicator_iff hE).2 hlocal).congr (Filter.Eventually.of_forall he)
  refine ⟨hglobal,?_⟩
  have hI : (∫ x, inner ℂ (F x) (g x) ∂mu)=∫ x in E, inner ℂ (F x) (g x) ∂mu := by
    rw [←integral_indicator hE,funext he]
  rw [hI]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hlocal.norm hF.norm hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite synthesis/analysis duality with arbitrary synthesizing coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem finite_analyzing_pairing {X I K : Type*} [MeasurableSpace X] [Fintype K]
    (mu : Measure X) (area : I → ℝ) (wave : I → K → X → ℂ)
    (g : X → EuclideanSpace ℂ K) (c : I → EuclideanSpace ℂ K) (S : Finset I)
    (ha : ∀ i∈S, area i≠0)
    (hint : ∀ i∈S, ∀ k, Integrable (fun x => g x k*conj (wave i k x)) mu) :
    (∫ x, inner ℂ (∑ i∈S, WithLp.toLp 2 (fun k => c i k*wave i k x)) (g x) ∂mu)=
      ∑ i∈S, (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i) := by
  have hterm (i : I) (hi : i∈S) :
      (area i:ℂ)*inner ℂ (c i) (analyzingCoefficient mu area wave g i)=
        ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have harea : (area i:ℂ)*analyzingCoefficient mu area wave g i k=
        ∫ x, g x k*conj (wave i k x) ∂mu := by
      change (area i:ℂ)*(((area i)⁻¹:ℂ)*_)=_
      rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast ha i hi),one_mul]
    rw [←harea]
    ring
  have hInt (i : I) (hi : i∈S) (k : K) :
      Integrable (fun x => conj (c i k)*(g x k*conj (wave i k x))) mu :=
    (hint i hi k).const_mul _
  symm
  calc
    _ = ∑ i∈S, ∑ k, conj (c i k)*(∫ x, g x k*conj (wave i k x) ∂mu) :=
      Finset.sum_congr rfl hterm
    _ = ∫ x, ∑ i∈S, ∑ k, conj (c i k)*(g x k*conj (wave i k x)) ∂mu := by
      simp_rw [←integral_const_mul]
      rw [integral_finsetSum S (fun i hi => integrable_finsetSum _ (fun k _ => hInt i hi k))]
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i hi k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply,RCLike.inner_apply,WithLp.ofLp_sum,Finset.sum_apply,
        map_sum,map_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjoint
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal finite adjoint duality for the ordinary masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem masked_physical_packet_memLp
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (q : P.PacketIndex) (k : κ) :
    MemLp (fun z => b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
      2 (volume.prod volume) := by
  apply ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).mono
    ((((hb q.1 q.2.1 k).comp hu).mul
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).continuous.measurable).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z‖≤_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb1 q.1 q.2.1 k (u z))

theorem ordinaryAdjointSum_memLp (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    MemLp (P.ordinaryAdjointSum S b u g) 2 (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.packetVector_memLp _ q)

theorem ordinary_forward_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2)
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) := by
  let area := fun q : P.PacketIndex => P.length q.1*P.width
  let masked := fun (q : P.PacketIndex) (k : κ) (z : ℝ×ℝ) =>
    b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
  let cf := fun q : P.PacketIndex => P.ordinaryCoefficient f q.1 q.2.1 q.2.2
  have ha (q : P.PacketIndex) (_hq : q∈S) : area q≠0 := (mul_pos (P.length_pos _) P.width_pos).ne'
  have hm (q : P.PacketIndex) (_hq : q∈S) (k : κ) :
      Integrable (fun z => g z k*conj (masked q k z)) (volume.prod volume) :=
    ((memLp_piLp_iff.mp hg) k).integrable_mul (P.masked_physical_packet_memLp b hb hb1 u hu q k).star
  have h := finite_analyzing_pairing (volume.prod volume) area masked g cf S ha hm
  have he (z : ℝ×ℝ) : (∑ q∈S, WithLp.toLp 2 (fun k => cf q k*masked q k z))=
      P.ordinaryForwardSum S b u f z := by
    apply Finset.sum_congr rfl
    intro q _
    apply WithLp.ofLp_injective
    funext k
    change cf q k*(b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)=
      cf q k*b q.1 q.2.1 k (u z)*P.physicalPacket 0 q.1 q.2.1 q.2.2 k z
    ring
  have hc (q : P.PacketIndex) : analyzingCoefficient (volume.prod volume) area masked g q=
      P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 := rfl
  simp_rw [he,hc] at h
  exact h

theorem ordinary_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : MemLp f 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume)=
      ∑ q∈S, ((P.length q.1*P.width:ℝ):ℂ)*inner ℂ
        (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2)
        (P.ordinaryCoefficient f q.1 q.2.1 q.2.2) := by
  apply finite_analyzing_pairing (volume.prod volume)
    (fun q : P.PacketIndex => P.length q.1*P.width)
    (fun q k => P.physicalPacket 0 q.1 q.2.1 q.2.2 k) f
    (fun q => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2) S
  · intro q _
    exact (mul_pos (P.length_pos _) P.width_pos).ne'
  · intro q _ k
    exact ((memLp_piLp_iff.mp hf) k).integrable_mul
      ((P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)).star

theorem ordinary_forward_adjoint_pairing (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume)) :
    (∫ z, inner ℂ (P.ordinaryForwardSum S b u f z) (g z) ∂volume.prod volume)=
      conj (∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume) := by
  rw [P.ordinary_forward_pairing S b hb hb1 u hu f g hg,P.ordinary_adjoint_pairing S b u f g hf,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul,Complex.conj_ofReal,inner_conj_symm]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAdjointPairingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a tested ordinary forward estimate to its literal adjoint
pairing. All integrals retain their actual packet sums. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert

theorem integrable_euclidean_inner {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) {f g : X → EuclideanSpace ℂ κ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z => inner ℂ (f z) (g z)) μ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  exact integrable_finsetSum _ (fun k _ =>
    ((memLp_piLp_iff.mp hg) k).integrable_mul (((memLp_piLp_iff.mp hf) k).star))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjointPairingBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Forward-adjoint duality for the unrestricted physical packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem ordinary_adjoint_pairing_bound (P : PacketLatticeData N κ Label Item)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : MemLp f 2 (volume.prod volume)) (hg : MemLp g 2 (volume.prod volume))
    (hgm : Measurable g) (hgb : ∀ z, ‖g z‖≤1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (hgs : ∀ z, z∉E → g z=0)
    (hint : IntegrableOn (P.ordinaryForwardSum S b u f) E (volume.prod volume)) :
    Integrable (fun z => inner ℂ (P.ordinaryAdjointSum S b u g z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (P.ordinaryAdjointSum S b u g z) (f z) ∂volume.prod volume‖≤
        ∫ z in E, ‖P.ordinaryForwardSum S b u f z‖ ∂volume.prod volume := by
  refine ⟨integrable_euclidean_inner _ (P.ordinaryAdjointSum_memLp S b u g) hf,?_⟩
  have h := P.ordinary_forward_adjoint_pairing S b hb hb1 u hu f g hf hg
  have hn := congrArg norm h
  rw [RCLike.norm_conj] at hn
  rw [←hn]
  exact (supported_inner_integral_le (volume.prod volume) E hE _ g hint hgm hgb hgs).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinct-profile, masked analyzing packet sum. No auxiliary
jet is needed for the physical bilinear operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem crossPacketValue_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (q : P.PacketIndex) :
    MemLp (fun z => P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact (((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).memLp p
    (volume.prod volume)).const_mul _

theorem crossSum_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (S : Finset P.PacketIndex) :
    MemLp (fun z => ∑ q∈S, P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.crossPacketValue_memLp alt hAlt t b v g p q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAdjointPolarization
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact polarization for masked analyzing coefficients and their
unmasked, distinct-profile adjoint synthesis. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem polarize_multiplier_coefficient (c : ℂ) (hc : ‖c‖=1)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (j : Fin N) (l : P.labels j) (a : Item j l) :
    (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g j l a=
      P.physicalMultiplierCoefficient 0 b u g j l a+
        conj c • (P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g j l a := by
  let f := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) => b j l k (u z)*P.physicalPacket 0 j l a k z
  let h := fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
    b j l k (u z)*(P.withProfile alt hAlt).physicalPacket 0 j l a k z
  have he : (fun (a : Item j l) (k : κ) (z : ℝ×ℝ) =>
      b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z)=
      fun a k z => f a k z+c*h a k z := by
    funext a k z
    rw [P.polarize_physicalPacket alt hAlt c hc]
    change b j l k (u z)*(P.physicalPacket 0 j l a k z+c*(P.withProfile alt hAlt).physicalPacket 0 j l a k z)=_
    dsimp only [f,h]
    ring
  change analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun a k z => b j l k (u z)*(P.polarize alt hAlt c hc).physicalPacket 0 j l a k z) g a=_
  rw [he]
  exact analyzingCoefficient_add_smul (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    f h g c
    (fun a k => P.physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k)
    (fun a k => (P.withProfile alt hAlt).physical_multiplier_analyzing_integrable 0 (fun z => b j l k (u z))
      ((hb j l k).comp hu) (fun z => hb1 j l k (u z)) g hg hg1 j l a k) a

theorem cross_adjoint_polarization (S : Finset P.PacketIndex)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (z : ℝ×ℝ) :
    (4:ℂ) • (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)=
      (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g z-
      (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g z-
      Complex.I • (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g z+
      Complex.I • (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g z := by
  have hcross (q : P.PacketIndex) : P.crossPacketValue alt hAlt 0 b u g z q=
      WithLp.toLp 2 (fun k => P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
        (P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := rfl
  have hterm (c : ℂ) (hc : ‖c‖=1) (q : P.PacketIndex) (k : κ) :
      (P.polarize alt hAlt c hc).packetVector
        ((P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g) q z k=
      (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k+
        conj c*(P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)*
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z+c*(P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
    change (P.polarize alt hAlt c hc).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k*
      (P.polarize alt hAlt c hc).physicalPacket 0 q.1 q.2.1 q.2.2 k z=_
    rw [P.polarize_multiplier_coefficient alt hAlt c hc b hb hb1 u hu g hg hg1,
      P.polarize_physicalPacket alt hAlt c hc]
    simp only [PiLp.add_apply,PiLp.smul_apply,add_apply,smul_apply,smul_eq_mul]
  apply WithLp.ofLp_injective
  funext k
  simp only [hcross,ordinaryAdjointSum,WithLp.ofLp_sum,Finset.sum_apply,
    WithLp.ofLp_smul,WithLp.ofLp_add,WithLp.ofLp_sub,
    Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  simp only [hterm]
  simp only [map_one,map_neg,Complex.conj_I,one_mul,neg_mul,neg_neg,
    Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have h := packet_cross_polarization
    (P.physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    ((P.withProfile alt hAlt).physicalMultiplierCoefficient 0 b u g q.1 q.2.1 q.2.2 k)
    (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)
    ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k z)
  linear_combination -h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossPairingBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four exact polarized adjoint pairings control the distinct-profile
pairing with no loss in a common bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_pairing_bound (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g f : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (hf : MemLp f 2 (volume.prod volume)) (B : ℝ)
    (hbound : ∀ (c : ℂ) (hc : ‖c‖=1),
      ‖∫ z, inner ℂ ((P.polarize alt hAlt c hc).ordinaryAdjointSum S b u g z) (f z)
        ∂volume.prod volume‖≤B) :
    Integrable (fun z => inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
      (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
        (f z) ∂volume.prod volume‖≤B := by
  let A := (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g
  let Bv := (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g
  let C := (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g
  let D := (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g
  let X := fun z => ∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q
  have hA : Integrable (fun z => inner ℂ (A z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hB : Integrable (fun z => inner ℂ (Bv z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hC : Integrable (fun z => inner ℂ (C z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hD : Integrable (fun z => inner ℂ (D z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  refine ⟨integrable_euclidean_inner _ (P.crossSum_memLp alt hAlt 0 b u g 2 S) hf,?_⟩
  have hpoint (z : ℝ×ℝ) : (4:ℂ)*inner ℂ (X z) (f z)=
      inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
        Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) := by
    have h := congrArg (fun v => inner ℂ v (f z))
      (P.cross_adjoint_polarization alt hAlt S b hb hb1 u hu g hg hg1 z)
    simpa only [inner_smul_left,inner_add_left,inner_sub_left,map_ofNat,
      Complex.conj_I,neg_mul,sub_neg_eq_add,←sub_eq_add_neg] using h
  let ia := ∫ z, inner ℂ (A z) (f z) ∂volume.prod volume
  let ib := ∫ z, inner ℂ (Bv z) (f z) ∂volume.prod volume
  let ic := ∫ z, inner ℂ (C z) (f z) ∂volume.prod volume
  let idv := ∫ z, inner ℂ (D z) (f z) ∂volume.prod volume
  have hint : (4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)=
      ia-ib+Complex.I*ic-Complex.I*idv := by
    calc
      _ = ∫ z, (4:ℂ)*inner ℂ (X z) (f z) ∂volume.prod volume := (integral_const_mul _ _).symm
      _ = ∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
          Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z)
          ∂volume.prod volume := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by
        have hs : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
              Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)-
            (∫ z, Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume) :=
          integral_sub ((hA.sub hB).add (hC.const_mul Complex.I)) (hD.const_mul Complex.I)
        have ha : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)+
            (∫ z, Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume) :=
          integral_add (hA.sub hB) (hC.const_mul Complex.I)
        have hb : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)=ia-ib :=
          integral_sub hA hB
        rw [hs,ha,hb,integral_const_mul,integral_const_mul]
  have hnorm : 4*‖∫ z, inner ℂ (X z) (f z) ∂volume.prod volume‖≤
      ‖ia‖+‖ib‖+‖ic‖+‖idv‖ := by
    calc
      _ = ‖(4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)‖ := by
        rw [norm_mul]; norm_num
      _ = ‖ia-ib+Complex.I*ic-Complex.I*idv‖ := congrArg norm hint
      _ ≤ (‖ia‖+‖ib‖)+‖ic‖+‖idv‖ := by
        calc
          _ ≤ ‖ia-ib+Complex.I*ic‖+‖Complex.I*idv‖ := norm_sub_le _ _
          _ ≤ (‖ia-ib‖+‖Complex.I*ic‖)+‖Complex.I*idv‖ :=
            add_le_add (norm_add_le _ _) le_rfl
          _ ≤ ((‖ia‖+‖ib‖)+‖Complex.I*ic‖)+‖Complex.I*idv‖ := by
            gcongr; exact norm_sub_le _ _
          _ = _ := by simp only [norm_mul,Complex.norm_I,one_mul]
  have ha : ‖ia‖≤B := hbound 1 (by simp)
  have hb' : ‖ib‖≤B := hbound (-1) (by simp)
  have hc : ‖ic‖≤B := hbound Complex.I (by simp)
  have hd : ‖idv‖≤B := hbound (-Complex.I) (by simp)
  nlinarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundedInputEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-support bounded inputs have finite energy, bounded by support area. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem bounded_supported_input {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g)
    (hbound : ∀ z, ‖g z‖≤1) (F : Set (ℝ×ℝ))
    (hF : MeasurableSet F) (hFfin : (volume.prod volume) F≠∞)
    (hsupport : ∀ z, z∉F → g z=0) :
    MemLp g 2 (volume.prod volume) ∧
      (∫ z, ‖g z‖^2 ∂volume.prod volume)≤(volume.prod volume).real F := by
  have hI : MemLp (F.indicator (fun _ => (1:ℝ))) 2 (volume.prod volume) :=
    memLp_indicator_const 2 hF 1 (Or.inr hFfin)
  have hb (z : ℝ×ℝ) : ‖g z‖≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,le_refl]
  have hMem : MemLp g 2 (volume.prod volume) :=
    hI.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hMem,?_⟩
  have hsq (z : ℝ×ℝ) : ‖g z‖^2≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      nlinarith [hbound z,norm_nonneg (g z)]
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,zero_pow (by decide : 2≠0),le_refl]
  have hle := integral_mono_ae (hMem.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((integrable_indicator_iff hF).2 (integrableOn_const (μ:=volume.prod volume) (C:=(1:ℝ)) hFfin))
    (Filter.Eventually.of_forall hsq)
  simpa only [integral_indicator_const (1:ℝ) hF,smul_eq_mul,mul_one] using hle

theorem reverse_disparity_identity {area support : ℝ} (harea : 0<area) (hsupport : 0 < support) :
    area*(area/support)^(-(1/20:ℝ))=
      Real.sqrt (support*area)*(area/support)^(9/20:ℝ) := by
  have hratio : 0<area/support := div_pos harea hsupport
  have he : (9/20:ℝ)=1/2+(-(1/20:ℝ)) := by norm_num
  rw [he,Real.rpow_add hratio,←Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (support*area)*Real.sqrt (area/support)=area := by
    rw [←Real.sqrt_mul (mul_pos hsupport harea).le]
    have hp : support*area*(area/support)=area^2 := by field_simp
    rw [hp,Real.sqrt_sq harea.le]
  rw [←mul_assoc,hsqrt]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformReverseDisparity
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported reverse estimate with constants independent of the
finite lattice. All geometric dependence is exposed in reverseModelCost. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
theorem exists_uniform_reverse_disparity (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (F : Set (ℝ×ℝ)), MeasurableSet F → (volume.prod volume) F≠∞ →
      (∀ z, z∉F → g z=0) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → (volume.prod volume) E≠∞ →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      let V := fun q (z : ℝ×ℝ) => WithLp.toLp 2 (fun j =>
        P.ordinaryCoefficient g q.1 q.2.1 q.2.2 j*d.selector q.1 q.2.1 j (u z)*
          P.physicalPacket 0 q.1 q.2.1 q.2.2 j z)
      IntegrableOn (fun z => ∑ q∈initial, V q z) E (volume.prod volume) ∧
        (∫ z in E, ‖∑ q∈initial, V q z‖ ∂volume.prod volume)≤
          d.reverseModelCost CD CS CT CZ ordinaryDensityUpper*Real.sqrt (((volume.prod volume).real F)*((volume.prod volume).real E))*
            (((volume.prod volume).real E)/((volume.prod volume).real F))^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_reverse_model_bound hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅
  let U := ordinaryDensityUpper
  have hU : 1≤U := le_max_left _ _
  have hModel := hAll N κ Label Item P initial d heq₁ heq₂ heq₃ heq₄ heq₅ U hU
  let C := d.reverseModelCost CD CS CT CZ U
  have hC : 0<C := d.reverseModelCost_pos CD CS CT CZ U
  intro g hgm hgb F hF hFfin hsupport E hE hEfin u hu V
  obtain ⟨hg,henergyBound⟩ := bounded_supported_input g hgm hgb F hF hFfin hsupport
  by_cases henergy : (∫ z, ‖g z‖^2 ∂volume.prod volume)=0
  · have heval (z : ℝ×ℝ) : (∑ q∈initial, V q z)=0 := by
      apply Finset.sum_eq_zero
      intro q _
      have hc := P.ordinaryCoefficient_zero_of_energy_zero g hg henergy q.1 q.2.1 q.2.2
      apply WithLp.ofLp_injective
      funext k
      change P.ordinaryCoefficient g q.1 q.2.1 q.2.2 k*d.selector q.1 q.2.1 k (u z)*
        P.physicalPacket 0 q.1 q.2.1 q.2.2 k z=0
      rw [hc]
      simp only [WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    refine ⟨?_,?_⟩
    · simpa only [heval] using (integrableOn_zero : IntegrableOn (fun _ : ℝ×ℝ => (0:EuclideanSpace ℂ κ)) E (volume.prod volume))
    · simp only [heval,norm_zero,integral_zero]
      positivity
  · by_cases harea : (volume.prod volume).real E=0
    · have hm : (volume.prod volume) E=0 := (measureReal_eq_zero_iff hEfin).mp harea
      have hr : (volume.prod volume).restrict E=0 := Measure.restrict_eq_zero.mpr hm
      simp [IntegrableOn,hr,harea]
    · have henergyPos : 0<(∫ z, ‖g z‖^2 ∂volume.prod volume) :=
        lt_of_le_of_ne (integral_nonneg (fun z => sq_nonneg ‖g z‖)) (Ne.symm henergy)
      have hareaPos : 0<(volume.prod volume).real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm harea)
      have hdenU (q : P.PacketIndex) : P.ordinaryDensity 0 d.cell d.grid d.w d.tau E u q≤U :=
        ((P.densityTile 0 d.cell q).density_le P.topLength d.w P.width d.tau d.grid E u).trans
          (le_max_right _ _)
      have h := hModel g hg hgm hgb (Real.sqrt (∫ z, ‖g z‖^2 ∂volume.prod volume))
        (Real.sqrt_pos.mpr henergyPos) (Real.sq_sqrt henergyPos.le) E hE hEfin hareaPos
        u hu U (zero_lt_one.trans_le hU) le_rfl (fun q _ => hdenU q)
      rw [Real.sq_sqrt henergyPos.le] at h
      have hFpos : 0<(volume.prod volume).real F := henergyPos.trans_le henergyBound
      have hratio : ((volume.prod volume).real E)/((volume.prod volume).real F)≤
          ((volume.prod volume).real E)/(∫ z, ‖g z‖^2 ∂volume.prod volume) :=
        div_le_div_of_nonneg_left hareaPos.le henergyPos henergyBound
      have hp := Real.rpow_le_rpow_of_nonpos (div_pos hareaPos hFpos) hratio
        (by norm_num : -(1/20:ℝ)≤0)
      refine ⟨h.1,h.2.trans ?_⟩
      calc
        _ ≤ C*((volume.prod volume).real E)*
            (((volume.prod volume).real E)/((volume.prod volume).real F))^(-(1/20:ℝ)) :=
          mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le hareaPos.le)
        _ = _ := by
          rw [mul_assoc,reverse_disparity_identity hareaPos hFpos]
          ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataUniformCrossReverse
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reverse-disparity control of the distinct-profile form.
All constants are chosen before the finite translated lattice. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_uniform_cross_reverse_disparity (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (bound : ℝ), 1≤bound → P.profileBound≤bound → P.referenceEnvelopeConstant≤bound →
    ∀
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width)  ,
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ),
      Measurable f → (∀ z, ‖f z‖≤1) → Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (F E : Set (ℝ×ℝ)), MeasurableSet F → (volume.prod volume) F≠∞ →
      MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉F → f z=0) → (∀ z, z∉E → g z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      Integrable (fun z => inner ℂ
        (∑ q∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z q)
        (f z) ∂volume.prod volume‖≤
        (d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4)*
          Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_reverse_disparity hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅
    bound hb hprofile habsolute alt hAlt hSpectrum hMargin hBin
    f g hfm hf1 hgm hg1 F E hF hFfin hE hEfin hfs hgs u hu
  have hf := (bounded_supported_input f hfm hf1 F hF hFfin hfs).1
  have hg := (bounded_supported_input g hgm hg1 E hE hEfin hgs).1
  let weight := Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
    ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ)
  have hw : 0≤weight := by dsimp only [weight]; positivity
  let C := d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4
  have h := P.cross_pairing_bound alt hAlt initial d.selector d.measurable d.bounded
    u hu g f hgm hg1 hf (C*weight) (by
    intro c hc
    let Q := P.polarize alt hAlt c hc
    let dp := d.polarize alt hAlt c hc hSpectrum hMargin hBin
    have hrev := hAll N κ Label Item Q initial dp heq₁ heq₂ heq₃ heq₄ heq₅
      f hfm hf1 F hF hFfin hfs E hE hEfin u hu
    have hcost : dp.reverseModelCost CD CS CT CZ ordinaryDensityUpper≤C := by
      have hprofileQ : Q.profileBound≤2*bound :=
        mul_le_mul_of_nonneg_left hprofile (by norm_num)
      have habsoluteEq : Q.referenceEnvelopeConstant=2*P.referenceEnvelopeConstant := by
        dsimp only [Q,polarize,referenceEnvelopeConstant]
        ring
      have habsoluteQ : Q.referenceEnvelopeConstant≤2*bound := by
        rw [habsoluteEq]
        exact mul_le_mul_of_nonneg_left habsolute (by norm_num)
      exact dp.reverseModelCost_le_quartic CD CS CT CZ ordinaryDensityUpper (2*bound)
        hCS.le hCZ.le (by linarith) hprofileQ habsoluteQ
    have hselector : dp.selector=d.selector := rfl
    have hi : IntegrableOn (Q.ordinaryForwardSum initial d.selector u f) E (volume.prod volume) := hrev.1
    have hp := (Q.ordinary_adjoint_pairing_bound initial d.selector d.measurable d.bounded
      u hu f g hf hg hgm hg1 E hE hgs hi).2
    apply hp.trans
    calc
      _ ≤ dp.reverseModelCost CD CS CT CZ ordinaryDensityUpper*weight := by
        simpa only [weight,ordinaryForwardSum,hselector,mul_assoc] using hrev.2
      _ ≤ C*weight := mul_le_mul_of_nonneg_right hcost hw)
  refine ⟨h.1,?_⟩
  simpa only [C,weight,mul_assoc] using h.2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataIntrinsicReverse
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reverse disparity with the intrinsic profile budget. The auxiliary
jet parameters are reset before the estimate, and the literal physical
form is transported back unchanged. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_intrinsic_cross_reverse_disparity (hL : LepingleInput)
    (cStar cEta CEta cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 < cb) (hcbQuarter : cb≤1/4)
    (hspectral : cStar < cEta*cb) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb → d.Cv=Cv →
    ∀ (bound : ℝ), 1≤bound → (2^P.order*P.profileBound)*3^(2*P.order)≤bound →
    ∀
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (_hSpectrum : ∀ j l a k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et|≤d.cStar/P.length j ∧ d.cEta≤d.w*et ∧ d.w*et≤d.CEta)
    (_hMargin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        Set.Icc (-xi/et-d.margin*(d.w/P.length q.1)) (-xi/et+d.margin*(d.w/P.length q.1))⊆
          scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1))
    (_hBin : ∀ q∈initial, ∀ k xi et,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,et)≠0 →
        |et-P.frequency k|≤d.Cv/P.width)  ,
    ∀ (f g : ℝ×ℝ → EuclideanSpace ℂ κ),
      Measurable f → (∀ z, ‖f z‖≤1) → Measurable g → (∀ z, ‖g z‖≤1) →
    ∀ (F E : Set (ℝ×ℝ)), MeasurableSet F → (volume.prod volume) F≠∞ →
      MeasurableSet E → (volume.prod volume) E≠∞ →
      (∀ z, z∉F → f z=0) → (∀ z, z∉E → g z=0) →
    ∀ (u : ℝ×ℝ → ℝ), Measurable u →
      Integrable (fun z => inner ℂ
        (∑ q∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z q) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z q)
        (f z) ∂volume.prod volume‖≤
        (d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4)*
          Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ) := by
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hAll⟩ := exists_uniform_cross_reverse_disparity hL
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hspectral
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄ heq₅ bound hb hbudget
    alt hAlt hSpectrum hMargin hBin f g hfm hf1 hgm hg1 F E hF hFfin hE hEfin hfs hgs u hu
  let Q := P.withJetControl 0 1 (by norm_num) (by simp)
  let dq := d.withJetControl 0 1 (by norm_num) (by simp)
  have hprofile : Q.profileBound≤bound := by
    change P.profileBound≤bound
    have h₂ : (1:ℝ)≤2^P.order := one_le_pow₀ (by norm_num)
    have h₃ : (1:ℝ)≤3^(2*P.order) := one_le_pow₀ (by norm_num)
    apply le_trans _ hbudget
    calc
      _ ≤ 2^P.order*P.profileBound := le_mul_of_one_le_left P.profileBound_pos.le h₂
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg (pow_nonneg (by norm_num) _) P.profileBound_pos.le) h₃
  have habsolute : Q.referenceEnvelopeConstant≤bound := by
    simpa only [Q,referenceEnvelopeConstant,PacketLatticeData.withJetControl,one_pow,mul_one] using hbudget
  have h := hAll N κ Label Item Q initial dq heq₁ heq₂ heq₃ heq₄ heq₅ bound hb
    hprofile habsolute alt hAlt hSpectrum hMargin hBin f g hfm hf1 hgm hg1
    F E hF hFfin hE hEfin hfs hgs u hu
  have he (z : ℝ×ℝ) :
      inner ℂ (∑ a∈initial, Q.crossPacketValue alt hAlt 0 d.selector u g z a) (f z)=
      inner ℂ (∑ a∈initial, P.crossPacketValue alt hAlt 0 d.selector u g z a) (f z) := by
    exact congrArg (fun v => inner ℂ v (f z)) (Finset.sum_congr rfl (fun a _ =>
      P.withJetControl_crossPacketValue 0 1 (by norm_num) (by simp)
        alt hAlt 0 d.selector u g z a))
  change Integrable (fun z => inner ℂ
      (∑ a∈initial, Q.crossPacketValue alt hAlt 0 d.selector u g z a) (f z))
      (volume.prod volume) ∧
    ‖∫ z, inner ℂ (∑ a∈initial, Q.crossPacketValue alt hAlt 0 d.selector u g z a)
      (f z) ∂volume.prod volume‖≤
      (d.unitReverseModelCost CD CS CT CZ ordinaryDensityUpper*(2*bound)^4)*
        Real.sqrt ((volume.prod volume).real F*(volume.prod volume).real E)*
        ((volume.prod volume).real E/(volume.prod volume).real F)^(9/20:ℝ) at h
  simpa only [he] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularPartition
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction after the three-grid split. The selector for
each piece agrees with the original one on every retained packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem sum_angularPackets (P : PacketLatticeData N κ Label Item)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    {E : Type*} [AddCommMonoid E] (f : P.PacketIndex → E) :
    (∑ g : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag g, f a)=
      ∑ a∈initial, f a := by
  simp only [angularPackets,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem crossPacketValue_congr_selector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (t : ℝ) (b c : ∀ j, P.labels j → κ → ℝ → ℂ)
    (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) (a : P.PacketIndex)
    (h : ∀ k s, b a.1 a.2.1 k s=c a.1 a.2.1 k s) :
    P.crossPacketValue alt hAlt t b u g z a=P.crossPacketValue alt hAlt t c u g z a := by
  have he : b a.1 a.2.1=c a.1 a.2.1 := funext (fun k => funext (h k))
  simp only [crossPacketValue,physicalMultiplierCoefficient,he]

theorem crossPacketValue_angularSelector (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (grid : DyadicLineGrid.GridChoice) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (t : ℝ) (u : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (z : ℝ×ℝ) (a : P.PacketIndex) (ha : a∈P.angularPackets initial tag grid) :
    P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a=
      P.crossPacketValue alt hAlt t b u g z a := by
  apply P.crossPacketValue_congr_selector alt hAlt t _ _ u g z a
  intro k s
  simp only [angularSelector,(Finset.mem_filter.mp ha).2,ite_true, if_true]

theorem sum_crossPacketValue_angularPartition (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (initial : Finset P.PacketIndex) (tag : ∀ j, P.labels j → DyadicLineGrid.GridChoice)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (t : ℝ) (u : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
      P.crossPacketValue alt hAlt t (P.angularSelector tag grid b) u g z a)=
      ∑ a∈initial, P.crossPacketValue alt hAlt t b u g z a := by
  calc
    _ = ∑ grid : DyadicLineGrid.GridChoice, ∑ a∈P.angularPackets initial tag grid,
        P.crossPacketValue alt hAlt t b u g z a := by
      apply Finset.sum_congr rfl
      intro grid _
      exact Finset.sum_congr rfl (fun a ha =>
        P.crossPacketValue_angularSelector alt hAlt initial tag grid b t u g z a ha)
    _ = _ := P.sum_angularPackets initial tag _

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PacketAngularReversePairing
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct and recombine the three angular models for the reverse
estimate. The fixed cost is independent of all finite packet data. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem exists_angular_reverse_pairing_oai (hVariation : LepingleInput)
    (cStar cEta CEta cb Cv radius : ℝ) (M : ℕ)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0≤CEta) (hCv : 0≤Cv)
    (hcb : 0 < cb) (hcbQuarter : cb≤1/4) (hsmall : cStar/cEta < cb/4) (hr : 0 ≤ radius)
    (hcoverSmall : 6*max radius (cStar/cEta+cb)<1)
    (num : OrdinaryModelNumerics cStar cEta cb radius) :
    ∃ CD CS CT CZ : ℝ, 0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CZ ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (S : Finset P.PacketIndex),
    ∀ w F : ℝ, 0<w → w≤P.width → 0≤F → 207≤P.order →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et, planarAngularFourier (P.physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound),
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |xi+P.rowSlope j l*et| ≤ cStar/P.length j ∧ cEta≤w*et ∧ w*et≤CEta) →
      (∀ j l a k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 j l a k) (xi,et)≠0 →
        |et-P.frequency k|≤Cv/P.width) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖≤1) →
      (∀ j l k s, b j l k s≠0 → cb*w/P.length j≤|P.rowSlope j l-s|) →
      (∀ j l k s, b j l k s≠0 → |s-P.rowSlope j l| ≤ radius*(w/P.length j)) →
      (∀ j l k s t, |s-t|≤w/P.length j → ‖b j l k s-b j l k t‖≤|s-t|/(w/P.length j)) →
    ∀ bound : ℝ, 1≤bound → (2^P.order*P.profileBound)*3^(2*P.order)≤bound →
    ∀ (g f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → Measurable f →
      (∀ z, ‖g z‖≤1) → (∀ z, ‖f z‖≤1) →
    ∀ E Fset : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet Fset →
      (volume.prod volume) E≠∞ → (volume.prod volume) Fset≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉Fset → f z=0) →
    ∀ u : ℝ×ℝ → ℝ, Measurable u →
      Integrable (fun z => inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z))
        (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z)
        ∂volume.prod volume‖≤3*((num.reverseUnitCost M CD CS CT CZ*(2*bound)^4)*
          Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
          ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)) := by
  have hsep : cStar < cEta*cb := by
    have h : cStar/cEta < cb := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hcEta).mp h
  obtain ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,hreverse⟩ := exists_intrinsic_cross_reverse_disparity hVariation
    cStar cEta CEta cb Cv hcStar hcEta hCEta hCv hcb hcbQuarter hsep
  refine ⟨CD,CS,CT,CZ,hCD,hCS,hCT,hCZ,?_⟩
  intro N κ Label Item _ _ P S w F hw hW hF horder hfreq hlocal spectrum bin
    alt hAlt altSpectrum altBin b hb hb1 haway hradius hnear bound hbound hprofile
    g f hgm hfm hgb hfb E Fset hE hFset hEfin hFfin hgs hfs u hu
  classical
  obtain ⟨tag,cell,hcover⟩ := P.exists_angular_assignment w cStar cEta cb radius
    hw hcStar hcEta hcb.le hr hcoverSmall
  let d := fun gamma => angularModelConfig P S cStar cEta CEta cb Cv w F radius M
    hcStar hcEta hCEta hCv hcb hcbQuarter hsmall num hw hW hF hr horder hfreq hlocal
    tag cell hcover spectrum bin b hb hb1 haway hradius hnear gamma
  let V := fun (gamma : DyadicLineGrid.GridChoice) (z : ℝ×ℝ) =>
    ∑ a∈P.angularPackets S tag gamma,
      P.crossPacketValue alt hAlt 0 (P.angularSelector tag gamma b) u g z a
  let B := (num.reverseUnitCost M CD CS CT CZ*(2*bound)^4)*
    Real.sqrt ((volume.prod volume).real Fset*(volume.prod volume).real E)*
    ((volume.prod volume).real E/(volume.prod volume).real Fset)^(9/20:ℝ)
  have hpiece (gamma : DyadicLineGrid.GridChoice) :
      Integrable (fun z => inner ℂ (V gamma z) (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (V gamma z) (f z) ∂volume.prod volume‖≤B := by
    have hMargin : ∀ a∈P.angularPackets S tag gamma, ∀ k xi et,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket 0 a.1 a.2.1 a.2.2 k) (xi,et)≠0 →
        Icc (-xi/et-cb*(w/P.length a.1)) (-xi/et+cb*(w/P.length a.1))⊆
          scaledAngularCell (w/P.topLength) gamma.val a.1.val (cell a.1 a.2.1) := by
      intro a ha k xi et hs
      have heq := (Finset.mem_filter.mp ha).2
      have hspec := altSpectrum a.1 a.2.1 a.2.2 k xi et hs
      simpa only [heq] using (hcover a.1 a.2.1).2 xi et hspec.2.1 hspec.1
    have h := hreverse N κ Label Item P (P.angularPackets S tag gamma) (d gamma)
      rfl rfl rfl rfl rfl bound hbound hprofile alt hAlt altSpectrum hMargin
      (fun a _ k xi et hs => altBin a.1 a.2.1 a.2.2 k xi et hs)
      f g hfm hfb hgm hgb Fset E hFset hFfin hE hEfin hfs hgs u hu
    rw [OrdinaryModelConfig.unitReverseModelCost_of_numeric_fields (d gamma) cStar cEta cb radius
      num M CD CS CT CZ rfl rfl rfl rfl rfl rfl rfl rfl rfl] at h
    exact h
  have hsum (z : ℝ×ℝ) : inner ℂ (∑ gamma, V gamma z) (f z)=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z) :=
    congrArg (fun v => inner ℂ v (f z)) (P.sum_crossPacketValue_angularPartition alt hAlt S tag b 0 u g z)
  have hsint : Integrable (fun z => ∑ gamma, inner ℂ (V gamma z) (f z)) (volume.prod volume) :=
    integrable_finsetSum _ (fun gamma _ => (hpiece gamma).1)
  have heq (z : ℝ×ℝ) : (∑ gamma, inner ℂ (V gamma z) (f z))=
      inner ℂ (∑ a∈S, P.crossPacketValue alt hAlt 0 b u g z a) (f z) := by
    rw [←sum_inner]; exact hsum z
  refine ⟨hsint.congr (Filter.Eventually.of_forall heq),?_⟩
  rw [←integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_finsetSum _ (fun gamma _ => (hpiece gamma).1)]
  calc
    _ ≤ ∑ gamma : DyadicLineGrid.GridChoice,
        ‖∫ z, inner ℂ (V gamma z) (f z) ∂volume.prod volume‖ := norm_sum_le _ _
    _ ≤ ∑ _gamma : DyadicLineGrid.GridChoice, B :=
      Finset.sum_le_sum (fun gamma _ => (hpiece gamma).2)
    _ = 3*B := by simp only [Finset.sum_const,Finset.card_univ,DyadicLineGrid.gridChoice_card,nsmul_eq_mul,Nat.cast_ofNat]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing_oai := @OAI.LipschitzHilbert.PacketLatticeData.exists_angular_reverse_pairing_oai
