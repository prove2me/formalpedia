-- Prove2me | solution 1 for OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:30:57.703976+00:00
-- url     : https://prove2.me/submissions/0ca967df-7dbd-4857-860a-8b1550cb66f3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_exists_supported_transverse_tree_maximal

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxPolynomialWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial localization lower bound on a reference interval, with
the horizontal box offset retained explicitly. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base (u r k x : ℝ) (hr : 0 < r) (hx : |x - u| ≤ r) :
    (1 + |k|) ^ 2 / 8 ≤ 1 + (x - (u + r * k)) ^ 2 / r ^ 2 := by
  let v := (x - (u + r * k)) / r
  have hunit : |(x - u) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hx
  have heq : k = (x - u) / r - v := by
    dsimp [v]
    field_simp
    ring
  have hk : |k| ≤ 1 + |v| := by
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hunit le_rfl)
  have hk2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |k|)
    (add_le_add (le_rfl : (1 : ℝ) ≤ 1) hk) 2
  have habs : |v| ^ 2 = v ^ 2 := sq_abs v
  have hs := sq_nonneg (|v| - 2)
  have hv : 1 + (x - (u + r * k)) ^ 2 / r ^ 2 = 1 + v ^ 2 := by
    dsimp [v]
    rw [div_pow]
  rw [hv]
  nlinarith

theorem box_polynomial_weight (u r k x : ℝ) (q : ℕ)
    (hr : 0 < r) (hx : |x - u| ≤ r) :
    ((1 + |k|) ^ 2 / 8) ^ q ≤ polynomialWeight (u + r * k) r q x := by
  exact pow_le_pow_left₀ (by positivity) (box_polynomial_base u r k x hr hx) q

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

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalOscillation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual maxima of subinterval sums on residual segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem intervalOscillation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) : 0 ≤ intervalOscillation F N a b := by
  classical
  apply Finset.le_sup'_of_le (b := ((0 : Fin (N + 1)), (0 : Fin (N + 1))))
    (f := fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ _)
  split_ifs <;> positivity

theorem exists_intervalOscillation_eq {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) :
    ∃ c d : ℕ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ intervalOscillation F N a b = ‖F d - F c‖ := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0)
  change intervalOscillation F N a b = _ at hq
  by_cases h : a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b
  · rw [ite_eq_left h] at hq
    exact ⟨q.1, q.2, h.1, h.2.1, h.2.2, hq⟩
  · rw [ite_eq_right h] at hq
    exact ⟨a, a, le_rfl, le_rfl, hab, by simpa only [sub_self, norm_zero] using hq⟩

theorem increment_le_intervalOscillation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ N) :
    ‖F d - F c‖ ≤ intervalOscillation F N a b := by
  classical
  let q : Fin (N + 1) × Fin (N + 1) :=
    (⟨c, by omega⟩, ⟨d, by omega⟩)
  have h := Finset.le_sup'
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ q)
  simpa only [intervalOscillation, q,
    ite_eq_left (show a ≤ c ∧ c ≤ d ∧ d ≤ b from ⟨hac, hcd, hdb⟩)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleLocalMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

omit [IsFiniteMeasure μ] in
theorem martingale_abs (hF : Martingale F ℱ μ) :
    Submartingale (fun i x => |F i x|) ℱ μ := by
  have heq : (fun i x => |F i x|) = F ⊔ -F := by
    funext i x
    exact abs_eq_max_neg
  rw [heq]
  exact hF.submartingale.sup hF.neg.submartingale

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaximalL2Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The p=2 maximal energy argument. A localized weak-L1 estimate,
layer cake, and Cauchy--Schwarz give the strong L2 constant four. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem maximal_square_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H g : Ω → ℝ) (hH : Measurable H) (hg : Measurable g)
    (hH0 : ∀ x, 0 ≤ H x) (hg0 : ∀ x, 0 ≤ g x)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t*μ {x | t ≤ H x} ≤
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal ((H x)^2) ∂μ) ≤
      2 * ∫⁻ x, ENNReal.ofReal (g x*H x) ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hν (t : ℝ) : ν {x | t ≤ H x} =
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ :=
    withDensity_apply _ (measurableSet_le measurable_const hH)
  have hpow := lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall hH0) hH.aemeasurable (by norm_num : (0:ℝ)<2)
  simp only [Real.rpow_two, show (2:ℝ)-1=1 by norm_num, Real.rpow_one,
    ENNReal.ofReal_ofNat] at hpow
  rw [hpow]
  apply mul_le_mul' le_rfl
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ν {x | t ≤ H x} := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      rw [hν, mul_comm]
      exact hweak t ht
    _ = ∫⁻ x, ENNReal.ofReal (H x) ∂ν :=
      (lintegral_eq_lintegral_meas_le ν (Filter.Eventually.of_forall hH0) hH.aemeasurable).symm
    _ = _ := by
      rw [lintegral_withDensity_eq_lintegral_mul μ hg.ennreal_ofReal hH.ennreal_ofReal]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (hg0 x)).symm

theorem maximal_L2_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H g : Ω → ℝ) (hH : Measurable H) (hg : Measurable g)
    (hH0 : ∀ x, 0 ≤ H x) (hg0 : ∀ x, 0 ≤ g x)
    (hH2 : MemLp H 2 μ) (hg2 : MemLp g 2 μ)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t*μ {x | t ≤ H x} ≤
      ∫⁻ x in {x | t ≤ H x}, ENNReal.ofReal (g x) ∂μ) :
    (∫ x, (H x)^2 ∂μ) ≤ 4 * ∫ x, (g x)^2 ∂μ := by
  have hintH := hH2.integrable_sq
  have hintg := hg2.integrable_sq
  have hintprod : Integrable (fun x => g x*H x) μ := hg2.integrable_mul hH2
  have h := maximal_square_lintegral μ H g hH hg hH0 hg0 hweak
  rw [← ofReal_integral_eq_lintegral_ofReal hintH
    (Filter.Eventually.of_forall (fun x => sq_nonneg (H x))),
    ← ofReal_integral_eq_lintegral_ofReal hintprod
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hg0 x) (hH0 x)))] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg (H x))),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => mul_nonneg (hg0 x) (hH0 x)))] at hr
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall hg0)
    (Filter.Eventually.of_forall hH0) (by simpa using hg2) (by simpa using hH2)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hposH : 0 ≤ ∫ x, (H x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (H x))
  have hposg : 0 ≤ ∫ x, (g x)^2 ∂μ := integral_nonneg (fun x => sq_nonneg (g x))
  have hrootH := Real.sq_sqrt hposH
  have hrootg := Real.sq_sqrt hposg
  have hsquare := sq_nonneg (Real.sqrt (∫ x, (H x)^2 ∂μ) -
    2*Real.sqrt (∫ x, (g x)^2 ∂μ))
  nlinarith [Real.sqrt_nonneg (∫ x, (H x)^2 ∂μ), Real.sqrt_nonneg (∫ x, (g x)^2 ∂μ)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleMaximalL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Doob's scalar finite-horizon L2 estimate, with its exact factor four,
for the dyadic averages used in the axis-parallel rectangle count. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

theorem finiteMaxSignal_nonneg {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    0 ≤ finiteMaxSignal F N x := by
  exact (abs_nonneg (F 0 x)).trans (Finset.le_sup' (fun i => |F i x|) (by simp))

theorem finiteMaxSignal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i ≤ N, Measurable (F i)) :
    Measurable (finiteMaxSignal F N) :=
  Finset.measurable_range_sup'' (fun i hi => by
    simpa only [Real.norm_eq_abs] using (hF i hi).norm)

theorem finiteMaxSignal_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (N : ℕ) (hF : ∀ i, MemLp (F i) 2 μ) :
    MemLp (finiteMaxSignal F N) 2 μ := by
  induction N with
  | zero =>
    have heq : finiteMaxSignal F 0 = fun x => |F 0 x| := by
      funext x
      simp [finiteMaxSignal]
    rw [heq]
    simpa only [Real.norm_eq_abs] using (hF 0).norm
  | succ N ih =>
    have heq : finiteMaxSignal F (N+1) = (fun x => |F (N+1) x|) ⊔ finiteMaxSignal F N := by
      funext x
      have hh := Finset.sup'_insert (s := Finset.range (N+1)) (H := Finset.nonempty_range_add_one)
        (b := N+1) (f := fun i => |F i x|)
      simpa only [← Finset.range_add_one, finiteMaxSignal, Pi.sup_apply] using hh
    rw [heq]
    have hn : MemLp (fun x => |F (N+1) x|) 2 μ := by
      simpa only [Real.norm_eq_abs] using (hF (N+1)).norm
    exact hn.sup ih

theorem martingale_maximal_L2 {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m) (F : ℕ → Ω → ℝ)
    (hF : Martingale F ℱ μ) (hF2 : ∀ i, MemLp (F i) 2 μ) (N : ℕ) :
    (∫ x, (finiteMaxSignal F N x)^2 ∂μ) ≤ 4 * ∫ x, (F N x)^2 ∂μ := by
  have hm (i : ℕ) : Measurable (F i) := (hF.stronglyMeasurable i).measurable.le (ℱ.le i)
  have h := maximal_L2_energy μ (finiteMaxSignal F N) (fun x => |F N x|)
    (finiteMaxSignal_measurable F N (fun i _ => hm i)) (by simpa only [Real.norm_eq_abs] using (hm N).norm)
    (finiteMaxSignal_nonneg F N) (fun x => abs_nonneg (F N x))
    (finiteMaxSignal_memLp μ F N hF2) (by simpa only [Real.norm_eq_abs] using (hF2 N).norm) (by
      intro t ht
      let ε : ℝ≥0 := ⟨t,ht.le⟩
      have hw := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
        (ε := ε) N
      rw [← ofReal_integral_eq_lintegral_ofReal (hF.integrable N).abs.integrableOn
        (Filter.Eventually.of_forall (fun x => abs_nonneg (F N x)))]
      have hc : (ε : ℝ≥0∞) = ENNReal.ofReal t := ENNReal.coe_nnreal_eq ε
      rw [hc] at hw
      exact hw)
  simpa only [sq_abs] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PartitionIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing nonnegative cell estimates over a countable measurable partition. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]

/-- Summable control on partition cells proves global integrability as well
as the global estimate; no integrability of the left side is assumed. -/
theorem integral_le_of_partition (μ : Measure α) (s : ι → Set α)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) = Set.univ) (f g : α → ℝ) {C : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hgint : Integrable g μ)
    (hf : ∀ i, IntegrableOn f (s i) μ)
    (hbound : ∀ i, (∫ x in s i, f x ∂μ) ≤ C * ∫ x in s i, g x ∂μ) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ C * ∫ x, g x ∂μ := by
  have hgsum : Summable (fun i => ∫ x in s i, g x ∂μ) :=
    (hasSum_integral_iUnion hs hd hgint.integrableOn).summable
  have hfsum : Summable (fun i => ∫ x in s i, f x ∂μ) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg hf0) hbound (hgsum.mul_left C)
  have hnorm : Summable (fun i => ∫ x in s i, ‖f x‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hfsum
  have hfint := integrableOn_iUnion_of_summable_integral_norm hf hnorm
  rw [hcover, integrableOn_univ] at hfint
  have hfi := integral_iUnion hs hd hfint.integrableOn
  have hgi := integral_iUnion hs hd hgint.integrableOn
  rw [hcover, setIntegral_univ] at hfi hgi
  refine ⟨hfint, ?_⟩
  calc
    (∫ x, f x ∂μ) = ∑' i, ∫ x in s i, f x ∂μ := hfi
    _ ≤ ∑' i, C * ∫ x in s i, g x ∂μ := hfsum.tsum_le_tsum hbound (hgsum.mul_left C)
    _ = C * ∑' i, ∫ x in s i, g x ∂μ := tsum_mul_left
    _ = C * ∫ x, g x ∂μ := congrArg (C * ·) hgi.symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PlanarSliceFourierAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript uses angular frequencies in `exp(iηy)`, whereas
mathlib's Fourier transform uses `exp(-2πi xξ)`. These definitions and
identities keep the conversion explicit. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem planarAngularFourier_eq_integral (f : ℝ × ℝ → ℂ) (frequency : ℝ × ℝ) :
    planarAngularFourier f frequency = ∫ z : ℝ × ℝ,
      Complex.exp (-(Complex.I * (z.1 * frequency.1 + z.2 * frequency.2))) * f z
        ∂volume.prod volume := by
  unfold planarAngularFourier planarFourier
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopping-level bands are intervals of the original source length
index. This is the bridge from interval concentration to summation by
parts over angular stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem length_antitone (P : SourceLabeledLattice N κ Label Item) : Antitone P.length := by
  intro i j hij
  unfold length
  exact div_le_div_of_nonneg_left P.topLength_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

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

/-- The covering cell has length at most six times the interval length. -/
theorem exists_comparable_three_grid_cover (c r : ℝ) (hr : 0 < r) :
    ∃ q∈Finset.Icc (-1) 1, ∃ k j : ℤ,
      Icc (c-r) (c+r)⊆cell q k j ∧ scale k≤12*r := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0<12*r by positivity) (by norm_num : (1:ℝ)<2)
  change scale k≤12*r at hlo
  change 12*r < scale (k+1) at hhi
  rw [scale_succ] at hhi
  obtain ⟨q,hq,j,hcell⟩ := exists_three_grid_cover k c r hr.le (by linarith)
  exact ⟨q,hq,k,j,hcell,hlo⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horizontal Whitney cells for the ordinary tree estimate. An allowed
cell has no tile of shorter length whose center meets its triple. A
maximal allowed cell obtains its concrete witness from its parent. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
attribute [local instance] Classical.propDecidable

theorem center_parent_bound (k j : ℤ) :
    |center k j-center (k+1) (parent 0 k j)| ≤ scale k/2 := by
  have hlo : 2*(j/2) ≤ j := by omega
  have hhi : j ≤ 2*(j/2)+1 := by omega
  have hlo' : (2:ℝ)*(j/2:ℤ) ≤ j := by exact_mod_cast hlo
  have hhi' : (j:ℝ) ≤ 2*(j/2:ℤ)+1 := by exact_mod_cast hhi
  have hs := scale_pos k
  have hl := mul_le_mul_of_nonneg_left hlo' hs.le
  have hh := mul_le_mul_of_nonneg_left hhi' hs.le
  simp only [center,left,parent,shift,Int.mul_zero,Int.cast_zero,zero_div,add_zero,scale_succ]
  apply abs_le.mpr
  constructor <;> nlinarith only [hl,hh,hs]

theorem allowed_of_parent {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (k j : ℤ) (h : Allowed tiles x ell (k+1) (parent 0 k j)) :
    Allowed tiles x ell k j := by
  intro i hi hlen
  have hs := scale_pos k
  have hlen' : ell i ≤ scale (k+1) := by rw [scale_succ]; linarith only [hlen,hs]
  have hp := h i hi hlen'
  have hd := center_parent_bound k j
  have ht := abs_sub_le (x i) (center k j) (center (k+1) (parent 0 k j))
  rw [scale_succ] at hp
  linarith only [hp,hd,ht,hs]

theorem parent_witness {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k j : ℤ} (h : Whitney tiles x ell k j) :
    ∃ i ∈ tiles, ell i ≤ 2*scale k ∧
      ∀ z ∈ cell 0 k j, |x i-z| ≤ 4*scale k := by
  have hn := h.2
  simp only [Allowed,not_forall,not_lt] at hn
  obtain ⟨i,hi,hlen,hnear⟩ := hn
  refine ⟨i,hi,by simpa only [scale_succ] using hlen,?_⟩
  intro z hz
  have hd := point_center_bound (k+1) (parent 0 k j) (cell_subset_parent 0 k j hz)
  rw [scale_succ] at hd hnear
  have ht := abs_sub_le (x i) (center (k+1) (parent 0 k j)) z
  rw [abs_sub_comm (center (k+1) (parent 0 k j)) z] at ht
  linarith only [ht,hd,hnear]

/-- The index of a point at the next scale is exactly its parent index. -/
theorem parent_index (k : ℤ) (z : ℝ) :
    parent 0 k (index 0 k z) = index 0 (k+1) z :=
  (index_eq_of_mem (cell_subset_parent 0 k (index 0 k z)
    (mem_index_cell 0 k z))).symm

/-- Being allowed passes from a larger cell to every smaller cell it meets. -/
theorem allowed_at_point_mono {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k l : ℤ} (hkl : k ≤ l) (z : ℝ)
    (h : Allowed tiles x ell l (index 0 l z)) :
    Allowed tiles x ell k (index 0 k z) := by
  obtain ⟨n,rfl⟩ := Int.le.dest hkl
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero] using h
  | succ n ih =>
    apply ih (by omega)
    apply allowed_of_parent tiles x ell (k+n) (index 0 (k+n) z)
    simpa only [parent_index,Nat.cast_add,Nat.cast_one,add_assoc] using h

/-- Distinct maximal allowed cells are disjoint at all scales. -/
theorem whitney_disjoint {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k l i j : ℤ} (hi : Whitney tiles x ell k i)
    (hj : Whitney tiles x ell l j) (hne : (k,i) ≠ (l,j)) :
    Disjoint (cell 0 k i) (cell 0 l j) := by
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hei := index_eq_of_mem hzi
  have hej := index_eq_of_mem hzj
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · apply hi.2
    have hp := cell_subset_parent 0 k i hzi
    have he := index_eq_of_mem hp
    rw [← he]
    apply allowed_at_point_mono tiles x ell (by omega : k+1 ≤ l) z
    simpa only [hej] using hj.1
  · subst l
    exact hne (by simp [hei.symm.trans hej])
  · apply hj.2
    have hp := cell_subset_parent 0 l j hzj
    have he := index_eq_of_mem hp
    rw [← he]
    apply allowed_at_point_mono tiles x ell (by omega : l+1 ≤ k) z
    simpa only [hei] using hi.1

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceWhitneyPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative packing of the actual Whitney intervals used in the
ordinary tree estimate. Bounds are on arbitrary finite subfamilies and
therefore also support subsequent monotone summation. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

/-- A parent witness locates the entire Whitney cell near the horizontal top. -/
theorem cell_subset_top_enlargement {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ}
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2) {k j : ℤ}
    (h : Whitney tiles x ell k j) :
    cell 0 k j ⊆ Icc (c-(4*scale k+L/2)) (c+(4*scale k+L/2)) := by
  obtain ⟨i,hi,_,hw⟩ := parent_witness tiles x ell h
  intro z hz
  have hbound : |z-c| ≤ 4*scale k+L/2 := by
    have ht := abs_sub_le z (x i) c
    rw [abs_sub_comm z (x i)] at ht
    linarith only [ht,hw z hz,hcenters i hi]
  exact ⟨by linarith [(abs_le.mp hbound).1],by linarith [(abs_le.mp hbound).2]⟩

/-- A finite subfamily with lengths at most `r` has total length at most
`8r+L`, where the tile centers lie in an interval of length `L`. -/
theorem finite_length_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2)
    (S : Finset (ℤ×ℤ))
    (hW : ∀ p ∈ S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p ∈ S, scale p.1 ≤ r) :
    ∑ p ∈ S, scale p.1 ≤ 8*r+L := by
  have hsub (p) (hp : p ∈ S) :
      cell 0 p.1 p.2 ⊆ Icc (c-(4*r+L/2)) (c+(4*r+L/2)) := by
    intro z hz
    have hc := cell_subset_top_enlargement tiles x ell hcenters (hW p hp) hz
    have hs := hscale p hp
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hdisj : Set.PairwiseDisjoint (S : Set (ℤ×ℤ)) (fun p => cell 0 p.1 p.2) := by
    intro p hp q hq hpq
    exact whitney_disjoint tiles x ell (hW p hp) (hW q hq) (by simpa using hpq)
  calc
    ∑ p ∈ S, scale p.1 = ∑ p ∈ S, volume.real (cell 0 p.1 p.2) := by
      simp only [cell_length]
    _ = volume.real (⋃ p ∈ S, cell 0 p.1 p.2) :=
      (measureReal_biUnion_finset hdisj (fun p _ => cell_measurable 0 p.1 p.2)
        (fun _ _ => measure_Ico_lt_top.ne)).symm
    _ ≤ volume.real (Icc (c-(4*r+L/2)) (c+(4*r+L/2))) := by
      apply measureReal_mono _ measure_Icc_lt_top.ne
      intro z hz
      obtain ⟨p,hp,hz⟩ := mem_iUnion₂.mp hz
      exact hsub p hp hz
    _ = 8*r+L := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- The small Whitney cells have a summable total length controlled by
the top length. -/
theorem small_length_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0 ≤ L)
    (hcenters : ∀ i ∈ tiles, |x i-c| ≤ L/2)
    (S : Finset (ℤ×ℤ))
    (hW : ∀ p ∈ S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p ∈ S, scale p.1 ≤ L) :
    ∑ p ∈ S, scale p.1 ≤ 9*L := by
  have h := finite_length_budget tiles x ell hL hL hcenters S hW hscale
  linarith only [h]

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual integer-indexed dyadic line averages. The alternating grids are
handled directly, with no alignment premise between a packet and a root. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

theorem lineAverage_martingale (q top j : ℤ) (f : ℝ → ℝ) :
    Martingale (lineAverage q top j f) (lineFiltration q top) (rootMeasure q top j) :=
  martingale_condExp f _ _

theorem lineAverage_memLp (q top j : ℤ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) (n : ℕ) :
    MemLp (lineAverage q top j f n) 2 (rootMeasure q top j) := hf.condExp (by norm_num)

theorem lineAverage_constant (q top j : ℤ) (f : ℝ → ℝ) (n : ℕ) {x y : ℝ}
    (hxy : index q (top-(n:ℤ)) x=index q (top-(n:ℤ)) y) :
    lineAverage q top j f n x=lineAverage q top j f n y :=
  (show StronglyMeasurable[lineFiltration q top n] (lineAverage q top j f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Each conditional expectation equals the literal average on the
actual dyadic cell containing the point. -/
theorem lineAverage_eq_cell_mean (q top j : ℤ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) (n : ℕ) {x : ℝ}
    (hx : x∈cell q top j) :
    lineAverage q top j f n x =
      (∫ y in cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x), f y)/scale (top-(n:ℤ)) := by
  let s := cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x)
  have hsub : s⊆cell q top j := cell_subset_of_intersect (by omega)
    ⟨x,mem_index_cell q (top-(n:ℤ)) x,hx⟩
  have hs : MeasurableSet[lineFiltration q top n] s := by
    change MeasurableSet[lineFiltration q top n] (cell q (top-(n:ℤ)) (index q (top-(n:ℤ)) x))
    rw [←index_fiber]
    exact (comap_measurable (index q (top-(n:ℤ)))) (measurableSet_singleton _)
  have hs' : MeasurableSet s := cell_measurable _ _ _
  have hmass : (rootMeasure q top j).real s=scale (top-(n:ℤ)) := by
    rw [measureReal_def,rootMeasure,Measure.restrict_apply hs',inter_eq_left.mpr hsub]
    exact cell_length q (top-(n:ℤ)) (index q (top-(n:ℤ)) x)
  apply (eq_div_iff (scale_pos (top-(n:ℤ))).ne').mpr
  calc
    lineAverage q top j f n x*scale (top-(n:ℤ)) =
        ∫ y in s, lineAverage q top j f n x ∂rootMeasure q top j := by
      rw [setIntegral_const,smul_eq_mul,hmass,mul_comm]
    _ = ∫ y in s, lineAverage q top j f n y ∂rootMeasure q top j := by
      apply setIntegral_congr_fun hs'
      intro y hy
      exact lineAverage_constant q top j f n (index_eq_of_mem hy).symm
    _ = ∫ y in s, f y ∂rootMeasure q top j := setIntegral_condExp ((lineFiltration q top).le n) hf hs
    _ = ∫ y in s, f y := by
      rw [rootMeasure,Measure.restrict_restrict hs',inter_eq_left.mpr hsub]

/-- Doob's bound on a root has a constant independent of the root, grid,
and number of retained scales. -/
theorem lineAverage_maximal_energy (q top j : ℤ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) (N : ℕ) :
    (∫ x, (finiteMaxSignal (lineAverage q top j f) N x)^2 ∂rootMeasure q top j) ≤
      4*∫ x, (f x)^2 ∂rootMeasure q top j := by
  have hmax := martingale_maximal_L2 (rootMeasure q top j) (lineFiltration q top)
    (lineAverage q top j f) (lineAverage_martingale q top j f)
    (fun n => lineAverage_memLp q top j hf n) N
  have hnorm : Integrable (fun x => ‖f x‖^(2:ℝ)) (rootMeasure q top j) := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hf.integrable_sq
  have hcond := integral_norm_condExp_rpow_le (μ:=rootMeasure q top j)
    (m:=lineFiltration q top N) (p:=2) (by norm_num) hnorm
  have hcond' : (∫ x, (lineAverage q top j f N x)^2 ∂rootMeasure q top j) ≤
      ∫ x, (f x)^2 ∂rootMeasure q top j := by
    simpa only [lineAverage,Real.rpow_two,Real.norm_eq_abs,sq_abs] using hcond
  exact hmax.trans (mul_le_mul_of_nonneg_left hcond' (by norm_num))

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceGlobalDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform L² bound for actual dyadic cell averages on the whole line.
The root intervals are glued using their true measurable partition. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem cellMean_measurable (q k : ℤ) (f : ℝ → ℝ) : Measurable (cellMean q k f) :=
  (measurable_of_countable (fun i : ℤ => (∫ y in cell q k i, f y)/scale k)).comp (index_measurable q k)

theorem dyadicMaximal_measurable (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) :
    Measurable (dyadicMaximal q top N f) :=
  finiteMaxSignal_measurable _ _ (fun n _ => cellMean_measurable q (top-(n:ℤ)) f)

theorem dyadicMaximal_nonneg (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    0≤dyadicMaximal q top N f x := finiteMaxSignal_nonneg _ _ _

theorem dyadicMaximal_eq_on_root (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : Integrable f (rootMeasure q top j)) {x : ℝ} (hx : x∈cell q top j) :
    dyadicMaximal q top N f x=finiteMaxSignal (lineAverage q top j f) N x := by
  have heq : (fun n : ℕ => |cellMean q (top-(n:ℤ)) f x|) =
      (fun n : ℕ => |lineAverage q top j f n x|) := by
    funext n
    rw [lineAverage_eq_cell_mean q top j hf n hx]
    rfl
  exact congrArg (fun g : ℕ → ℝ => (Finset.range (N+1)).sup' Finset.nonempty_range_add_one g) heq

theorem dyadicMaximal_root_memLp (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) :
    MemLp (dyadicMaximal q top N f) 2 (rootMeasure q top j) := by
  have hm := finiteMaxSignal_memLp (rootMeasure q top j) (lineAverage q top j f) N
    (fun n => lineAverage_memLp q top j hf n)
  refine (memLp_congr_ae ?_).mp hm
  change ∀ᵐ x ∂volume.restrict (cell q top j), _
  filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
  exact (dyadicMaximal_eq_on_root q top j N (hf.integrable (by norm_num)) hx).symm

theorem dyadicMaximal_root_energy (q top j : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 (rootMeasure q top j)) :
    (∫ x, (dyadicMaximal q top N f x)^2 ∂rootMeasure q top j) ≤
      4*∫ x, (f x)^2 ∂rootMeasure q top j := by
  have heq : ∀ᵐ x ∂rootMeasure q top j,
      (dyadicMaximal q top N f x)^2=(finiteMaxSignal (lineAverage q top j f) N x)^2 := by
    change ∀ᵐ x ∂volume.restrict (cell q top j), _
    filter_upwards [ae_restrict_mem (cell_measurable q top j)] with x hx
    rw [dyadicMaximal_eq_on_root q top j N (hf.integrable (by norm_num)) hx]
  rw [integral_congr_ae heq]
  exact lineAverage_maximal_energy q top j hf N

/-- Actual finite dyadic maximal averages are L² bounded on Lebesgue
measure with constant four in squared norm, uniformly in both cutoffs. -/
theorem dyadicMaximal_energy (q top : ℤ) (N : ℕ) {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    MemLp (dyadicMaximal q top N f) 2 volume ∧
    (∫ x, (dyadicMaximal q top N f x)^2) ≤ 4*∫ x, (f x)^2 := by
  have hcover : ⋃ j : ℤ, cell q top j = (univ : Set ℝ) := by
    apply Set.eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨index q top x,mem_index_cell q top x⟩
  have hdisj : Pairwise (fun i j : ℤ => Disjoint (cell q top i) (cell q top j)) :=
    fun _ _ h => cells_disjoint q top h
  have hroot (j : ℤ) : MemLp f 2 (rootMeasure q top j) := hf.restrict _
  have h := integral_le_of_partition volume (cell q top) (cell_measurable q top) hdisj hcover
    (fun x => (dyadicMaximal q top N f x)^2) (fun x => (f x)^2)
    (fun x => sq_nonneg _) hf.integrable_sq
    (fun j => (dyadicMaximal_root_memLp q top j N (hroot j)).integrable_sq)
    (fun j => dyadicMaximal_root_energy q top j N (hroot j))
  exact ⟨(memLp_two_iff_integrable_sq (dyadicMaximal_measurable q top N f).aestronglyMeasurable).mpr h.1,h.2⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMonotoneMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing from finite scale cutoffs to a genuine countable maximal
function. The real-valued representative is defined even on the null set
where the extended supremum is infinite. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem maximalSquare_measurable {X : Type*} [MeasurableSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) :
    Measurable (maximalSquare F) :=
  Measurable.iSup (fun n => (hF n).pow_const 2 |>.ennreal_ofReal)

theorem monotoneMaximal_measurable {X : Type*} [MeasurableSpace X]
    (F : ℕ → X → ℝ) (hF : ∀ n, Measurable (F n)) :
    Measurable (monotoneMaximal F) :=
  (maximalSquare_measurable F hF).ennreal_toReal.sqrt

/-- A nonnegative increasing sequence with a uniform squared-integral
bound has a measurable L² majorant with the same bound. -/
theorem monotoneMaximal_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ℕ → X → ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀ n, Measurable (F n)) (hpos : ∀ n x, 0≤F n x)
    (hmono : Monotone F) (hLp : ∀ n, MemLp (F n) 2 μ)
    (henergy : ∀ n, (∫ x, (F n x)^2 ∂μ)≤C) :
    MemLp (monotoneMaximal F) 2 μ ∧
    (∫ x, (monotoneMaximal F x)^2 ∂μ)≤C ∧
    ∀ᵐ x ∂μ, ∀ n, F n x ≤ monotoneMaximal F x := by
  have hm := maximalSquare_measurable F hF
  have hlin : (∫⁻ x, maximalSquare F x ∂μ)≤ENNReal.ofReal C := by
    change (∫⁻ x, ⨆ n, ENNReal.ofReal ((F n x)^2) ∂μ)≤ENNReal.ofReal C
    rw [lintegral_iSup]
    · apply iSup_le
      intro n
      rw [←ofReal_integral_eq_lintegral_ofReal (hLp n).integrable_sq
        (Filter.Eventually.of_forall (fun x => sq_nonneg (F n x)))]
      exact ENNReal.ofReal_le_ofReal (henergy n)
    · exact fun n => (hF n).pow_const 2 |>.ennreal_ofReal
    · intro i j hij x
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hpos i x) (hmono hij x) 2)
  have hfin : (∫⁻ x, maximalSquare F x ∂μ)≠∞ :=
    ne_of_lt (hlin.trans_lt ENNReal.ofReal_lt_top)
  have haefin := ae_lt_top hm hfin
  have hreal := integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
  have heq : (fun x => (monotoneMaximal F x)^2) =
      (fun x => (maximalSquare F x).toReal) := by
    funext x
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  refine ⟨(memLp_two_iff_integrable_sq
    (monotoneMaximal_measurable F hF).aestronglyMeasurable).mpr
      (heq.symm ▸ hreal),?_,?_⟩
  · rw [heq,integral_toReal hm.aemeasurable haefin]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    simpa only [ENNReal.toReal_ofReal hC] using h
  · filter_upwards [haefin] with x hx
    intro n
    apply Real.le_sqrt_of_sq_le
    have h := ENNReal.toReal_mono hx.ne (le_iSup (fun n => ENNReal.ofReal ((F n x)^2)) n)
    simpa only [ENNReal.toReal_ofReal (sq_nonneg (F n x))] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAxisMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual one-coordinate dyadic maximal operator on the plane.
Fubini transfers the uniform line estimate without a dimension or scale
count factor. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem indexedCellIntegral_measurable (q k : ℤ) {f : ℝ×ℝ → ℝ}
    (hf : Measurable f) :
    Measurable (fun p : ℤ×ℝ => (∫ x in cell q k p.1, f (x,p.2))/scale k) := by
  apply measurable_from_prod_countable_right
  intro i
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ:=volume.restrict (cell q k i))).measurable.div_const _

theorem horizontalCellMean_measurable (q k : ℤ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (horizontalCellMean q k f) := by
  change Measurable (fun z : ℝ×ℝ =>
    (∫ x in cell q k (index q k z.1), f (x,z.2))/scale k)
  have hm1 : Measurable (fun z : ℝ×ℝ => index q k z.1) :=
    (index_measurable q k).comp (measurable_fst : Measurable (Prod.fst : ℝ×ℝ → ℝ))
  have hm : Measurable (fun z : ℝ×ℝ => (index q k z.1,z.2)) :=
    hm1.prodMk (measurable_snd : Measurable (Prod.snd : ℝ×ℝ → ℝ))
  have hprod : Measurable (fun p : ℤ×ℝ =>
      (∫ x in cell q k p.1, f (x,p.2))/scale k) :=
    indexedCellIntegral_measurable (f:=f) q k hf
  have hc := hprod.comp hm
  exact hc

theorem horizontalMaximal_measurable (q top : ℤ) (N : ℕ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (horizontalMaximal q top N f) := by
  exact finiteMaxSignal_measurable (fun n => horizontalCellMean q (top-(n:ℤ)) f) N
    (fun n _ => horizontalCellMean_measurable q (top-(n:ℤ)) hf)

/-- The horizontal maximal operator has squared L² norm at most four
on the product Lebesgue measure. -/
theorem horizontalMaximal_energy (q top : ℤ) (N : ℕ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (horizontalMaximal q top N f) 2 (volume.prod volume) ∧
    (∫ z, (horizontalMaximal q top N f z)^2 ∂volume.prod volume) ≤
      4*∫ z, (f z)^2 ∂volume.prod volume := by
  let H := horizontalMaximal q top N f
  have hHm : Measurable H := horizontalMaximal_measurable q top N hfmeas
  have hfm : Integrable (fun z => (f z)^2) (volume.prod volume) := hf.integrable_sq
  have hslices : ∀ᵐ y ∂volume, MemLp (fun x => f (x,y)) 2 volume := by
    filter_upwards [hfm.prod_left_ae] with y hy
    exact (memLp_two_iff_integrable_sq
      (hfmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hy
  have hinner : ∀ᵐ y ∂volume,
      Integrable (fun x => (H (x,y))^2) volume ∧
      (∫ x, (H (x,y))^2) ≤ 4*∫ x, (f (x,y))^2 := by
    filter_upwards [hslices] with y hy
    have h := dyadicMaximal_energy q top N hy
    exact ⟨h.1.integrable_sq,h.2⟩
  have hmajor : Integrable (fun y => 4*∫ x, (f (x,y))^2) volume :=
    hfm.integral_prod_right.const_mul 4
  have houter : Integrable (fun y => ∫ x, ‖(H (x,y))^2‖) volume := by
    apply hmajor.mono' (hHm.pow_const 2).stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hinner] with y hy
    have hn : (∫ x, ‖(H (x,y))^2‖) = ∫ x, (H (x,y))^2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => Real.norm_of_nonneg (sq_nonneg (H (x,y))))
    rw [hn, Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg (H (x,y))))]
    exact hy.2
  have hHi : Integrable (fun z => (H z)^2) (volume.prod volume) :=
    (integrable_prod_iff' (hHm.pow_const 2).aestronglyMeasurable).mpr
      ⟨hinner.mono (fun _ hy => hy.1),houter⟩
  refine ⟨(memLp_two_iff_integrable_sq hHm.aestronglyMeasurable).mpr hHi,?_⟩
  rw [integral_prod_symm _ hHi,integral_prod_symm _ hfm,←integral_const_mul]
  apply integral_mono_ae hHi.integral_prod_right hmajor
  exact hinner.mono (fun _ hy => hy.2)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStrongDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite rectangular maximal averages on the actual nested line grids.
The constants are uniform in both scale cutoffs. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem abs_cellMean_le_dyadicMaximal (q top : ℤ) (N n : ℕ) (hn : n≤N)
    (f : ℝ → ℝ) (x : ℝ) :
    |cellMean q (top-(n:ℤ)) f x| ≤ dyadicMaximal q top N f x := by
  change |cellMean q (top-(n:ℤ)) f x| ≤
    (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
      (fun i : ℕ => |cellMean q (top-(i:ℤ)) f x|)
  exact Finset.le_sup' (fun i : ℕ => |cellMean q (top-(i:ℤ)) f x|)
    (Finset.mem_range.mpr (show n<N+1 by omega))

theorem horizontalMaximal_nonneg (q top : ℤ) (N : ℕ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤horizontalMaximal q top N f z := dyadicMaximal_nonneg _ _ _ _ _

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAllDyadicMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic maximal averages over all integer scales. Uniform finite
estimates give the countable-scale estimate without any scale loss. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem dyadicWindow_mono (q : ℤ) (f : ℝ → ℝ) :
    Monotone (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f) := by
  apply monotone_nat_of_le_succ
  intro N x
  change (Finset.range (2*N+1)).sup' Finset.nonempty_range_add_one
    (fun j : ℕ => |cellMean q ((N:ℤ)-(j:ℤ)) f x|) ≤ _
  apply (Finset.sup'_le_iff _ _).mpr
  intro j hj
  have hj' : j≤2*N := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have heq : (N:ℤ)-(j:ℤ)=((N+1:ℕ):ℤ)-((j+1:ℕ):ℤ) := by omega
  change |cellMean q ((N:ℤ)-(j:ℤ)) f x|≤_
  rw [heq]
  exact abs_cellMean_le_dyadicMaximal q (N+1:ℕ) (2*(N+1)) (j+1) (by omega) f x

theorem allDyadicMaximal_nonneg (q : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    0≤allDyadicMaximal q f x := Real.sqrt_nonneg _

theorem cellMean_le_window (q k : ℤ) (f : ℝ → ℝ) (x : ℝ) :
    |cellMean q k f x|≤dyadicMaximal q (k.natAbs:ℤ) (2*k.natAbs) f x := by
  let N := k.natAbs
  let j := ((N:ℤ)-k).toNat
  have hk : -(N:ℤ)≤k ∧ k≤N := by
    dsimp only [N]
    rw [Int.natCast_natAbs]
    exact ⟨neg_abs_le k,le_abs_self k⟩
  have hj : (j:ℤ)=(N:ℤ)-k := Int.toNat_of_nonneg (by omega)
  have hbound : j≤2*N := by omega
  have hscale : (N:ℤ)-(j:ℤ)=k := by omega
  have hcell := abs_cellMean_le_dyadicMaximal q (N:ℤ) (2*N) j hbound f x
  rw [hscale] at hcell
  exact hcell

/-- The genuine dyadic maximal operator is L² bounded, and dominates
all integer-scale averages simultaneously outside a single null set. -/
theorem allDyadicMaximal_energy (q : ℤ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (allDyadicMaximal q f) 2 volume ∧
    (∫ x, (allDyadicMaximal q f x)^2)≤4*∫ x, (f x)^2 ∧
    ∀ᵐ x ∂volume, ∀ k : ℤ, |cellMean q k f x|≤allDyadicMaximal q f x := by
  have h := monotoneMaximal_energy volume
    (fun N : ℕ => dyadicMaximal q (N:ℤ) (2*N) f)
    (4*∫ x, (f x)^2) (mul_nonneg (by norm_num) (integral_nonneg (fun x => sq_nonneg (f x))))
    (fun N => dyadicMaximal_measurable q N (2*N) f)
    (fun N x => dyadicMaximal_nonneg q N (2*N) f x)
    (dyadicWindow_mono q f)
    (fun N => (dyadicMaximal_energy q N (2*N) hf).1)
    (fun N => (dyadicMaximal_energy q N (2*N) hf).2)
  refine ⟨h.1,h.2.1,?_⟩
  filter_upwards [h.2.2] with x hx
  intro k
  exact (cellMean_le_window q k f x).trans (hx k.natAbs)

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

theorem threeGridMaximal_nonneg (f : ℝ → ℝ) (x : ℝ) :
    0≤threeGridMaximal f x :=
  Finset.sum_nonneg (fun _ _ => allDyadicMaximal_nonneg _ _ _)

theorem allDyadicMaximal_le_three (q : GridChoice) (f : ℝ → ℝ) (x : ℝ) :
    allDyadicMaximal q.val f x≤threeGridMaximal f x :=
  Finset.single_le_sum (fun _ _ => allDyadicMaximal_nonneg _ _ _) (Finset.mem_univ q)

/-- All real intervals containing a point are controlled simultaneously,
not merely an a.e. set chosen separately for each interval. -/
theorem interval_average_le_threeGridMaximal {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hf0 : ∀ x, 0≤f x) :
    ∀ᵐ x ∂volume, ∀ c r : ℝ, 0 < r → x∈Icc (c-r) (c+r) →
      (∫ y in Icc (c-r) (c+r), f y)/(2*r)≤6*threeGridMaximal f x := by
  have hdom : ∀ᵐ x ∂volume, ∀ q : GridChoice, ∀ k : ℤ,
      |cellMean q.val k f x|≤allDyadicMaximal q.val f x :=
    ae_all_iff.mpr (fun q => (allDyadicMaximal_energy q.val hf).2.2)
  filter_upwards [hdom] with x hx
  intro c r hr hxc
  obtain ⟨q,hq,k,j,hsub,hscale⟩ := exists_comparable_three_grid_cover c r hr
  let Q : GridChoice := ⟨q,hq⟩
  have hxcell := hsub hxc
  have hint : IntegrableOn f (cell q k j) :=
    (show MemLp f 2 (rootMeasure q k j) from hf.restrict _).integrable (by norm_num)
  have hI : (∫ y in Icc (c-r) (c+r), f y)≤∫ y in cell q k j, f y :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hsub)
  have heq : (∫ y in cell q k j, f y)=scale k*cellMean q k f x := by
    unfold cellMean
    rw [index_eq_of_mem hxcell]
    field_simp [(scale_pos k).ne']
  have hmean : cellMean q k f x≤threeGridMaximal f x :=
    (le_abs_self _).trans ((hx Q k).trans (allDyadicMaximal_le_three Q f x))
  apply (div_le_iff₀ (by positivity : 0<2*r)).mpr
  calc
    _ ≤ scale k*cellMean q k f x := hI.trans_eq heq
    _ ≤ scale k*threeGridMaximal f x := mul_le_mul_of_nonneg_left hmean (scale_pos k).le
    _ ≤ (12*r)*threeGridMaximal f x :=
      mul_le_mul_of_nonneg_right hscale (threeGridMaximal_nonneg f x)
    _ = _ := by ring

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceKernelShells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic annuli for a reproducing-kernel bound by actual interval
averages. Closed outer intervals and open inner intervals retain every
boundary point. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem kernelShell_measurable (c r : ℝ) (n : ℕ) : MeasurableSet (kernelShell c r n) := by
  cases n with
  | zero => exact measurableSet_Icc
  | succ n => exact measurableSet_Icc.diff measurableSet_Ioo

theorem kernelShell_subset (c r : ℝ) (n : ℕ) :
    kernelShell c r n⊆Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r) := by
  cases n with
  | zero => simp only [kernelShell,pow_zero,one_mul,subset_refl]
  | succ n => exact fun _ hx => hx.1

theorem kernelShell_covers (c r : ℝ) (hr : 0 < r) :
    (⋃ n, kernelShell c r n)=univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : |x-c| ≤ r
  · have h := abs_le.mp hx
    exact mem_iUnion.mpr ⟨0,by constructor <;> linarith [h.1,h.2]⟩
  · have hd : 1≤|x-c|/r := (le_div_iff₀ hr).mpr (by linarith)
    obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near hd (by norm_num : (1:ℝ)<2)
    have hlo' := (le_div_iff₀ hr).mp hlo
    have hhi' := (div_lt_iff₀ hr).mp hhi
    refine mem_iUnion.mpr ⟨n+1,?_,?_⟩
    · exact ⟨by linarith [(neg_le_abs (x-c))],by linarith [(le_abs_self (x-c))]⟩
    · intro hin
      have hlt : |x-c|<(2:ℝ)^n*r := abs_lt.mpr ⟨by linarith [hin.1],by linarith [hin.2]⟩
      exact not_lt_of_ge hlo' hlt

theorem kernelShell_lower (c r : ℝ) (hr : 0 < r) (n : ℕ) {x : ℝ}
    (hx : x∈kernelShell c r (n+1)) :
    (2:ℝ)^n≤|(x-c)/r| := by
  have hlow : (2:ℝ)^n*r≤|x-c| := by
    by_contra hn
    apply hx.2
    have h := abs_lt.mp (lt_of_not_ge hn)
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  rw [abs_div,abs_of_pos hr]
  exact (le_div_iff₀ hr).mpr hlow

/-- The inverse quadratic envelope has a geometric shell bound; after
multiplication by shell length, the remaining series has ratio one half. -/
theorem kernelShell_envelope (c r : ℝ) (hr : 0 < r) (n : ℕ) {x : ℝ}
    (hx : x∈kernelShell c r n) :
    lineEnvelope c r 1 x≤4/((2:ℝ)^n)^2 := by
  have hden : 0<1+((x-c)/r)^2 := by positivity
  cases n with
  | zero =>
    simp only [pow_zero,one_pow,div_one]
    have h := lineEnvelope_antitone c r x (by omega : 0≤1)
    simp only [lineEnvelope,pow_zero,inv_one] at h
    exact h.trans (by norm_num)
  | succ n =>
    have hlow := kernelShell_lower c r hr n hx
    have hsq := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^n) hlow 2
    rw [sq_abs] at hsq
    simp only [lineEnvelope,pow_one]
    rw [inv_eq_one_div,div_le_div_iff₀ hden (sq_pos_of_pos (by positivity))]
    rw [show (2:ℝ)^(n+1)=(2:ℝ)^n*2 by exact pow_succ _ _]
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceKernelIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive kernel tail is controlled by interval averages.
The constant is independent of the spatial scale. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem kernel_integral_of_interval_bounds (f : ℝ → ℝ) (hf : Measurable f)
    (C c r M : ℝ) (hr : 0 < r) (hM : 0≤M)
    (hf0 : ∀ x, 0≤f x) (hbound : ∀ x, ‖f x‖≤C)
    (havg : ∀ n : ℕ,
      (∫ x in Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r), f x)≤12*((2:ℝ)^n*r)*M) :
    (∫ x, r⁻¹*lineEnvelope c r 1 x*f x)≤96*M := by
  let g := fun x => r⁻¹*lineEnvelope c r 1 x*f x
  have hg0 (x) : 0≤g x :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) (lineEnvelope_nonneg _ _ _ _)) (hf0 x)
  have hgi : Integrable g :=
    ((integrable_lineEnvelope_one c r hr).const_mul r⁻¹).mul_bdd
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hfb (n : ℕ) : IntegrableOn f (Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r)) :=
    IntegrableOn.of_bound measure_Icc_lt_top hf.aestronglyMeasurable.restrict C
      (Filter.Eventually.of_forall hbound)
  have hshell (n : ℕ) :
      (∫ x in kernelShell c r n, g x)≤(48*M)*(1/2:ℝ)^n := by
    let t : ℝ := 2^n
    have ht : 0<t := by dsimp [t]; positivity
    let A : ℝ := r⁻¹*(4/t^2)
    have hA : 0≤A := by dsimp [A]; positivity
    have hlocal : (∫ x in kernelShell c r n, g x)≤
        A*∫ x in kernelShell c r n, f x := by
      rw [←integral_const_mul]
      apply setIntegral_mono_on hgi.integrableOn
        (((hfb n).mono_set (kernelShell_subset c r n)).const_mul A) (kernelShell_measurable c r n)
      intro x hx
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (kernelShell_envelope c r hr n hx) (inv_nonneg.mpr hr.le)) (hf0 x)
    have hsub : (∫ x in kernelShell c r n, f x)≤
        ∫ x in Icc (c-t*r) (c+t*r), f x :=
      setIntegral_mono_set (hfb n) (Filter.Eventually.of_forall hf0)
        (Filter.Eventually.of_forall (kernelShell_subset c r n))
    calc
      _ ≤ A*(12*(t*r)*M) := hlocal.trans
        (mul_le_mul_of_nonneg_left (hsub.trans (havg n)) hA)
      _ = (48*M)*(1/2:ℝ)^n := by
        dsimp [A,t]
        rw [one_div_pow]
        field_simp
        ring
  have hgeo : Summable (fun n : ℕ => (48*M)*(1/2:ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_left _
  have hsum : (∑' n : ℕ, (48*M)*(1/2:ℝ)^n)=96*M := by
    rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]
    ring
  have hlin : ENNReal.ofReal (∫ x, g x)≤ENNReal.ofReal (96*M) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
    calc
      _ ≤ ∑' n : ℕ, ∫⁻ x in kernelShell c r n, ENNReal.ofReal (g x) := by
        simpa only [kernelShell_covers c r hr,Measure.restrict_univ] using
          lintegral_iUnion_le (kernelShell c r) (fun x => ENNReal.ofReal (g x))
      _ ≤ ∑' n : ℕ, ENNReal.ofReal ((48*M)*(1/2:ℝ)^n) := by
        apply ENNReal.tsum_le_tsum
        intro n
        rw [←ofReal_integral_eq_lintegral_ofReal hgi.integrableOn
          (Filter.Eventually.of_forall hg0)]
        exact ENNReal.ofReal_le_ofReal (hshell n)
      _ = ENNReal.ofReal (96*M) := by
        rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hgeo,hsum]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤96*M)).mp hlin

/-- The kernel centered at any point within one scale of the evaluation
point is bounded by its actual three-grid maximal majorant. -/
theorem kernel_integral_le_threeGridMaximal (f : ℝ → ℝ) (hf : Measurable f)
    (hLp : MemLp f 2 volume) (C : ℝ) (hf0 : ∀ x, 0≤f x) (hbound : ∀ x, ‖f x‖≤C) :
    ∀ᵐ z ∂volume, ∀ c r : ℝ, 0 < r → |z-c| ≤ r →
      (∫ x, r⁻¹*lineEnvelope c r 1 x*f x)≤96*DyadicLineGrid.threeGridMaximal f z := by
  filter_upwards [DyadicLineGrid.interval_average_le_threeGridMaximal hLp hf0] with z hz
  intro c r hr hzc
  apply kernel_integral_of_interval_bounds f hf C c r _ hr
    (DyadicLineGrid.threeGridMaximal_nonneg f z) hf0 hbound
  intro n
  have hpow : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  have hrad : 0<(2:ℝ)^n*r := mul_pos (by positivity) hr
  have hmem : z∈Icc (c-(2:ℝ)^n*r) (c+(2:ℝ)^n*r) := by
    have h := hzc.trans (show r≤(2:ℝ)^n*r by nlinarith)
    exact ⟨by linarith [(abs_le.mp h).1],by linarith [(abs_le.mp h).2]⟩
  have h := (div_le_iff₀ (by positivity : 0<2*((2:ℝ)^n*r))).mp (hz c ((2:ℝ)^n*r) hrad hmem)
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAllStrongMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable-scale coordinate maximal functions on the plane, with
uniform strong L² control. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

theorem allHorizontalMaximal_measurable (q : ℤ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (allHorizontalMaximal q f) :=
  monotoneMaximal_measurable _ (fun N => horizontalMaximal_measurable q N (2*N) hf)

theorem allHorizontalMaximal_energy (q : ℤ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (allHorizontalMaximal q f) 2 (volume.prod volume) ∧
    (∫ z, (allHorizontalMaximal q f z)^2 ∂volume.prod volume)≤
      4*∫ z, (f z)^2 ∂volume.prod volume ∧
    ∀ᵐ z ∂volume.prod volume, ∀ k : ℤ,
      |horizontalCellMean q k f z|≤allHorizontalMaximal q f z := by
  have h := monotoneMaximal_energy (volume.prod volume)
    (fun N : ℕ => horizontalMaximal q (N:ℤ) (2*N) f)
    (4*∫ z, (f z)^2 ∂volume.prod volume)
    (mul_nonneg (by norm_num) (integral_nonneg (fun z => sq_nonneg (f z))))
    (fun N => horizontalMaximal_measurable q N (2*N) hfmeas)
    (fun N z => horizontalMaximal_nonneg q N (2*N) f z)
    (fun i j hij z => dyadicWindow_mono q (fun x => f (x,z.2)) hij z.1)
    (fun N => (horizontalMaximal_energy q N (2*N) hfmeas hf).1)
    (fun N => (horizontalMaximal_energy q N (2*N) hfmeas hf).2)
  refine ⟨h.1,h.2.1,?_⟩
  filter_upwards [h.2.2] with z hz
  intro k
  exact (cellMean_le_window q k (fun x => f (x,z.2)) z.1).trans (hz k.natAbs)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaximalBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform boundedness of the actual maximal representatives on a
bounded source, including on their null-set representatives. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem monotoneMaximal_le_of_bound {X : Type*} (F : ℕ → X → ℝ)
    (x : X) (B : ℝ) (hB : 0≤B) (hF : ∀ n, |F n x|≤B) :
    monotoneMaximal F x≤B := by
  have hsq : maximalSquare F x≤ENNReal.ofReal (B^2) := by
    apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (F n x)) (hF n) 2
  apply Real.sqrt_le_iff.mpr
  refine ⟨hB,?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsq
  simpa only [ENNReal.toReal_ofReal (sq_nonneg B)] using h

namespace DyadicLineGrid

theorem cellMean_bound (q k : ℤ) (f : ℝ → ℝ) (B : ℝ)
    (hbound : ∀ y, |f y|≤B) (x : ℝ) : |cellMean q k f x|≤B := by
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (s:=cell q k (index q k x)) (f:=f) (C:=B)
    (show volume (cell q k (index q k x))<∞ from measure_Ico_lt_top)
    (fun y (_ : y∈cell q k (index q k x)) => by simpa only [Real.norm_eq_abs] using hbound y)
  rw [cellMean,abs_div,abs_of_pos (scale_pos k)]
  apply (div_le_iff₀ (scale_pos k)).mpr
  simpa only [Real.norm_eq_abs,cell_length] using h

theorem dyadicMaximal_bound (q top : ℤ) (N : ℕ) (f : ℝ → ℝ) (B : ℝ)
    (hbound : ∀ y, |f y|≤B) (x : ℝ) : dyadicMaximal q top N f x≤B := by
  change (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
    (fun n : ℕ => |cellMean q (top-(n:ℤ)) f x|)≤B
  apply (Finset.sup'_le_iff _ _).mpr
  intro n _
  exact cellMean_bound q (top-(n:ℤ)) f B hbound x

theorem allDyadicMaximal_bound (q : ℤ) (f : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hbound : ∀ y, |f y|≤B) (x : ℝ) : allDyadicMaximal q f x≤B := by
  apply monotoneMaximal_le_of_bound _ x B hB
  intro n
  rw [abs_of_nonneg (dyadicMaximal_nonneg _ _ _ _ _)]
  exact dyadicMaximal_bound q n (2*n) f B hbound x

theorem threeGridMaximal_bound (f : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hbound : ∀ y, |f y|≤B) (x : ℝ) : threeGridMaximal f x≤3*B := by
  calc
    _ ≤ ∑ q : GridChoice, B := Finset.sum_le_sum (fun q _ => allDyadicMaximal_bound q.val f B hB hbound x)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; norm_num

end DyadicLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridPlane
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three-grid coordinate majorants on the plane. The construction has
uniform bounds both on L² and on bounded functions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem threeHorizontalMaximal_eq_line (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    threeHorizontalMaximal f z=threeGridMaximal (fun x => f (x,z.2)) z.1 := rfl

theorem threeHorizontalMaximal_measurable {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (threeHorizontalMaximal f) :=
  Finset.measurable_sum _ (fun _ _ => allHorizontalMaximal_measurable _ hf)

theorem threeVerticalMaximal_measurable {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (threeVerticalMaximal f) :=
  (threeHorizontalMaximal_measurable (hf.comp measurable_swap)).comp measurable_swap

theorem threeStrongMaximal_measurable {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (threeStrongMaximal f) :=
  threeHorizontalMaximal_measurable (threeVerticalMaximal_measurable hf)

theorem threeHorizontalMaximal_nonneg (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤threeHorizontalMaximal f z := threeGridMaximal_nonneg _ _

theorem threeVerticalMaximal_nonneg (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤threeVerticalMaximal f z := threeGridMaximal_nonneg _ _

theorem threeStrongMaximal_nonneg (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤threeStrongMaximal f z := threeHorizontalMaximal_nonneg _ _

theorem threeVerticalMaximal_bound (f : ℝ×ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hf : ∀ z, |f z|≤B) (z : ℝ×ℝ) :
    threeVerticalMaximal f z≤3*B :=
  threeGridMaximal_bound _ B hB (fun y => hf (z.1,y)) z.2

theorem threeHorizontalMaximal_energy {f : ℝ×ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (threeHorizontalMaximal f) 2 (volume.prod volume) ∧
    (∫ z, (threeHorizontalMaximal f z)^2 ∂volume.prod volume)≤
      36*∫ z, (f z)^2 ∂volume.prod volume := by
  have hq (q : GridChoice) := allHorizontalMaximal_energy q.val hfm hf
  have hm : MemLp (threeHorizontalMaximal f) 2 (volume.prod volume) :=
    memLp_finsetSum Finset.univ (fun q _ => (hq q).1)
  have he := weighted_integral_sum_square (volume.prod volume)
    (fun q : GridChoice => allHorizontalMaximal q.val f) (fun q => (hq q).1)
    (fun _ => (1:ℝ)) (fun _ => by norm_num)
  simp only [div_one,Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,
    gridChoice_card,nsmul_eq_mul,mul_one] at he
  refine ⟨hm,he.trans ?_⟩
  calc
    _ ≤ 3*∑ q : GridChoice, (4*∫ z, (f z)^2 ∂volume.prod volume) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => (hq q).2.1)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; ring

theorem threeVerticalMaximal_energy {f : ℝ×ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (threeVerticalMaximal f) 2 (volume.prod volume) ∧
    (∫ z, (threeVerticalMaximal f z)^2 ∂volume.prod volume)≤
      36*∫ z, (f z)^2 ∂volume.prod volume := by
  have hs : MemLp (f ∘ Prod.swap) 2 (volume.prod volume) :=
    hf.comp_measurePreserving Measure.measurePreserving_swap
  have h := threeHorizontalMaximal_energy (hfm.comp measurable_swap) hs
  refine ⟨h.1.comp_measurePreserving Measure.measurePreserving_swap,?_⟩
  change (∫ z, (threeHorizontalMaximal (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume)≤_
  rw [show (∫ z, (threeHorizontalMaximal (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume)=
      ∫ z, (threeHorizontalMaximal (f ∘ Prod.swap) z)^2 ∂volume.prod volume from
    integral_prod_swap (fun z => (threeHorizontalMaximal (f ∘ Prod.swap) z)^2)]
  calc
    _ ≤ 36*∫ z, ((f ∘ Prod.swap) z)^2 ∂volume.prod volume := h.2
    _ = _ := by congr 1; exact integral_prod_swap (fun z => (f z)^2)

theorem threeStrongMaximal_energy {f : ℝ×ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (threeStrongMaximal f) 2 (volume.prod volume) ∧
    (∫ z, (threeStrongMaximal f z)^2 ∂volume.prod volume)≤
      1296*∫ z, (f z)^2 ∂volume.prod volume := by
  have hv := threeVerticalMaximal_energy hfm hf
  have hh := threeHorizontalMaximal_energy (threeVerticalMaximal_measurable hfm) hv.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ 36*(36*∫ z, (f z)^2 ∂volume.prod volume) := mul_le_mul_of_nonneg_left hv.2 (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarKernelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product reproducing-kernel majorants are controlled by the actual
strong maximal construction on the plane. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
open DyadicLineGrid

theorem normalizedLineEnvelope_measurable (c r : ℝ) :
    Measurable (normalizedLineEnvelope c r) := by unfold normalizedLineEnvelope lineEnvelope; fun_prop

theorem normalizedLineEnvelope_nonneg (c r x : ℝ) (hr : 0 < r) :
    0≤normalizedLineEnvelope c r x :=
  mul_nonneg (inv_nonneg.mpr hr.le) (lineEnvelope_nonneg _ _ _ _)

theorem normalizedLineEnvelope_integrable (c r : ℝ) (hr : 0 < r) :
    Integrable (normalizedLineEnvelope c r) :=
  (integrable_lineEnvelope_one c r hr).const_mul _

theorem verticalKernelAverage_measurable {U : ℝ×ℝ → ℝ} (hU : Measurable U) (c r : ℝ) :
    Measurable (verticalKernelAverage U c r) :=
  (((normalizedLineEnvelope_measurable c r).comp measurable_snd).mul hU).stronglyMeasurable.integral_prod_right'.measurable

theorem verticalKernelAverage_le_maximal {U : ℝ×ℝ → ℝ}
    (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hU0 : ∀ z, 0≤U z) (hUb : ∀ z, ‖U z‖≤B)
    (c r : ℝ) (hr : 0 < r) :
    ∀ᵐ z ∂volume.prod volume, |z.2-c| ≤ r →
      verticalKernelAverage U c r z.1≤96*threeVerticalMaximal U z := by
  have hP : MeasurableSet {z : ℝ×ℝ | |z.2-c| ≤ r →
      verticalKernelAverage U c r z.1≤96*threeVerticalMaximal U z} := by
    simp only [imp_iff_not_or]
    change MeasurableSet ({z : ℝ×ℝ | |z.2-c| ≤ r}ᶜ ∪
      {z | verticalKernelAverage U c r z.1≤96*threeVerticalMaximal U z})
    exact (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-c|) by fun_prop)
      measurable_const).compl.union
      (measurableSet_le ((verticalKernelAverage_measurable hUm c r).comp measurable_fst)
        ((threeVerticalMaximal_measurable hUm).const_mul 96))
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  filter_upwards [hU2.integrable_sq.prod_right_ae] with x hx
  have hxm : Measurable (fun y => U (x,y)) := hUm.comp (measurable_const.prodMk measurable_id)
  have hx2 : MemLp (fun y => U (x,y)) 2 volume :=
    (memLp_two_iff_integrable_sq hxm.aestronglyMeasurable).mpr hx
  filter_upwards [kernel_integral_le_threeGridMaximal (fun y => U (x,y)) hxm hx2 B
    (fun y => hU0 (x,y)) (fun y => hUb (x,y))] with y hy
  intro hyc
  exact hy c r hr hyc

/-- The product kernel is bounded on its central rectangle by one
strong maximal function, with constants independent of both scales. -/
theorem planar_kernel_le_strongMaximal {U : ℝ×ℝ → ℝ}
    (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ z, 0≤U z) (hUb : ∀ z, ‖U z‖≤B)
    (cx cy rx ry : ℝ) (hrx : 0 < rx) (hry : 0 < ry) :
    ∀ᵐ z ∂volume.prod volume, |z.1-cx| ≤ rx ∧ |z.2-cy| ≤ ry →
      (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume)≤9216*threeStrongMaximal U z := by
  let V := threeVerticalMaximal U
  have hVm : Measurable V := threeVerticalMaximal_measurable hUm
  have hV2 : MemLp V 2 (volume.prod volume) := (threeVerticalMaximal_energy hUm hU2).1
  have hV0 (z) : 0≤V z := threeVerticalMaximal_nonneg U z
  have hVb (z) : ‖V z‖≤3*B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hV0 z)]
    exact threeVerticalMaximal_bound U B hB (fun z => by simpa only [Real.norm_eq_abs] using hUb z) z
  have hki : Integrable (fun p : ℝ×ℝ =>
      normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p)
      (volume.prod volume) :=
    ((normalizedLineEnvelope_integrable cx rx hrx).mul_prod
      (normalizedLineEnvelope_integrable cy ry hry)).mul_bdd
      hUm.aestronglyMeasurable (Filter.Eventually.of_forall hUb)
  have houter : Integrable (fun x => normalizedLineEnvelope cx rx x*verticalKernelAverage U cy ry x) := by
    have h := hki.integral_prod_left
    simpa only [verticalKernelAverage,Prod.fst,Prod.snd,mul_assoc,integral_const_mul] using h
  have heq : (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
      ∂volume.prod volume)=∫ x, normalizedLineEnvelope cx rx x*verticalKernelAverage U cy ry x := by
    rw [integral_prod _ hki]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [verticalKernelAverage,←integral_const_mul,mul_assoc])
  have hvertical := verticalKernelAverage_le_maximal hUm hU2 B hU0 hUb cy ry hry
  have hPv : MeasurableSet {z : ℝ×ℝ | |z.2-cy| ≤ ry →
      verticalKernelAverage U cy ry z.1≤96*V z} := by
    simp only [imp_iff_not_or]
    change MeasurableSet ({z : ℝ×ℝ | |z.2-cy| ≤ ry}ᶜ ∪
      {z | verticalKernelAverage U cy ry z.1≤96*V z})
    exact (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-cy|) by fun_prop)
      measurable_const).compl.union
      (measurableSet_le ((verticalKernelAverage_measurable hUm cy ry).comp measurable_fst)
        (hVm.const_mul 96))
  have hvertical' : ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
      |y-cy| ≤ ry → verticalKernelAverage U cy ry x≤96*V (x,y) :=
    (Measure.ae_ae_comm hPv).mp (Measure.ae_ae_of_ae_prod hvertical)
  have hP : MeasurableSet {z : ℝ×ℝ | |z.1-cx| ≤ rx ∧ |z.2-cy| ≤ ry →
      (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume)≤9216*threeStrongMaximal U z} := by
    simp only [imp_iff_not_or]
    change MeasurableSet (({z : ℝ×ℝ | |z.1-cx| ≤ rx} ∩ {z | |z.2-cy| ≤ ry})ᶜ ∪
      {z | (∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume)≤9216*threeStrongMaximal U z})
    exact ((measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.1-cx|) by fun_prop)
      measurable_const).inter
      (measurableSet_le (show Measurable (fun z : ℝ×ℝ => |z.2-cy|) by fun_prop)
        measurable_const)).compl.union
        (measurableSet_le measurable_const ((threeStrongMaximal_measurable hUm).const_mul 9216))
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  apply (Measure.ae_ae_comm hP).mpr
  filter_upwards [hvertical',hV2.integrable_sq.prod_left_ae] with y hy hy2
  have hym : Measurable (fun x => V (x,y)) := hVm.comp (measurable_id.prodMk measurable_const)
  have hyLp : MemLp (fun x => V (x,y)) 2 volume :=
    (memLp_two_iff_integrable_sq hym.aestronglyMeasurable).mpr hy2
  filter_upwards [kernel_integral_le_threeGridMaximal (fun x => V (x,y)) hym hyLp (3*B)
    (fun x => hV0 (x,y)) (fun x => hVb (x,y))] with x hx
  rintro ⟨hxc,hyc⟩
  have hVK : Integrable (fun s => normalizedLineEnvelope cx rx s*V (s,y)) :=
    (normalizedLineEnvelope_integrable cx rx hrx).mul_bdd hym.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => hVb (s,y)))
  calc
    _ = ∫ s, normalizedLineEnvelope cx rx s*verticalKernelAverage U cy ry s := heq
    _ ≤ 96*∫ s, normalizedLineEnvelope cx rx s*V (s,y) := by
      rw [←integral_const_mul]
      apply integral_mono_ae houter (hVK.const_mul 96)
      filter_upwards [hy] with s hs
      have h := mul_le_mul_of_nonneg_left (hs hyc) (normalizedLineEnvelope_nonneg cx rx s hrx)
      nlinarith only [h]
    _ ≤ 96*(96*threeGridMaximal (fun s => V (s,y)) x) :=
      mul_le_mul_of_nonneg_left (hx cx rx hrx hxc) (by norm_num)
    _ = _ := by change _ = 9216*threeHorizontalMaximal V (x,y); rw [threeHorizontalMaximal_eq_line]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SchwartzPacketDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Obtain the finite packet decay orders directly from Schwartz
seminorms, including the first two vertical derivatives. -/

noncomputable section
namespace LipschitzHilbert

theorem schwartzEnvelopeConstant_pos (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    0 < schwartzEnvelopeConstant f n := by
  unfold schwartzEnvelopeConstant
  positivity

theorem schwartz_lineEnvelope_bound (f : SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    ‖f x‖ ≤ schwartzEnvelopeConstant f n*lineEnvelope 0 1 n x := by
  have hp : 0 < polynomialWeight 0 1 n x :=
    zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)
  have h := SchwartzMap.norm_le_seminorm ℝ (polynomialLocalization 0 1 n f) x
  rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp] at h
  have hbound : polynomialWeight 0 1 n x*‖f x‖ ≤ schwartzEnvelopeConstant f n := by
    dsimp [schwartzEnvelopeConstant]
    linarith
  calc
    ‖f x‖ ≤ schwartzEnvelopeConstant f n/polynomialWeight 0 1 n x :=
      (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hbound)
    _ = schwartzEnvelopeConstant f n*lineEnvelope 0 1 n x := by
      simp [polynomialWeight, lineEnvelope, div_eq_mul_inv]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReproduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Schwartz reproducing kernels for the long-tree frequency
rectangles. A smooth compact-frequency cutoff is constructed, rather
than adding a reproduction hypothesis to the tree estimate. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform Convolution
namespace LipschitzHilbert

/-- A smooth frequency cutoff equal to one throughout the prescribed
closed interval. Its inverse transform is a Schwartz reproducing kernel. -/
theorem exists_schwartz_reproducing_kernel (R : ℝ) (hR : 0<R) :
    ∃ K : SchwartzMap ℝ ℂ, ∀ ξ, |ξ|≤R → 𝓕 K ξ=1 := by
  let b : ContDiffBump (0:ℝ) := ⟨R,2*R,hR,by linarith⟩
  let chi : SchwartzMap ℝ ℂ :=
    (b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨𝓕⁻ chi,?_⟩
  intro ξ hξ
  rw [fourier_fourierInv_eq]
  change (b ξ : ℂ)=1
  rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hξ)]
  norm_num

theorem scaledReproducingKernel_fourier (K : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0 < r) (ξ : ℝ) :
    𝓕 (scaledReproducingKernel K r hr) ξ=𝓕 K (r*ξ) := by
  simp only [scaledReproducingKernel,fourier_smul,smul_apply,
    schwartzDilation_fourier,inv_inv,abs_of_pos hr]
  rw [smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  congr 1
  field_simp

/-- Every fixed Schwartz seminorm gives the scale-invariant polynomial
kernel tail used in the cell-supremum estimate. -/
theorem scaledReproducingKernel_envelope (K : SchwartzMap ℝ ℂ)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (x : ℝ) :
    ‖scaledReproducingKernel K r hr x‖≤
      (schwartzEnvelopeConstant K n/r)*lineEnvelope 0 r n x := by
  rw [scaledReproducingKernel_apply,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hr]
  have h := mul_le_mul_of_nonneg_left (schwartz_lineEnvelope_bound K n (x/r))
    (inv_nonneg.mpr hr.le)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [lineEnvelope,sub_zero,div_eq_mul_inv]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVectorReproduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reproduction estimates for the actual Hilbert-valued packets, with
constants independent of the number of Hilbert coordinates. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped Convolution
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

/-- Scalar convolution reproduces a vector Schwartz function on its
original Fourier support. -/
theorem vector_schwartz_convolution_reproduction
    (K : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (hK : ∀ ξ, 𝓕 f ξ≠0 → 𝓕 K ξ=1) :
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) K f=f := by
  have hprod : SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕 K) (𝓕 f)=𝓕 f := by
    ext ξ k
    have h : 𝓕 K ξ • 𝓕 f ξ=𝓕 f ξ := by
      by_cases hzero : 𝓕 f ξ=0
      · rw [hzero,smul_zero]
      · rw [hK ξ hzero,one_smul]
    exact congrArg (fun v : EuclideanSpace ℂ κ => v k) h
  calc
    _ = 𝓕⁻ (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) K f)) := by simp
    _ = 𝓕⁻ (𝓕 f) := by rw [SchwartzMap.fourier_convolution,hprod]
    _ = f := by simp

/-- The symmetric integral formula places the packet norm under a
positive scalar kernel. -/
theorem vector_schwartz_integral_reproduction
    (K : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (hK : ∀ ξ, 𝓕 f ξ≠0 → 𝓕 K ξ=1) (x : ℝ) :
    f x=∫ y, K (x-y) • f y := by
  have h := congrArg (fun g : SchwartzMap ℝ (EuclideanSpace ℂ κ) => g x)
    (vector_schwartz_convolution_reproduction K f hK)
  rw [SchwartzMap.convolution_apply,←convolution_flip,convolution_def] at h
  exact h.symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarVectorReproduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A product reproducing formula for general Hilbert-valued planar
Schwartz packets, derived from their two actual coordinate spectra. -/
noncomputable section
open MeasureTheory FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem vector_scaled_integral_reproduction
    (K : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (R r : ℝ) (hr : 0 < r) (hK : ∀ ξ, |ξ|≤R → 𝓕 K ξ=1)
    (hf : ∀ ξ, 𝓕 f ξ≠0 → |ξ|≤R/r) (x : ℝ) :
    f x=∫ y, scaledReproducingKernel K r hr (x-y) • f y := by
  apply vector_schwartz_integral_reproduction
  intro ξ hξ
  rw [scaledReproducingKernel_fourier]
  apply hK
  rw [abs_mul,abs_of_pos hr]
  have h := (le_div_iff₀ hr).mp (hf ξ hξ)
  nlinarith

theorem planar_vector_integral_reproduction
    (Kx Ky : SchwartzMap ℝ ℂ) (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry rx ry : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤Ry/ry)
    (x y : ℝ) :
    f (x,y)=∫ p, (scaledReproducingKernel Kx rx hrx (x-p.1)*
      scaledReproducingKernel Ky ry hry (y-p.2)) • f p ∂volume.prod volume := by
  let A := scaledReproducingKernel Kx rx hrx
  let B := scaledReproducingKernel Ky ry hry
  let M := SchwartzMap.seminorm ℝ 0 0 f
  have hiA : Integrable (fun s => A (x-s)) := A.integrable.comp_sub_left x
  have hiB : Integrable (fun t => B (y-t)) := B.integrable.comp_sub_left y
  have hmajor : Integrable (fun p : ℝ×ℝ => (‖A (x-p.1)‖*‖B (y-p.2)‖)*M)
      (volume.prod volume) := (hiA.norm.mul_prod hiB.norm).mul_const M
  have hi : Integrable (fun p : ℝ×ℝ => (A (x-p.1)*B (y-p.2)) • f p)
      (volume.prod volume) := by
    apply hmajor.mono' (by fun_prop)
    filter_upwards [] with p
    rw [norm_smul,norm_mul]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ f p)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ = ∫ s, A (x-s) • f (s,y) := by
      simpa only [vectorHorizontalSlice_apply] using
        vector_scaled_integral_reproduction Kx (vectorHorizontalSlice f y) Rx rx hrx hKx (hFx y) x
    _ = ∫ s, A (x-s) • ∫ t, B (y-t) • f (s,t) := by
      apply integral_congr_ae
      filter_upwards [] with s
      congr 1
      simpa only [vectorVerticalSlice_apply] using
        vector_scaled_integral_reproduction Ky (vectorVerticalSlice f s) Ry ry hry hKy (hFy s) y
    _ = ∫ s, ∫ t, (A (x-s)*B (y-t)) • f (s,t) := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [←integral_smul]
      simp only [smul_smul]
    _ = _ := (integral_prod _ hi).symm

/-- Moving the evaluation point within one kernel scale changes the
positive envelope by at most a factor four. -/
theorem lineEnvelope_move_center (c x r s : ℝ) (hr : 0 < r) (hx : |x-c| ≤ r) :
    lineEnvelope x r 1 s≤4*lineEnvelope c r 1 s := by
  have h := polynomial_base_le s x c r r hr hr le_rfl hx
  simp only [lineEnvelope,pow_one,inv_eq_one_div]
  have hA : 0<1+((s-x)/r)^2 := by positivity
  have hB : 0<1+((s-c)/r)^2 := by positivity
  rw [mul_one_div,div_le_div_iff₀ hA hB]
  simpa only [div_pow,one_mul] using h

theorem scaledReproducingKernel_shifted_bound (K : SchwartzMap ℝ ℂ)
    (r c x s : ℝ) (hr : 0 < r) (hx : |x-c| ≤ r) :
    ‖scaledReproducingKernel K r hr (x-s)‖≤
      (4*schwartzEnvelopeConstant K 1)*normalizedLineEnvelope c r s := by
  have hC := (schwartzEnvelopeConstant_pos K 1).le
  have h := scaledReproducingKernel_envelope K r hr 1 (x-s)
  have heq : lineEnvelope 0 r 1 (x-s)=lineEnvelope x r 1 s := by
    simp only [lineEnvelope,sub_zero,div_pow,sub_sq_comm]
  rw [heq] at h
  calc
    _ ≤ (schwartzEnvelopeConstant K 1/r)*lineEnvelope x r 1 s := h
    _ ≤ (schwartzEnvelopeConstant K 1/r)*(4*lineEnvelope c r 1 s) :=
      mul_le_mul_of_nonneg_left (lineEnvelope_move_center c x r s hr hx) (div_nonneg hC hr.le)
    _ = _ := by unfold normalizedLineEnvelope; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoxReproduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform reproduction on a physical rectangle. The two spectra are
properties of the actual coordinate restrictions, and all vector
members are controlled by one scalar maximal function. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert
open DyadicLineGrid
variable {κ : Type*} [Fintype κ]

theorem planar_reproduction_kernel_bound
    (Kx Ky : SchwartzMap ℝ ℂ) (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry cx cy rx ry : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤Ry/ry)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (B : ℝ) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ p, ‖f p‖≤U p) (w : ℝ×ℝ) (hw : w∈coordinateBox cx cy rx ry) :
    ‖f w‖≤(16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
      ∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
        ∂volume.prod volume := by
  let Cx := schwartzEnvelopeConstant Kx 1
  let Cy := schwartzEnvelopeConstant Ky 1
  have hCx : 0≤Cx := (schwartzEnvelopeConstant_pos Kx 1).le
  have hCy : 0≤Cy := (schwartzEnvelopeConstant_pos Ky 1).le
  have hki : Integrable (fun p : ℝ×ℝ =>
      normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p)
      (volume.prod volume) :=
    ((normalizedLineEnvelope_integrable cx rx hrx).mul_prod
      (normalizedLineEnvelope_integrable cy ry hry)).mul_bdd hUm.aestronglyMeasurable
        (Filter.Eventually.of_forall hUb)
  rw [show f w=f (w.1,w.2) from rfl,
    planar_vector_integral_reproduction Kx Ky f Rx Ry rx ry hrx hry hKx hKy hFx hFy w.1 w.2,
    ←integral_const_mul]
  apply norm_integral_le_of_norm_le (hki.const_mul (16*Cx*Cy))
  filter_upwards [] with p
  rw [norm_smul,norm_mul]
  have hx := scaledReproducingKernel_shifted_bound Kx rx cx w.1 p.1 hrx hw.1
  have hy := scaledReproducingKernel_shifted_bound Ky ry cy w.2 p.2 hry hw.2
  have hkx := normalizedLineEnvelope_nonneg cx rx p.1 hrx
  have hky := normalizedLineEnvelope_nonneg cy ry p.2 hry
  calc
    _ ≤ ((4*Cx)*normalizedLineEnvelope cx rx p.1)*
        ((4*Cy)*normalizedLineEnvelope cy ry p.2)*U p :=
      mul_le_mul (mul_le_mul hx hy (norm_nonneg _) (by positivity)) (hFU p)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- One exceptional set controls every packet and every evaluation
point of the box. -/
theorem planar_family_box_bound {ι : Type*}
    (Kx Ky : SchwartzMap ℝ ℂ) (F : ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry cx cy rx ry : ℝ) (hrx : 0 < rx) (hry : 0 < ry)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ a y ξ, 𝓕 (vectorHorizontalSlice (F a) y) ξ≠0 → |ξ|≤Rx/rx)
    (hFy : ∀ a x η, 𝓕 (vectorVerticalSlice (F a) x) η≠0 → |η|≤Ry/ry)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ a p, ‖F a p‖≤U p) :
    ∀ᵐ z ∂volume.prod volume, z∈coordinateBox cx cy rx ry →
      ∀ a w, w∈coordinateBox cx cy rx ry →
        ‖F a w‖≤(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
          threeStrongMaximal U z := by
  have hC : 0≤16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1 := by
    have := (schwartzEnvelopeConstant_pos Kx 1).le
    have := (schwartzEnvelopeConstant_pos Ky 1).le
    positivity
  filter_upwards [planar_kernel_le_strongMaximal hUm hU2 B hB hU0 hUb cx cy rx ry hrx hry] with z hz
  intro hzc a w hw
  calc
    _ ≤ (16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
        ∫ p, normalizedLineEnvelope cx rx p.1*normalizedLineEnvelope cy ry p.2*U p
          ∂volume.prod volume :=
      planar_reproduction_kernel_bound Kx Ky (F a) Rx Ry cx cy rx ry hrx hry hKx hKy
        (hFx a) (hFy a) U hUm B hUb (hFU a) w hw
    _ ≤ (16*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)*
        (9216*threeStrongMaximal U z) := mul_le_mul_of_nonneg_left (hz hzc) hC
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A disjoint half-open partition underneath the manuscript's closed
transverse cells. Boundary points are retained exactly once. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

theorem transverseCell_measurable (b W : ℝ) (n : ℤ) :
    MeasurableSet (transverseCell b W n) := measurableSet_Ico

theorem transverseCell_length (b W : ℝ) (n : ℤ) (hW : 0<W) :
    volume.real (transverseCell b W n)=W := by
  rw [transverseCell,Real.volume_real_Ico_of_le (by linarith)]
  ring

theorem transverseCell_bound (b W : ℝ) (n : ℤ) {y : ℝ}
    (hy : y∈transverseCell b W n) : |y-b-(n:ℝ)*W|≤W/2 := by
  exact abs_le.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩

theorem transverseCell_disjoint (b W : ℝ) (hW : 0<W) :
    Pairwise (Disjoint on transverseCell b W) := by
  have haux (n m : ℤ) (hlt : n < m) :
      Disjoint (transverseCell b W n) (transverseCell b W m) := by
    have hstep : (n:ℝ)+1 ≤ m := by exact_mod_cast (show n+1 ≤ m by omega)
    have hmul := mul_le_mul_of_nonneg_right hstep hW.le
    apply Set.disjoint_left.mpr
    intro y hyn hym
    have hny := hyn.2
    have hmy := hym.1
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · exact haux n m hlt
  · exact (haux m n hlt).symm

theorem mem_transverseCell_floor (b W y : ℝ) (hW : 0<W) :
    y∈transverseCell b W ⌊(y-b)/W+1/2⌋ := by
  have hl := Int.floor_le ((y-b)/W+1/2)
  have hu := Int.lt_floor_add_one ((y-b)/W+1/2)
  have hl' := mul_le_mul_of_nonneg_right hl hW.le
  have hu' := mul_lt_mul_of_pos_right hu hW
  have hc : ((y-b)/W+1/2)*W=y-b+W/2 := by field_simp
  rw [hc] at hl' hu'
  constructor <;> linarith

theorem partitionCell_measurable (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    MeasurableSet (partitionCell b W p) :=
  (cell_measurable 0 p.1.1 p.1.2).prod (transverseCell_measurable b W p.2)

theorem partitionCell_finite (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    (volume.prod volume) (partitionCell b W p)≠∞ := by
  rw [partitionCell,Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Ico_lt_top.ne measure_Ico_lt_top.ne

theorem partitionCell_area (b W : ℝ) (p : (ℤ×ℤ)×ℤ) (hW : 0<W) :
    (volume.prod volume).real (partitionCell b W p)=scale p.1.1*W := by
  rw [partitionCell,measureReal_prod_prod,cell_length,transverseCell_length b W p.2 hW]

theorem partitionCell_subset_box (b W : ℝ) (p : (ℤ×ℤ)×ℤ) :
    partitionCell b W p⊆coordinateBox (center p.1.1 p.1.2) (b+(p.2:ℝ)*W)
      (scale p.1.1/2) (W/2) := by
  intro z hz
  refine ⟨point_center_bound p.1.1 p.1.2 hz.1,?_⟩
  have h := transverseCell_bound b W p.2 hz.2
  simpa only [sub_add_eq_sub_sub] using h

theorem partitionCell_disjoint {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    (b W : ℝ) (hW : 0<W) (S : Set ((ℤ×ℤ)×ℤ))
    (hS : ∀ p∈S, Whitney tiles x ell p.1.1 p.1.2) :
    Set.Pairwise S (Disjoint on partitionCell b W) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro z hzp hzq
  by_cases he : p.1=q.1
  · have hn : p.2≠q.2 := by
      intro hn
      exact hpq (Prod.ext he hn)
    exact Set.disjoint_left.mp (transverseCell_disjoint b W hW hn) hzp.2 hzq.2
  · exact Set.disjoint_left.mp (whitney_disjoint tiles x ell (hS p hp) (hS q hq) he) hzp.1 hzq.1

end LipschitzHilbert.SourceWhitney

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

/-- The transverse tail left by the fixed manuscript exponents is summable. -/
theorem summable_transverse_sixth :
    Summable (fun n : ℤ => ((1+|(n:ℝ)|)^6)⁻¹) := by
  have hs : Summable (fun n : ℕ => (((n:ℝ)+1)^6)⁻¹) := by
    have h := (summable_nat_add_iff (f:=fun n : ℕ => ((n:ℝ)^6)⁻¹) 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1<(6:ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have ha (n : ℕ) : |(n:ℝ)|=(n:ℝ) := abs_of_nonneg n.cast_nonneg
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast,ha,add_comm] using hs
  · simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,ha,add_comm] using hs

theorem transverseTailConstant_nonneg : 0≤transverseTailConstant :=
  tsum_nonneg (fun _ => by positivity)

theorem finite_transverse_tail (s : Finset ℤ) :
    ∑ n∈s, ((1+|(n:ℝ)|)^6)⁻¹≤transverseTailConstant :=
  summable_transverse_sixth.sum_le_tsum s (fun _ _ => by positivity)

/-- Weighted Cauchy--Schwarz with exactly the exponents needed by the
cell-density and polynomial-energy estimates. -/
theorem transverse_density_cauchy {J : Type*} (s : Finset J)
    (A m w : J → ℝ) (hm : ∀ j∈s, 0 ≤ m j) (hw : ∀ j∈s, 0<w j) :
    (∑ j∈s, A j*m j*(w j)^203)^2≤
      (∑ j∈s, (A j)^2*m j*(w j)^412)*(∑ j∈s, m j/(w j)^6) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun j hj => mul_nonneg (mul_nonneg (sq_nonneg _) (hm j hj)) (pow_nonneg (hw j hj).le _))
    (fun j hj => div_nonneg (hm j hj) (pow_nonneg (hw j hj).le _))
  intro j hj
  apply le_of_eq
  have hw0 : (w j)^6≠0 := pow_ne_zero _ (hw j hj).ne'
  have hp : (w j)^412/(w j)^6=(w j)^406 := by
    rw [show (412:ℕ)=406+6 by omega,pow_add,mul_div_cancel_right₀ _ hw0]
  calc
    (A j*m j*(w j)^203)^2=(A j)^2*(m j)^2*(w j)^406 := by
      rw [mul_pow,mul_pow,←pow_mul]
    _ = (A j)^2*(m j)^2*((w j)^412/(w j)^6) := by rw [hp]
    _ = _ := by ring

/-- Density mass times the actual supremum is controlled by weighted
energy and the summable volume tail. -/
theorem finite_density_supremum_sum {J : Type*} (s : Finset J)
    (A d m w : J → ℝ) (D E V : ℝ)
    (hA : ∀ j∈s, 0≤A j) (hd : ∀ j∈s, 0≤d j)
    (hm : ∀ j∈s, 0 ≤ m j) (hw : ∀ j∈s, 0<w j)
    (hE : 0≤E)
    (hmass : ∀ j∈s, d j≤D*(w j)^203*m j)
    (henergy : (∑ j∈s, (A j)^2*m j*(w j)^412)≤E)
    (hvolume : (∑ j∈s, m j/(w j)^6)≤V) :
    (∑ j∈s, A j*d j)^2≤D^2*E*V := by
  have hsum : (∑ j∈s, A j*d j)≤D*∑ j∈s, A j*m j*(w j)^203 := by
    calc
      _ ≤ ∑ j∈s, A j*(D*(w j)^203*m j) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hmass j hj) (hA j hj))
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hs0 : 0≤∑ j∈s, A j*d j :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hA j hj) (hd j hj))
  have hc := transverse_density_cauchy s A m w hm hw
  have hEV : (∑ j∈s, A j*m j*(w j)^203)^2≤E*V :=
    hc.trans (mul_le_mul henergy hvolume
      (Finset.sum_nonneg (fun j hj => div_nonneg (hm j hj) (pow_nonneg (hw j hj).le _))) hE)
  calc
    _ ≤ (D*∑ j∈s, A j*m j*(w j)^203)^2 := pow_le_pow_left₀ hs0 hsum 2
    _ = D^2*(∑ j∈s, A j*m j*(w j)^203)^2 := mul_pow _ _ _
    _ ≤ D^2*(E*V) := mul_le_mul_of_nonneg_left hEV (sq_nonneg D)
    _ = _ := by ring

namespace SourceWhitney
open DyadicLineGrid

/-- For any finite family of small Whitney intervals, the entire
transverse tail has a uniform volume budget. -/
theorem finite_whitney_transverse_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) (c L W : ℝ) (hL : 0≤L) (hW : 0≤W)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ)
    (hWhitney : ∀ p∈S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p∈S, scale p.1≤L) :
    (∑ p∈S×ˢT, (scale p.1.1*W)/(1+|(p.2:ℝ)|)^6)≤
      9*L*W*transverseTailConstant := by
  have hS := small_length_budget tiles x ell hL hcenters S hWhitney hscale
  have hT := finite_transverse_tail T
  calc
    _ = (∑ p∈S, scale p.1)*W*(∑ n∈T, ((1+|(n:ℝ)|)^6)⁻¹) := by
      rw [Finset.sum_product,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    _ ≤ (9*L)*W*transverseTailConstant := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hS hW) hT
        (Finset.sum_nonneg (fun _ _ => by positivity))
        (mul_nonneg (mul_nonneg (by norm_num) hL) hW)
    _ = _ := by ring

end SourceWhitney
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVectorSchwartz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite scalar packet coordinates assemble into an actual vector
Schwartz function. Fourier cutoffs pass through the same coordinates. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]
attribute [local instance] Classical.propDecidable

theorem vector_fourier_coordinate (f : SchwartzMap ℝ (EuclideanSpace ℂ κ))
    (k : κ) (ξ : ℝ) :
    (𝓕 f ξ) k=𝓕 (f.postcompCLM (vectorCoordinate k)) ξ := by
  let phase := fun x : ℝ => Real.fourierChar (-(x*ξ))
  have hi : Integrable (fun x => phase x • f x) := by
    apply f.integrable.norm.mono' (by fun_prop)
    filter_upwards [] with x
    simp only [Circle.norm_smul]
    exact le_rfl
  have h := (vectorCoordinate k).integral_comp_comm hi
  simp only [SchwartzMap.fourier_coe,Real.fourier_eq,Real.inner_apply]
  change vectorCoordinate k (∫ x, phase x • f x)=
    ∫ x, phase x • (f.postcompCLM (vectorCoordinate k)) x
  rw [←h]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Circle.smul_def,map_smul,SchwartzMap.postcompCLM_apply]

theorem vectorSchwartz_fourier_coordinate (f : κ → SchwartzMap ℝ ℂ) (k : κ) (ξ : ℝ) :
    (𝓕 (vectorSchwartz f) ξ) k=𝓕 (f k) ξ := by
  have heq : (vectorSchwartz f).postcompCLM (vectorCoordinate k)=f k := by
    ext x
    simp only [SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,vectorSchwartz_apply]
  rw [vector_fourier_coordinate,heq]

theorem vectorSchwartz_fourier_zero (f : κ → SchwartzMap ℝ ℂ) (ξ : ℝ)
    (hf : ∀ k, 𝓕 (f k) ξ=0) : 𝓕 (vectorSchwartz f) ξ=0 := by
  ext k
  rw [vectorSchwartz_fourier_coordinate,hf]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCoordinateSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Fourier support of actual planar packets. These lemmas
project the original two-dimensional spectrum without a tensor assumption. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

theorem planarFourier_swap (f : SchwartzMap (ℝ×ℝ) ℂ) (ξ η : ℝ) :
    planarFourier (planarSwap f) (ξ,η)=planarFourier f (η,ξ) := by
  unfold planarFourier
  simp only [planarSwap_apply]
  have h := integral_prod_swap (μ:=volume) (ν:=volume)
    (fun z : ℝ×ℝ => Real.fourierChar (-(z.1*η+z.2*ξ)) • f z)
  simpa only [Prod.fst_swap,Prod.snd_swap,add_comm] using h

theorem planarVerticalSlice_fourier_eq_zero (f : SchwartzMap (ℝ×ℝ) ℂ)
    (x η : ℝ) (hfiber : ∀ ξ, planarFourier f (ξ,η)=0) :
    𝓕 (planarVerticalSlice f x) η=0 := by
  apply planarSchwartzSlice_fourier_eq_zero
  intro ξ
  simpa only [zero_mul,sub_zero,planarFourier_swap] using hfiber ξ

theorem planarHorizontalSlice_fourier_band (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ)
    (hf : ∀ ξ η, planarFourier f (ξ,η)≠0 → |ξ|≤R) (y ξ : ℝ)
    (hne : 𝓕 (planarSchwartzSlice f y 0) ξ≠0) : |ξ|≤R := by
  by_contra hn
  apply hne
  apply planarSchwartzSlice_fourier_eq_zero
  intro η
  simp only [zero_mul,sub_zero]
  by_contra h
  exact hn (hf ξ η h)

theorem planarVerticalSlice_fourier_band (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ)
    (hf : ∀ ξ η, planarFourier f (ξ,η)≠0 → |η|≤R) (x η : ℝ)
    (hne : 𝓕 (planarVerticalSlice f x) η≠0) : |η|≤R := by
  by_contra hn
  apply hne
  apply planarVerticalSlice_fourier_eq_zero
  intro ξ
  by_contra h
  exact hn (hf ξ η h)

/-- Angular and cycles-per-unit cutoffs differ by exactly `2π`. -/
theorem planarAngularFourier_coordinate_bands (f : SchwartzMap (ℝ×ℝ) ℂ) (Rx Ry : ℝ)
    (hf : ∀ ξ η, planarAngularFourier f (ξ,η)≠0 → |ξ|≤Rx ∧ |η|≤Ry) :
    ∀ ξ η, planarFourier f (ξ,η)≠0 →
      |ξ|≤Rx/(2*Real.pi) ∧ |η|≤Ry/(2*Real.pi) := by
  intro ξ η hne
  have hπ : 0<2*Real.pi := by positivity
  have he (t : ℝ) : (2*Real.pi*t)/(2*Real.pi)=t := by field_simp
  have hs := hf (2*Real.pi*ξ) (2*Real.pi*η) (by
    simpa only [planarAngularFourier,he] using hne)
  simp only [abs_mul,abs_of_pos hπ] at hs
  constructor
  · exact (le_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hs.1)
  · exact (le_div_iff₀ hπ).mpr (by simpa only [mul_comm] using hs.2)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums of the original scalar planar packets are actual vector
Schwartz maps, and their coordinate cutoffs follow from those of the
nonzero summands. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem planarSynthesisSchwartz_horizontal (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (y : ℝ) (k : κ) :
    (vectorHorizontalSlice (planarSynthesisSchwartz c f) y).postcompCLM (vectorCoordinate k)=
      packetSynthesis (fun i => c i k) (fun i => planarSchwartzSlice (f i k) y 0) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,vectorHorizontalSlice_apply,
    planarSynthesisSchwartz,vectorSchwartz_apply,sum_apply,smul_apply,smul_eq_mul,
    packetSynthesis_apply,planarSchwartzSlice_apply,zero_mul,add_zero]

theorem planarSynthesisSchwartz_vertical (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (x : ℝ) (k : κ) :
    (vectorVerticalSlice (planarSynthesisSchwartz c f) x).postcompCLM (vectorCoordinate k)=
      packetSynthesis (fun i => c i k) (fun i => planarVerticalSlice (f i k) x) := by
  ext y
  simp only [SchwartzMap.postcompCLM_apply,vectorCoordinate_apply,vectorVerticalSlice_apply,
    planarSynthesisSchwartz,vectorSchwartz_apply,sum_apply,smul_apply,smul_eq_mul,
    packetSynthesis_apply,planarVerticalSlice_apply]

theorem planarSynthesisSchwartz_coordinate_bands (c : ι → EuclideanSpace ℂ κ)
    (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) (Rx Ry : ℝ)
    (hfx : ∀ i k, c i k≠0 → ∀ y ξ, 𝓕 (planarSchwartzSlice (f i k) y 0) ξ≠0 → |ξ|≤Rx)
    (hfy : ∀ i k, c i k≠0 → ∀ x η, 𝓕 (planarVerticalSlice (f i k) x) η≠0 → |η|≤Ry) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice (planarSynthesisSchwartz c f) y) ξ≠0 → |ξ|≤Rx) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice (planarSynthesisSchwartz c f) x) η≠0 → |η|≤Ry) := by
  constructor
  · intro y ξ hne
    by_contra hn
    apply hne
    ext k
    rw [vector_fourier_coordinate,planarSynthesisSchwartz_horizontal,packetSynthesis_fourier]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hc : c i k=0
    · rw [hc,zero_mul]
    · have hz : 𝓕 (planarSchwartzSlice (f i k) y 0) ξ=0 := by
        by_contra h
        exact hn (hfx i k hc y ξ h)
      rw [hz,mul_zero]
  · intro x η hne
    by_contra hn
    apply hne
    ext k
    rw [vector_fourier_coordinate,planarSynthesisSchwartz_vertical,packetSynthesis_fourier]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hc : c i k=0
    · rw [hc,zero_mul]
    · have hz : 𝓕 (planarVerticalSlice (f i k) x) η=0 := by
        by_contra h
        exact hn (hfy i k hc x η h)
      rw [hz,mul_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted interval-maximal synthesis on actual separated
source trees, conditional only on the published scalar Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal
namespace LipschitzHilbert

private theorem continuous_interval_max {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => intervalOscillation (fun n => F n x) N 0 N) := by
  classical
  let v := fun (q : Fin (N+1)×Fin (N+1)) (x : X) =>
    if 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N then ‖F q.2 x-F q.1 x‖ else 0
  have hv (q) : Continuous (v q) := by
    by_cases hq : 0≤q.1.val ∧ q.1.val≤q.2.val ∧ q.2.val≤N
    · simpa only [v,ite_eq_left hq,Pi.sub_apply] using ((hF q.2).sub (hF q.1)).norm
    · simp only [v,ite_eq_right hq]; exact continuous_const
  have h := Continuous.finset_sup' Finset.univ_nonempty (fun q _ => hv q)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [intervalOscillation,v,Finset.sup'_apply]


namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

theorem physicalTreePartial_continuous (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) :
    Continuous (P.physicalTreePartial t c n) := by
  classical
  unfold physicalTreePartial packetPartialSum
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val<n
  · simp only [ite_eq_left hj]
    unfold planarFixedSynthesis
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_finsetSum _ fun u _ =>
      continuous_const.mul (P.physicalPacket t j u.1 u.2 k).continuous
  · simp only [ite_eq_right hj]; exact continuous_const

theorem physicalTreeMaximal_continuous (P : SourceLabeledLattice N κ Label Item)
    (t : ℝ) (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Continuous (P.physicalTreeMaximal t c) :=
  continuous_interval_max _ (P.physicalTreePartial_continuous t c) N

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Schwartz representatives and coordinate spectra of tree
partial sums. Only packets longer than the cell scale are used. -/
noncomputable section
open FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ : Type} [Fintype κ]

theorem vector_horizontal_sum {J : Type*} (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
    vectorHorizontalSlice (∑ j∈s, f j) y=∑ j∈s, vectorHorizontalSlice (f j) y := by
  ext x k
  simp only [vectorHorizontalSlice_apply,sum_apply,WithLp.ofLp_sum,Finset.sum_apply]

theorem vector_vertical_sum {J : Type*} (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorVerticalSlice (∑ j∈s, f j) x=∑ j∈s, vectorVerticalSlice (f j) x := by
  ext y k
  simp only [vectorVerticalSlice_apply,sum_apply,WithLp.ofLp_sum,Finset.sum_apply]

theorem vector_sum_bands {J : Type*} (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (Rx Ry : ℝ)
    (hf : ∀ j∈s,
      (∀ y ξ, 𝓕 (vectorHorizontalSlice (f j) y) ξ≠0 → |ξ|≤Rx) ∧
      (∀ x η, 𝓕 (vectorVerticalSlice (f j) x) η≠0 → |η|≤Ry)) :
    (∀ y ξ, 𝓕 (vectorHorizontalSlice (∑ j∈s, f j) y) ξ≠0 → |ξ|≤Rx) ∧
    (∀ x η, 𝓕 (vectorVerticalSlice (∑ j∈s, f j) x) η≠0 → |η|≤Ry) := by
  constructor
  · intro y ξ hne
    by_contra hn
    apply hne
    rw [vector_horizontal_sum,fourier_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    by_contra h
    exact hn ((hf j hj).1 y ξ h)
  · intro x η hne
    by_contra hn
    apply hne
    rw [vector_vertical_sum,fourier_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    by_contra h
    exact hn ((hf j hj).2 x η h)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongPrefixes
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long packets form a literal prefix in scale. Every truncated
interval of that prefix has the proved coordinate cutoffs and is bounded
pointwise by the original tree maximum. -/
noncomputable section
open FourierTransform
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem longPrefix_le (r : ℝ) : P.longPrefix r≤N := by
  apply Finset.sup_le
  intro j _
  omega

theorem longPrefix_spec (r : ℝ) (j : Fin N) :
    j.val<P.longPrefix r ↔ 32*r<P.length j := by
  unfold longPrefix
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨k,hk,hjk⟩
    have hkj : j≤k := by change j.val≤k.val; omega
    exact (Finset.mem_filter.mp hk).2.trans_le (P.length_antitone hkj)
  · intro hj
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,by omega⟩

theorem physicalLongIntervalSchwartz_norm (t r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lo hi : ℕ) (z : ℝ×ℝ) :
    ‖P.physicalLongIntervalSchwartz t r c lo hi z‖≤P.physicalTreeMaximal t c z := by
  simp only [physicalLongIntervalSchwartz,sub_apply,physicalTreePartialSchwartz_apply]
  let a := min lo (P.longPrefix r)
  let b := min hi (P.longPrefix r)
  have ha : a≤N := (min_le_right _ _).trans (P.longPrefix_le r)
  have hb : b≤N := (min_le_right _ _).trans (P.longPrefix_le r)
  rcases le_total a b with hab | hba
  · exact increment_le_intervalOscillation _ N 0 N a b (Nat.zero_le _) hab hb le_rfl
  · rw [norm_sub_rev]
    exact increment_le_intervalOscillation _ N 0 N b a (Nat.zero_le _) hba ha le_rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenLongInterval
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The hard angular cutoff in the frozen long-tree expression selects
one exact interval of the original scale indices. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem angularStart_spec (w d : ℝ) (hw : 0≤w) (j : Fin N) :
    j.val<P.angularStart w d ↔ w/P.length j<d := by
  unfold angularStart
  rw [Finset.lt_sup_iff]
  constructor
  · rintro ⟨k,hk,hjk⟩
    have hkj : j≤k := by change j.val≤k.val; omega
    have hdiv : w/P.length j≤w/P.length k :=
      div_le_div_of_nonneg_left hw (P.length_pos k) (P.length_antitone hkj)
    exact hdiv.trans_lt (Finset.mem_filter.mp hk).2
  · intro hj
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,by omega⟩

/-- The frozen selector tail, intersected with the long prefix, is a
literal interval difference, including the empty-interval case. -/
theorem frozenLongValue_eq_interval (t r w s : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    P.frozenLongValue t r w s c z=
      P.physicalLongIntervalSchwartz t r c (P.angularStart w |s-t|) N z := by
  simp only [physicalLongIntervalSchwartz,sub_apply,physicalTreePartialSchwartz_apply,
    physicalTreePartial,packetPartialSum]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hl : j.val < min N (P.longPrefix r) ↔ 32*r<P.length j := by
    rw [lt_min_iff,P.longPrefix_spec]
    exact and_iff_right j.isLt
  have ha : j.val < min (P.angularStart w |s-t|) (P.longPrefix r) ↔
      ¬|s-t|≤w/P.length j ∧ 32*r<P.length j := by
    rw [lt_min_iff,P.angularStart_spec w |s-t| hw,P.longPrefix_spec,not_le]
  by_cases hj : 32*r<P.length j <;> by_cases hs : |s-t|≤w/P.length j <;>
    simp only [hl,ha,hj,hs,and_true,and_false,not_true_eq_false,
      not_false_eq_true,ite_true, if_true,ite_false, if_false,sub_zero,sub_self]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoxSupremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual suprema of packet values and their energy on disjoint cells.
The supremum includes zero, so an empty packet family contributes zero. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {X E ι : Type*} [NormedAddCommGroup E]

theorem packetNormValues_bddAbove (F : ι → X → E) (Q : Set X)
    (B : ℝ) (hB : 0≤B) (hF : ∀ a x, x∈Q → ‖F a x‖≤B) :
    BddAbove (packetNormValues F Q) := by
  refine ⟨B,?_⟩
  rintro r (hr | ⟨a,x,hx,rfl⟩)
  · exact hr ▸ hB
  · exact hF a x hx

theorem packetNormSup_nonneg (F : ι → X → E) (Q : Set X)
    (B : ℝ) (hB : 0≤B) (hF : ∀ a x, x∈Q → ‖F a x‖≤B) :
    0≤packetNormSup F Q :=
  le_csSup (packetNormValues_bddAbove F Q B hB hF) (Or.inl rfl)

theorem packetNormSup_le (F : ι → X → E) (Q : Set X)
    (B : ℝ) (hB : 0≤B) (hF : ∀ a x, x∈Q → ‖F a x‖≤B) :
    packetNormSup F Q≤B := by
  unfold packetNormSup
  apply csSup_le (s:=packetNormValues F Q) ⟨0,Or.inl rfl⟩
  rintro r (hr | ⟨a,x,hx,rfl⟩)
  · exact hr ▸ hB
  · exact hF a x hx

variable [MeasurableSpace X]

/-- Integrating a common pointwise majorant controls a literal supremum
on any finite-measure cell. -/
theorem packetNormSup_cell_energy (μ : Measure X) (F : ι → X → E) (Q A : Set X)
    (hA : MeasurableSet A) (hAfin : μ A≠∞)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hF : ∀ a x, x∈Q → ‖F a x‖≤B)
    (g : X → ℝ) (hg : MemLp g 2 μ) (hg0 : ∀ x, 0≤g x)
    (hpoint : ∀ᵐ z ∂μ, z∈A → ∀ a x, x∈Q → ‖F a x‖≤C*g z) :
    (packetNormSup F Q)^2*μ.real A≤C^2*∫ z in A, (g z)^2 ∂μ := by
  have hsup0 := packetNormSup_nonneg F Q B hB hF
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  have hi : (∫ _z in A, (packetNormSup F Q)^2 ∂μ)≤
      ∫ z in A, C^2*(g z)^2 ∂μ := by
    apply integral_mono_ae (integrable_const _) ((hg.restrict A).integrable_sq.const_mul _)
    filter_upwards [ae_restrict_of_ae hpoint,ae_restrict_mem hA] with z hz hzA
    have hs := packetNormSup_le F Q (C*g z) (mul_nonneg hC (hg0 z)) (hz hzA)
    simpa only [mul_pow] using pow_le_pow_left₀ hsup0 hs 2
  rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,integral_const_mul] at hi
  simpa only [mul_comm] using hi

/-- Disjoint cell summation does not introduce a cell-count factor. -/
theorem packetNormSup_finite_energy {J : Type*} (μ : Measure X) (s : Finset J)
    (F : J → ι → X → E) (Q A : J → Set X)
    (hA : ∀ j∈s, MeasurableSet (A j)) (hAfin : ∀ j∈s, μ (A j)≠∞)
    (hdisj : Set.Pairwise (↑s) (Disjoint on A))
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hF : ∀ j∈s, ∀ a x, x∈Q j → ‖F j a x‖≤B)
    (g : X → ℝ) (hg : MemLp g 2 μ) (hg0 : ∀ x, 0≤g x)
    (hpoint : ∀ j∈s, ∀ᵐ z ∂μ, z∈A j → ∀ a x, x∈Q j → ‖F j a x‖≤C*g z) :
    (∑ j∈s, (packetNormSup (F j) (Q j))^2*μ.real (A j))≤
      C^2*∫ z, (g z)^2 ∂μ := by
  calc
    _ ≤ ∑ j∈s, C^2*∫ z in A j, (g z)^2 ∂μ :=
      Finset.sum_le_sum (fun j hj => packetNormSup_cell_energy μ (F j) (Q j) (A j)
        (hA j hj) (hAfin j hj) B C hB hC (hF j hj) g hg hg0 (hpoint j hj))
    _ = C^2*∫ z in ⋃ j∈s, A j, (g z)^2 ∂μ := by
      rw [←Finset.mul_sum,integral_biUnion_finset s hA hdisj (fun _ _ => hg.integrable_sq.integrableOn)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hg.integrable_sq (Filter.Eventually.of_forall (fun z => sq_nonneg (g z))))
      (sq_nonneg C)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoxSupremumEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform cell-supremum energy estimate, derived from actual
coordinate spectra and the proved strong maximal bound. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators FourierTransform ENNReal
namespace LipschitzHilbert
open DyadicLineGrid
variable {J ι κ : Type*} [Fintype κ]

theorem finite_box_supremum_energy
    (s : Finset J) (Kx Ky : SchwartzMap ℝ ℂ)
    (F : J → ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (Rx Ry : ℝ) (cx cy rx ry : J → ℝ)
    (hrx : ∀ j∈s, 0 < rx j) (hry : ∀ j∈s, 0 < ry j)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ j∈s, ∀ a y ξ, 𝓕 (vectorHorizontalSlice (F j a) y) ξ≠0 → |ξ|≤Rx/rx j)
    (hFy : ∀ j∈s, ∀ a x η, 𝓕 (vectorVerticalSlice (F j a) x) η≠0 → |η|≤Ry/ry j)
    (A : J → Set (ℝ×ℝ)) (hA : ∀ j∈s, MeasurableSet (A j))
    (hAfin : ∀ j∈s, (volume.prod volume) (A j)≠∞)
    (hsub : ∀ j∈s, A j⊆coordinateBox (cx j) (cy j) (rx j) (ry j))
    (hdisj : Set.Pairwise (↑s) (Disjoint on A))
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ j∈s, ∀ a p, ‖F j a p‖≤U p) :
    (∑ j∈s, (packetNormSup (fun a z => F j a z)
      (coordinateBox (cx j) (cy j) (rx j) (ry j)))^2*(volume.prod volume).real (A j))≤
      (147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*
        (1296*∫ p, (U p)^2 ∂volume.prod volume) := by
  let C := 147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1
  have hC : 0≤C := by
    have := (schwartzEnvelopeConstant_pos Kx 1).le
    have := (schwartzEnvelopeConstant_pos Ky 1).le
    positivity
  have hG := threeStrongMaximal_energy hUm hU2
  have hpoint (j : J) (hj : j∈s) :
      ∀ᵐ z ∂volume.prod volume, z∈A j →
        ∀ a x, x∈coordinateBox (cx j) (cy j) (rx j) (ry j) →
          ‖F j a x‖≤C*threeStrongMaximal U z := by
    have h := planar_family_box_bound Kx Ky (F j) Rx Ry (cx j) (cy j) (rx j) (ry j)
      (hrx j hj) (hry j hj) hKx hKy (hFx j hj) (hFy j hj)
      U hUm hU2 B hB hU0 hUb (hFU j hj)
    filter_upwards [h] with z hz
    intro hzA
    exact hz (hsub j hj hzA)
  have hbound : ∀ j∈s, ∀ a x, x∈coordinateBox (cx j) (cy j) (rx j) (ry j) →
      ‖F j a x‖≤B := by
    intro j hj a x _
    exact (hFU j hj a x).trans ((le_abs_self (U x)).trans (hUb x))
  have h := packetNormSup_finite_energy (volume.prod volume) s
    (fun j a z => F j a z) (fun j => coordinateBox (cx j) (cy j) (rx j) (ry j))
    A hA hAfin hdisj B C hB hC hbound (threeStrongMaximal U) hG.1
    (threeStrongMaximal_nonneg U) hpoint
  exact h.trans (mul_le_mul_of_nonneg_left hG.2 (sq_nonneg C))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCellPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial weights on the actual transverse cells of a tree.
The exponent is kept symbolic so the fixed high order need not expand. -/
noncomputable section
namespace LipschitzHilbert

theorem transverse_cell_polynomial_lower (b W n y : ℝ) (q : ℕ)
    (hW : 0<W) (hy : |y-b-n*W|≤W/2) :
    ((1+|n|)^2/32)^q≤polynomialWeight b (2*W) q y := by
  have hy' : |y-(b+n*W)|≤2*W := by
    have he : y-(b+n*W)=y-b-n*W := by ring
    rw [he]
    linarith
  have h := box_polynomial_weight (b+n*W) (2*W) (-n/2) y q (by positivity) hy'
  have hc : b+n*W+(2*W)*(-n/2)=b := by ring
  rw [hc] at h
  apply le_trans _ h
  apply pow_le_pow_left₀ (by positivity)
  rw [abs_div,abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [abs_nonneg n]

theorem transverse_cell_polynomial_weight (b W n y : ℝ) (q : ℕ)
    (hW : 0<W) (hy : |y-b-n*W|≤W/2) :
    (1+|n|)^(2*q)≤32^q*polynomialWeight b (2*W) q y := by
  have h := transverse_cell_polynomial_lower b W n y q hW hy
  rw [div_pow,←pow_mul] at h
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<(32:ℝ)^q)).mp h

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

theorem vectorPolynomialLocalization_high (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ (EuclideanSpace ℂ κ)) (hi : ℝ)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ=0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (vectorPolynomialLocalization a r q f) ξ=0 := by
  apply vectorSchwartz_fourier_zero
  intro k
  apply polynomialLocalization_high a r q (f.postcompCLM (vectorCoordinate k)) 0 hi
    (fun η hη => (not_lt_of_ge (abs_nonneg η) hη).elim) _ ξ hξ
  intro η hη
  rw [←vector_fourier_coordinate,hhigh η hη]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePlanarPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse polynomial localization of actual planar vector packets.
Both coordinate frequency cutoffs are retained. -/
noncomputable section
open FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem transversePolynomial_temperate (b r : ℝ) (q : ℕ) :
    Function.HasTemperateGrowth (fun z : ℝ×ℝ => (polynomialWeight b r q z.2:ℂ)) := by
  have hs : Function.HasTemperateGrowth (fun z : ℝ×ℝ => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  unfold polynomialWeight
  simp only [div_eq_mul_inv]
  fun_prop

@[simp] theorem planarPolynomialLocalization_apply (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    planarPolynomialLocalization b r q f z=(polynomialWeight b r q z.2:ℂ) • f z :=
  SchwartzMap.smulLeftCLM_apply_apply (transversePolynomial_temperate b r q) f z

theorem planarPolynomialLocalization_norm (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    ‖planarPolynomialLocalization b r q f z‖=polynomialWeight b r q z.2*‖f z‖ := by
  rw [planarPolynomialLocalization_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ((polynomialWeight_one_le b r q z.2).trans' (by norm_num))]

theorem planarPolynomialLocalization_horizontal (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
    vectorHorizontalSlice (planarPolynomialLocalization b r q f) y=
      (polynomialWeight b r q y:ℂ) • vectorHorizontalSlice f y := by
  ext x k
  simp only [vectorHorizontalSlice_apply,planarPolynomialLocalization_apply,smul_apply]

theorem planarPolynomialLocalization_vertical (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorVerticalSlice (planarPolynomialLocalization b r q f) x=
      vectorPolynomialLocalization b r q (vectorVerticalSlice f x) := by
  ext y k
  simp only [vectorVerticalSlice_apply,planarPolynomialLocalization_apply,vectorPolynomialLocalization_apply]

theorem planarPolynomialLocalization_horizontal_band (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (R : ℝ)
    (hf : ∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤R) :
    ∀ y ξ, 𝓕 (vectorHorizontalSlice (planarPolynomialLocalization b r q f) y) ξ≠0 → |ξ|≤R := by
  intro y ξ hne
  by_contra hn
  have hzero : 𝓕 (vectorHorizontalSlice f y) ξ=0 := by
    by_contra h
    exact hn (hf y ξ h)
  apply hne
  rw [planarPolynomialLocalization_horizontal,fourier_smul,smul_apply,hzero,smul_zero]

theorem planarPolynomialLocalization_vertical_band (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (R : ℝ)
    (hf : ∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤R) :
    ∀ x η, 𝓕 (vectorVerticalSlice (planarPolynomialLocalization b r q f) x) η≠0 → |η|≤R := by
  intro x η hne
  by_contra hn
  apply hne
  rw [planarPolynomialLocalization_vertical]
  apply vectorPolynomialLocalization_high b r q (vectorVerticalSlice f x) R _ η (lt_of_not_ge hn)
  intro ξ hξ
  by_contra h
  exact (not_le_of_gt hξ) (hf x ξ h)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedCellSupremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially weighted suprema on transverse tree cells. The bound
comes from coordinate Fourier support and the strong maximal estimate. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators FourierTransform ENNReal
namespace LipschitzHilbert

/-- A pointwise weighted comparison passes to the actual packet supremum. -/
theorem packetNormSup_weighted_le {X E ι : Type*} [NormedAddCommGroup E]
    (F G : ι → X → E) (Q : Set X) (c d B : ℝ)
    (hc : 0 < c) (hd : 0≤d) (hB : 0≤B)
    (hG : ∀ a x, x∈Q → ‖G a x‖≤B)
    (hFG : ∀ a x, x∈Q → c*‖F a x‖≤d*‖G a x‖) :
    c*packetNormSup F Q≤d*packetNormSup G Q := by
  have hGb := packetNormValues_bddAbove G Q B hB hG
  have hG0 := packetNormSup_nonneg G Q B hB hG
  have hs : packetNormSup F Q≤d*packetNormSup G Q/c := by
    apply packetNormSup_le F Q _ (div_nonneg (mul_nonneg hd hG0) hc.le)
    intro a x hx
    apply (le_div_iff₀ hc).mpr
    have hv : ‖G a x‖≤packetNormSup G Q :=
      le_csSup hGb (Or.inr ⟨a,x,hx,rfl⟩)
    simpa only [mul_comm c] using (hFG a x hx).trans (mul_le_mul_of_nonneg_left hv hd)
  simpa only [mul_comm c] using (le_div_iff₀ hc).mp hs

variable {J ι κ : Type*} [Fintype κ]

/-- The polynomial power on each transverse cell is paid for by the
energy of the polynomially localized packet family, uniformly in the
number of cells and packets. -/
theorem finite_weighted_box_supremum_energy
    (s : Finset J) (Kx Ky : SchwartzMap ℝ ℂ)
    (F : J → ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ))
    (q : ℕ) (b W Rx Ry : ℝ) (hW : 0<W) (cx rx n : J → ℝ)
    (hrx : ∀ j∈s, 0 < rx j)
    (hKx : ∀ ξ, |ξ|≤Rx → 𝓕 Kx ξ=1) (hKy : ∀ η, |η|≤Ry → 𝓕 Ky η=1)
    (hFx : ∀ j∈s, ∀ a y ξ, 𝓕 (vectorHorizontalSlice (F j a) y) ξ≠0 → |ξ|≤Rx/rx j)
    (hFy : ∀ j∈s, ∀ a x η, 𝓕 (vectorVerticalSlice (F j a) x) η≠0 → |η|≤Ry/(W/2))
    (A : J → Set (ℝ×ℝ)) (hA : ∀ j∈s, MeasurableSet (A j))
    (hAfin : ∀ j∈s, (volume.prod volume) (A j)≠∞)
    (hsub : ∀ j∈s, A j⊆coordinateBox (cx j) (b+n j*W) (rx j) (W/2))
    (hdisj : Set.Pairwise (↑s) (Disjoint on A))
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ p, 0≤U p) (hUb : ∀ p, ‖U p‖≤B)
    (hFU : ∀ j∈s, ∀ a p, polynomialWeight b (2*W) q p.2*‖F j a p‖≤U p) :
    (∑ j∈s, (1+|n j|)^(4*q)*
      (packetNormSup (fun a z => F j a z)
        (coordinateBox (cx j) (b+n j*W) (rx j) (W/2)))^2*
          (volume.prod volume).real (A j))≤
      32^(2*q)*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*
        (1296*∫ p, (U p)^2 ∂volume.prod volume) := by
  let G := fun j a => planarPolynomialLocalization b (2*W) q (F j a)
  let Q := fun j => coordinateBox (cx j) (b+n j*W) (rx j) (W/2)
  have hGU : ∀ j∈s, ∀ a p, ‖G j a p‖≤U p := by
    intro j hj a p
    exact (planarPolynomialLocalization_norm b (2*W) q (F j a) p).trans_le (hFU j hj a p)
  have hGb : ∀ j∈s, ∀ a p, ‖G j a p‖≤B := by
    intro j hj a p
    exact (hGU j hj a p).trans ((le_abs_self (U p)).trans (hUb p))
  have hFG : ∀ j∈s, ∀ a p, ‖F j a p‖≤‖G j a p‖ := by
    intro j hj a p
    rw [planarPolynomialLocalization_norm]
    exact le_mul_of_one_le_left (norm_nonneg _) (polynomialWeight_one_le b (2*W) q p.2)
  have hcell (j : J) (hj : j∈s) :
      (1+|n j|)^(4*q)*(packetNormSup (fun a z => F j a z) (Q j))^2≤
        32^(2*q)*(packetNormSup (fun a z => G j a z) (Q j))^2 := by
    have hpoint (a : ι) (p : ℝ×ℝ) (hp : p∈Q j) :
        (1+|n j|)^(2*q)*‖F j a p‖≤32^q*‖G j a p‖ := by
      have hy : |p.2-b-n j*W|≤W/2 := by
        simpa only [sub_add_eq_sub_sub] using hp.2
      rw [planarPolynomialLocalization_norm]
      have h := mul_le_mul_of_nonneg_right
        (transverse_cell_polynomial_weight b W (n j) p.2 q hW hy) (norm_nonneg (F j a p))
      simpa only [mul_assoc] using h
    have hs := packetNormSup_weighted_le (fun a z => F j a z) (fun a z => G j a z)
      (Q j) ((1+|n j|)^(2*q)) (32^q) B (by positivity) (by positivity) hB
      (fun a p _ => hGb j hj a p) hpoint
    have hF0 := packetNormSup_nonneg (fun a z => F j a z) (Q j) B hB
      (fun a p _ => (hFG j hj a p).trans (hGb j hj a p))
    have hs2 := pow_le_pow_left₀ (mul_nonneg (by positivity) hF0) hs 2
    simp only [mul_pow,←pow_mul] at hs2
    convert hs2 using 1 <;> first | (with_reducible_and_instances rfl) | (congr 2 <;> omega)
  have he := finite_box_supremum_energy s Kx Ky G Rx Ry cx (fun j => b+n j*W)
    rx (fun _ => W/2) hrx (fun _ _ => by positivity) hKx hKy
    (fun j hj a => planarPolynomialLocalization_horizontal_band b (2*W) q (F j a)
      (Rx/rx j) (hFx j hj a))
    (fun j hj a => planarPolynomialLocalization_vertical_band b (2*W) q (F j a)
      (Ry/(W/2)) (hFy j hj a))
    A hA hAfin hsub hdisj U hUm hU2 B hB hU0 hUb hGU
  calc
    _ ≤ ∑ j∈s, 32^(2*q)*(packetNormSup (fun a z => G j a z) (Q j))^2*
        (volume.prod volume).real (A j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcell j hj) (measureReal_nonneg)
    _ = 32^(2*q)*∑ j∈s, (packetNormSup (fun a z => G j a z) (Q j))^2*
        (volume.prod volume).real (A j) := by rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by positivity : 0≤(32:ℝ)^(2*q))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenCellIntegral
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual frozen long sums are measurable, have finite cell suprema,
and integrate against the original common angular-support mask. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

/-- A bounded measurable function on a finite cell integrates over its
mask with the exact mass of the intersection. -/
theorem masked_cell_norm_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (C A : Set X) (hC : MeasurableSet C) (hA : MeasurableSet A)
    (hfin : μ C≠∞) (f : X → E) (hf : AEStronglyMeasurable f μ)
    (M : ℝ) (hbound : ∀ z∈C, ‖f z‖≤M) :
    IntegrableOn (A.indicator f) C μ ∧
      (∫ z in C, ‖A.indicator f z‖ ∂μ)≤M*μ.real (C∩A) := by
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hfin
  have hpoint (z : X) (hz : z∈C) :
      ‖A.indicator f z‖≤A.indicator (fun _ => M) z := by
    by_cases ha : z∈A
    · simp only [indicator_of_mem ha]
      exact hbound z hz
    · simp only [indicator_of_notMem ha,norm_zero,le_refl]
  have hi : IntegrableOn (A.indicator f) C μ := by
    apply ((integrable_const M).indicator hA).mono' ((hf.indicator hA).restrict)
    filter_upwards [ae_restrict_mem hC] with z hz
    exact hpoint z hz
  refine ⟨hi,?_⟩
  have hle := integral_mono_ae hi.norm ((integrable_const M).indicator hA)
    (by filter_upwards [ae_restrict_mem hC] with z hz; exact hpoint z hz)
  apply hle.trans_eq
  rw [integral_indicator hA,integral_const]
  simp only [measureReal_def,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter,Measure.restrict_apply hA]
  rw [Set.inter_comm,mul_comm]

namespace SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem physicalLongInterval_uniform_bound (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    ∃ B : ℝ, 0≤B ∧ ∀ r lo hi z, ‖P.physicalLongIntervalSchwartz t r c lo hi z‖≤B := by
  let v : Fin (N+1) → ℝ := fun n =>
    SchwartzMap.seminorm ℝ 0 0 (P.physicalTreePartialSchwartz t c n)
  let S := ∑ n, v n
  have hv (n : Fin (N+1)) : 0≤v n := apply_nonneg _ _
  have hS : 0≤S := Finset.sum_nonneg (fun n _ => hv n)
  have hb (n : ℕ) (hn : n≤N) (z : ℝ×ℝ) : ‖P.physicalTreePartialSchwartz t c n z‖≤S := by
    have hn' : n<N+1 := by omega
    have hsingle := Finset.single_le_sum (f:=v) (fun n _ => hv n)
      (Finset.mem_univ (⟨n,hn'⟩ : Fin (N+1)))
    exact (SchwartzMap.norm_le_seminorm ℝ (P.physicalTreePartialSchwartz t c n) z).trans hsingle
  refine ⟨2*S,by positivity,?_⟩
  intro r lo hi z
  rw [physicalLongIntervalSchwartz,sub_apply]
  exact (norm_sub_le _ _).trans (by
    have hhi := hb (min hi (P.longPrefix r)) ((min_le_right _ _).trans (P.longPrefix_le r)) z
    have hlo := hb (min lo (P.longPrefix r)) ((min_le_right _ _).trans (P.longPrefix_le r)) z
    linarith)

theorem longCellSup_nonneg
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (b : ℝ) (p : (ℤ×ℤ)×ℤ) :
    0≤P.longCellSup c b p := by
  obtain ⟨B,hB,hbound⟩ := P.physicalLongInterval_uniform_bound 0 c
  exact packetNormSup_nonneg _ _ B hB (fun a z _ => hbound _ a.1 a.2 z)

theorem frozenLongValue_measurable (t r w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (fun z => P.frozenLongValue t r w (u z) c z) := by
  unfold frozenLongValue
  apply Finset.measurable_sum
  intro j _
  by_cases hj : 32*r<P.length j
  · simp only [hj,true_and]
    have hset : MeasurableSet {z | |u z-t|≤w/P.length j} :=
      measurableSet_le (show Measurable (fun z => |u z-t|) by fun_prop) measurable_const
    have hc := (planarSynthesisSchwartz
      (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
      (fun a k => P.physicalPacket t j a.1 a.2 k)).continuous.measurable
    have hc' : Measurable (fun z => planarFixedSynthesis
        (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
        (fun a k => P.physicalPacket t j a.1 a.2 k) z) := by
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      exact (planarSynthesisSchwartz_apply _ _ z).symm
    exact Measurable.ite hset hc' measurable_const
  · simp only [hj,false_and,ite_false, if_false]
    exact measurable_const

/-- Pointwise interval extraction controls the actual variable frozen
selector on every half-open cell. -/
theorem frozenLongValue_le_cell_sup (w : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (b : ℝ) (p : (ℤ×ℤ)×ℤ) {z : ℝ×ℝ}
    (hz : z∈partitionCell b P.width p) :
    ‖P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z‖≤P.longCellSup c b p := by
  obtain ⟨B,hB,hbound⟩ := P.physicalLongInterval_uniform_bound 0 c
  apply le_csSup (packetNormValues_bddAbove _ _ B hB (fun a x _ => hbound _ a.1 a.2 x))
  refine Or.inr ⟨(P.angularStart w |u z-0|,N),z,partitionCell_subset_box b P.width p hz,?_⟩
  rw [P.frozenLongValue_eq_interval 0 _ w (u z) hw c z]

theorem frozen_cell_integral (w : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (b : ℝ) (p : (ℤ×ℤ)×ℤ)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) :
    IntegrableOn (A.indicator (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z))
      (partitionCell b P.width p) (volume.prod volume) ∧
    (∫ z in partitionCell b P.width p,
      ‖A.indicator (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z) z‖
        ∂volume.prod volume)≤
      P.longCellSup c b p*(volume.prod volume).real (partitionCell b P.width p∩A) :=
  masked_cell_norm_integral (volume.prod volume) _ A (partitionCell_measurable b P.width p)
    hA (partitionCell_finite b P.width p) _ (P.frozenLongValue_measurable 0 _ w c u hu).aestronglyMeasurable
    (P.longCellSup c b p)
    (fun _ hz => P.frozenLongValue_le_cell_sup w hw c u b p hz)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWhitneyGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue stripwise estimates over the actual countable Whitney partition.
Finite-subfamily bounds imply integrability and the same global bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)

variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

theorem indexAt_mem (z : ℝ) :
    z∈cell 0 (indexAt tiles x ell hne hpos z).val.1 (indexAt tiles x ell hne hpos z).val.2 :=
  Classical.choose_spec (exists_cellIndex tiles x ell hne hpos z)

theorem indexAt_eq_of_mem (i : CellIndex tiles x ell) {z : ℝ}
    (hz : z∈cell 0 i.val.1 i.val.2) : indexAt tiles x ell hne hpos z=i := by
  apply Subtype.ext
  by_contra hne'
  exact Set.disjoint_left.mp
    (whitney_disjoint tiles x ell (indexAt tiles x ell hne hpos z).property i.property hne')
    (indexAt_mem tiles x ell hne hpos z) hz

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLongCellMask
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent-witness density test supplies the common mask and
mass bounds on the disjoint cells used in long-tree integration. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem long_cell_scale_le_top (i : P.DensityWhitneyCell) (hi : P.HasLongPacket i) :
    DyadicLineGrid.scale i.val.1≤P.topLength := by
  obtain ⟨q,hq⟩ := hi
  have hl : P.length q.1≤P.topLength :=
    div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  linarith [DyadicLineGrid.scale_pos i.val.1]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceWeightedTreeMajorant
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual polynomially weighted tree maximum is a bounded
measurable majorant. Its L2 energy is inherited from the stronger product
weight, without adding a maximal-function premise. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem transverseTreeMajorant_nonneg (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    0≤P.transverseTreeMajorant b q c z :=
  mul_nonneg ((polynomialWeight_one_le b (2*P.width) q z.2).trans' (by norm_num))
    (intervalOscillation_nonneg _ _ _ _)

theorem transverseTreeMajorant_continuous (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Continuous (P.transverseTreeMajorant b q c) := by
  have hw : Continuous (fun z : ℝ×ℝ => polynomialWeight b (2*P.width) q z.2) := by
    unfold polynomialWeight
    fun_prop
  exact hw.mul (P.physicalTreeMaximal_continuous 0 c)

/-- Boundedness is obtained from the finitely many actual weighted
Schwartz partial sums; the bound is needed only for representatives. -/
theorem transverseTreeMajorant_bounded (b : ℝ) (q : ℕ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    ∃ B : ℝ, 0≤B ∧ ∀ z, ‖P.transverseTreeMajorant b q c z‖≤B := by
  let f := fun n : Fin (N+1) =>
    planarPolynomialLocalization b (2*P.width) q (P.physicalTreePartialSchwartz 0 c n)
  let v := fun n : Fin (N+1) => SchwartzMap.seminorm ℝ 0 0 (f n)
  let S := ∑ n, v n
  have hv (n : Fin (N+1)) : 0≤v n := apply_nonneg _ _
  have hS : 0≤S := Finset.sum_nonneg (fun n _ => hv n)
  have hb (n : ℕ) (hn : n≤N) (z : ℝ×ℝ) :
      polynomialWeight b (2*P.width) q z.2*‖P.physicalTreePartial 0 c n z‖≤S := by
    have hn' : n<N+1 := by omega
    have hs := Finset.single_le_sum (f:=v) (fun n _ => hv n)
      (Finset.mem_univ (⟨n,hn'⟩ : Fin (N+1)))
    have hnrm := SchwartzMap.norm_le_seminorm ℝ (f ⟨n,hn'⟩) z
    rw [planarPolynomialLocalization_norm,physicalTreePartialSchwartz_apply] at hnrm
    exact hnrm.trans hs
  refine ⟨2*S,by positivity,?_⟩
  intro z
  obtain ⟨lo,hi,_hlo,horder,hhi,hmax⟩ :=
    exists_intervalOscillation_eq (fun n => P.physicalTreePartial 0 c n z) N 0 N (Nat.zero_le _)
  have hlow := hb lo (horder.trans hhi) z
  have hhigh := hb hi hhi z
  rw [Real.norm_eq_abs,abs_of_nonneg (P.transverseTreeMajorant_nonneg b q c z)]
  change polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z≤2*S
  change P.physicalTreeMaximal 0 c z=_ at hmax
  rw [hmax]
  have hp : 0≤polynomialWeight b (2*P.width) q z.2 :=
    (polynomialWeight_one_le b (2*P.width) q z.2).trans' (by norm_num)
  calc
    _ ≤ polynomialWeight b (2*P.width) q z.2*
        (‖P.physicalTreePartial 0 c hi z‖+‖P.physicalTreePartial 0 c lo z‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp
    _ ≤ _ := by rw [mul_add]; linarith

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTreeCellGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable gluing on the actual horizontal Whitney cells and
half-open transverse cells. A finite rectangle bound suffices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

theorem productCell_measurable (b W : ℝ) (i : ProductCellIndex tiles x ell) :
    MeasurableSet (productCell tiles x ell b W i) := partitionCell_measurable b W _

theorem productCell_disjoint (b W : ℝ) (hW : 0<W) :
    Pairwise (fun i j : ProductCellIndex tiles x ell =>
      Disjoint (productCell tiles x ell b W i) (productCell tiles x ell b W j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  by_cases he : i.1=j.1
  · have hn : i.2≠j.2 := by
      intro hn
      exact hij (Prod.ext he hn)
    exact Set.disjoint_left.mp (transverseCell_disjoint b W hW hn) hzi.2 hzj.2
  · have hv : i.1.val≠j.1.val := fun h => he (Subtype.ext h)
    exact Set.disjoint_left.mp
      (whitney_disjoint tiles x ell i.1.property j.1.property hv) hzi.1 hzj.1

include hne hpos in
theorem productCell_iUnion (b W : ℝ) (hW : 0<W) :
    (⋃ i : ProductCellIndex tiles x ell, productCell tiles x ell b W i)=univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i,hi⟩ := exists_cellIndex tiles x ell hne hpos z.1
  exact mem_iUnion.mpr ⟨(i,⌊(z.2-b)/W+1/2⌋),hi,mem_transverseCell_floor b W z.2 hW⟩

variable {V : Type*} [NormedAddCommGroup V]

/-- Any finite collection is dominated by its finite rectangle of
horizontal and transverse indices. -/
theorem product_finite_bound
    (F : ProductCellIndex tiles x ell → ℝ) (hF : ∀ i, 0≤F i) (C : ℝ)
    (hrect : ∀ (S : Finset (CellIndex tiles x ell)) (T : Finset ℤ),
      (∑ i∈S×ˢT, F i)≤C) (A : Finset (ProductCellIndex tiles x ell)) :
    (∑ i∈A, F i)≤C := by
  classical
  apply le_trans _ (hrect (A.image Prod.fst) (A.image Prod.snd))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩
  · intro i _ _
    exact hF i

/-- Integrability of the pasted function follows from the proved local
integrals and their uniform finite-rectangle bound. -/
theorem product_paste_integrable_bound (b W : ℝ) (hW : 0<W)
    (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (hF : ∀ i : ProductCellIndex tiles x ell,
      IntegrableOn (F i.1) (productCell tiles x ell b W i) (volume.prod volume))
    (C : ℝ) (hrect : ∀ (S : Finset (CellIndex tiles x ell)) (T : Finset ℤ),
      (∑ i∈S×ˢT, ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume)≤C) :
    Integrable (paste tiles x ell hne hpos F) (volume.prod volume) ∧
      (∫ z, ‖paste tiles x ell hne hpos F z‖ ∂volume.prod volume)≤C := by
  let G := paste tiles x ell hne hpos F
  have heq (i : ProductCellIndex tiles x ell) {z : ℝ×ℝ}
      (hz : z∈productCell tiles x ell b W i) : G z=F i.1 z := by
    dsimp [G,paste]
    rw [indexAt_eq_of_mem tiles x ell hne hpos i.1 hz.1]
  have hlocal (i : ProductCellIndex tiles x ell) :
      IntegrableOn G (productCell tiles x ell b W i) (volume.prod volume) :=
    (hF i).congr_fun (fun z hz => (heq i hz).symm) (productCell_measurable tiles x ell b W i)
  have hint (i : ProductCellIndex tiles x ell) :
      (∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume)=
        ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume :=
    setIntegral_congr_fun (productCell_measurable tiles x ell b W i)
      (fun _ hz => congrArg norm (heq i hz))
  have hbound (A : Finset (ProductCellIndex tiles x ell)) :
      (∑ i∈A, ∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume)≤C := by
    simpa only [hint] using product_finite_bound tiles x ell
      (fun i => ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume)
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) C hrect A
  have hs : Summable (fun i : ProductCellIndex tiles x ell =>
      ∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume) :=
    summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  have hi := integrableOn_iUnion_of_summable_integral_norm hlocal hs
  rw [productCell_iUnion tiles x ell hne hpos b W hW,integrableOn_univ] at hi
  refine ⟨hi,?_⟩
  have hpart := integral_iUnion (μ:=volume.prod volume) (f:=fun z => ‖G z‖)
    (productCell_measurable tiles x ell b W) (productCell_disjoint tiles x ell b W hW)
    hi.norm.integrableOn
  rw [productCell_iUnion tiles x ell hne hpos b W hW,setIntegral_univ] at hpart
  rw [hpart]
  exact Real.tsum_le_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound

end LipschitzHilbert.SourceWhitney

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceVerticalDemodulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing each vertical bin carrier is an exact pointwise isometry.
Box reproduction can therefore use the narrow demodulated spectra. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {κ : Type*} [Fintype κ]

theorem verticalCarrier_temperate (nu : ℝ) : Function.HasTemperateGrowth (verticalCarrier nu) := by
  change Function.HasTemperateGrowth (fun z : ℝ×ℝ => Complex.exp ((nu*z.2 : ℝ)*Complex.I))
  simpa only [sub_zero,zero_mul] using physicalPacketCarrier_temperate 0 0 0 nu

@[simp] theorem verticalDemodulation_apply (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) (k : κ) :
    verticalDemodulation nu f z k=verticalCarrier (-nu k) z*f z k := by
  rw [verticalDemodulation,vectorSchwartz_apply,
    SchwartzMap.smulLeftCLM_apply_apply (verticalCarrier_temperate (-nu k))]
  rfl

@[simp] theorem verticalDemodulation_norm (nu : κ → ℝ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    ‖verticalDemodulation nu f z‖=‖f z‖ := by
  have h : ‖verticalDemodulation nu f z‖^2=‖f z‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,verticalDemodulation_apply,norm_mul,
      verticalCarrier_norm,one_mul]
  nlinarith [norm_nonneg (verticalDemodulation nu f z),norm_nonneg (f z)]

@[simp] theorem scalarVerticalDemodulation_apply (nu : ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    scalarVerticalDemodulation nu f z=verticalCarrier (-nu) z*f z := by
  exact SchwartzMap.smulLeftCLM_apply_apply (verticalCarrier_temperate (-nu)) f z

@[simp] theorem verticalDemodulation_zero (nu : κ → ℝ) :
    verticalDemodulation nu 0=0 := by
  ext z k
  simp

@[simp] theorem verticalDemodulation_sub (nu : κ → ℝ)
    (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    verticalDemodulation nu (f-g)=verticalDemodulation nu f-verticalDemodulation nu g := by
  ext z k
  simp [mul_sub]

@[simp] theorem verticalDemodulation_sum {J : Type*} (nu : κ → ℝ) (s : Finset J)
    (f : J → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    verticalDemodulation nu (∑ j∈s, f j)=∑ j∈s, verticalDemodulation nu (f j) := by
  ext z k
  simp [sum_apply,WithLp.ofLp_sum,Finset.sum_apply,Finset.mul_sum]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDemodulatedFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact translation of the angular Fourier transform when the
vertical bin carrier is removed. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem planarAngularFourier_vertical_demodulation (f : ℝ×ℝ → ℂ) (nu xi eta : ℝ) :
    planarAngularFourier (fun z => verticalCarrier (-nu) z*f z) (xi,eta)=
      planarAngularFourier f (xi,eta+nu) := by
  simp only [planarAngularFourier_eq_integral,verticalCarrier]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  push_cast
  ring

/-- A bin of width proportional to 1/W becomes a low vertical-frequency
band; the horizontal bound still uses w and cancels its slope factor. -/
theorem demodulated_packet_bands
    (f : ℝ×ℝ → ℂ) (nu theta ell W w cStar CEta Cb Cv : ℝ)
    (hell : 0<ell) (hw : 0<w) (hCb : 0≤Cb)
    (hslope : |theta|≤Cb*w/ell)
    (hspectrum : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta| ≤ cStar/ell ∧ |eta|≤CEta/w)
    (hbin : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 → |eta-nu|≤Cv/W) :
    ∀ xi eta, planarAngularFourier (fun z => verticalCarrier (-nu) z*f z) (xi,eta)≠0 →
      |xi|≤(cStar+Cb*CEta)/ell ∧ |eta|≤Cv/W := by
  intro xi eta hne
  rw [planarAngularFourier_vertical_demodulation] at hne
  obtain ⟨hx,hy⟩ := hspectrum xi (eta+nu) hne
  have hv := hbin xi (eta+nu) hne
  constructor
  · calc
      |xi| = |(xi+theta*(eta+nu))-theta*(eta+nu)| := by ring_nf
      _ ≤ |xi+theta*(eta+nu)|+|theta*(eta+nu)| := abs_sub _ _
      _ ≤ cStar/ell+(Cb*w/ell)*(CEta/w) :=
        add_le_add hx (by rw [abs_mul]; exact mul_le_mul hslope hy (abs_nonneg _) (by positivity))
      _ = _ := by field_simp
  · simpa only [add_sub_cancel_right] using hv

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDemodulatedSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate cutoffs for the actual packet sums after removing each
bin's common vertical carrier. -/
noncomputable section
open FourierTransform
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem verticalDemodulation_synthesis (nu : κ → ℝ)
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap (ℝ×ℝ) ℂ) :
    verticalDemodulation nu (planarSynthesisSchwartz c f)=
      planarSynthesisSchwartz c (fun i k => scalarVerticalDemodulation (nu k) (f i k)) := by
  ext z k
  simp [planarSynthesisSchwartz,Finset.mul_sum,mul_left_comm]

theorem scalarVerticalDemodulation_bands (f : SchwartzMap (ℝ×ℝ) ℂ)
    (nu theta ell W w cStar CEta Cb Cv : ℝ)
    (hell : 0<ell) (hw : 0<w) (hCb : 0≤Cb)
    (hslope : |theta|≤Cb*w/ell)
    (hspectrum : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 →
      |xi+theta*eta| ≤ cStar/ell ∧ |eta|≤CEta/w)
    (hbin : ∀ xi eta, planarAngularFourier f (xi,eta)≠0 → |eta-nu|≤Cv/W) :
    (∀ y xi, 𝓕 (planarSchwartzSlice (scalarVerticalDemodulation nu f) y 0) xi≠0 →
      |xi|≤((cStar+Cb*CEta)/ell)/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (planarVerticalSlice (scalarVerticalDemodulation nu f) x) eta≠0 →
      |eta|≤(Cv/W)/(2*Real.pi)) := by
  have h := planarAngularFourier_coordinate_bands (scalarVerticalDemodulation nu f)
    ((cStar+Cb*CEta)/ell) (Cv/W) (by
      have heq : (scalarVerticalDemodulation nu f : (ℝ×ℝ) → ℂ)=
          fun z => verticalCarrier (-nu) z*f z := by
        funext z
        exact scalarVerticalDemodulation_apply nu f z
      rw [heq]
      exact demodulated_packet_bands f nu theta ell W w cStar CEta Cb Cv hell hw hCb
          hslope hspectrum hbin)
  exact ⟨planarHorizontalSlice_fourier_band _ _ (fun xi eta hn => (h xi eta hn).1),
    planarVerticalSlice_fourier_band _ _ (fun xi eta hn => (h xi eta hn).2)⟩

namespace SourceLabeledLattice
variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem physicalTreePartialSchwartz_demodulated_bands
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (n : ℕ) (r w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ)
    (hr : 0 < r) (hw : 0<w) (hcStar : 0 ≤ cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hlen : ∀ j : Fin N, j.val<n → r≤P.length j)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ |eta|≤CEta/w)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |eta-nu k|≤Cv/P.width) :
    (∀ y xi, 𝓕 (vectorHorizontalSlice
      (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c n)) y) xi≠0 →
      |xi|≤((cStar+Cb*CEta)/r)/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (vectorVerticalSlice
      (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c n)) x) eta≠0 →
      |eta|≤(Cv/P.width)/(2*Real.pi)) := by
  unfold physicalTreePartialSchwartz
  rw [verticalDemodulation_sum]
  apply vector_sum_bands
  intro j _
  by_cases hj : j.val<n
  · rw [ite_eq_left hj,verticalDemodulation_synthesis]
    apply planarSynthesisSchwartz_coordinate_bands
    · intro a k _ y xi hxi
      have h := (scalarVerticalDemodulation_bands (P.physicalPacket 0 j a.1 a.2 k)
        (nu k) (P.rowSlope j a.1) (P.length j) P.width w cStar CEta Cb Cv
        (P.length_pos j) hw hCb (hslope j a.1) (hspectrum j a.1 a.2 k)
        (hbin j a.1 a.2 k)).1 y xi hxi
      exact h.trans (div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hr (hlen j hj)) (by positivity))
    · intro a k _
      exact (scalarVerticalDemodulation_bands (P.physicalPacket 0 j a.1 a.2 k)
        (nu k) (P.rowSlope j a.1) (P.length j) P.width w cStar CEta Cb Cv
        (P.length_pos j) hw hCb (hslope j a.1) (hspectrum j a.1 a.2 k)
        (hbin j a.1 a.2 k)).2
  · rw [ite_eq_right hj,verticalDemodulation_zero]
    have hx (y : ℝ) : vectorHorizontalSlice (0 : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) y=0 := by
      ext x k
      rfl
    have hy (x : ℝ) : vectorVerticalSlice (0 : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) x=0 := by
      ext y k
      rfl
    simp only [hx,hy,FourierTransform.fourier_zero,zero_apply,ne_eq,not_true_eq_false,
      IsEmpty.forall_iff,and_self,forall_const]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDemodulatedLong
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Narrow-bin reproduction for actual long intervals. The transverse
weight and all physical cells retain their original spatial width. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert
variable {κ : Type} [Fintype κ]

theorem packetNormSup_verticalDemodulation {ι : Type*} (nu : κ → ℝ)
    (F : ι → SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (Q : Set (ℝ×ℝ)) :
    packetNormSup (fun a z => verticalDemodulation nu (F a) z) Q=
      packetNormSup (fun a z => F a z) Q := by
  simp only [packetNormSup,packetNormValues,verticalDemodulation_norm]

namespace SourceLabeledLattice
variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalLongIntervalSchwartz_demodulated_bands
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lo hi : ℕ) (r w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ)
    (hr : 0 < r) (hw : 0<w) (hcStar : 0 ≤ cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |xi+P.rowSlope j l*eta| ≤ cStar/P.length j ∧ |eta|≤CEta/w)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
      |eta-nu k|≤Cv/P.width) :
    (∀ y xi, 𝓕 (vectorHorizontalSlice
      (verticalDemodulation nu (P.physicalLongIntervalSchwartz 0 r c lo hi)) y) xi≠0 →
      |xi|≤((cStar+Cb*CEta)/r)/(2*Real.pi)) ∧
    (∀ x eta, 𝓕 (vectorVerticalSlice
      (verticalDemodulation nu (P.physicalLongIntervalSchwartz 0 r c lo hi)) x) eta≠0 →
      |eta|≤(Cv/P.width)/(2*Real.pi)) := by
  have hp (n : ℕ) := P.physicalTreePartialSchwartz_demodulated_bands c (min n (P.longPrefix r))
    r w cStar CEta Cb Cv nu hr hw hcStar hCEta hCb (by
      intro j hj
      have hl := (P.longPrefix_spec r j).mp (hj.trans_le (min_le_right _ _))
      linarith) hspectrum hslope hbin
  have hx (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
      vectorHorizontalSlice (f-g) y=vectorHorizontalSlice f y-vectorHorizontalSlice g y := by
    ext x k
    rfl
  have hy (f g : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
      vectorVerticalSlice (f-g) x=vectorVerticalSlice f x-vectorVerticalSlice g x := by
    ext y k
    rfl
  constructor
  · intro y xi hne
    by_contra hn
    apply hne
    rw [physicalLongIntervalSchwartz,verticalDemodulation_sub,hx]
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,add_apply,neg_apply]
    have hz (n : ℕ) : 𝓕 (vectorHorizontalSlice
        (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c (min n (P.longPrefix r)))) y) xi=0 := by
      by_contra h
      exact hn ((hp n).1 y xi h)
    rw [hz,hz,neg_zero,add_zero]
  · intro x eta hne
    by_contra hn
    apply hne
    rw [physicalLongIntervalSchwartz,verticalDemodulation_sub,hy]
    simp only [sub_eq_add_neg,FourierTransform.fourier_add,FourierTransform.fourier_neg,add_apply,neg_apply]
    have hz (n : ℕ) : 𝓕 (vectorVerticalSlice
        (verticalDemodulation nu (P.physicalTreePartialSchwartz 0 c (min n (P.longPrefix r)))) x) eta=0 := by
      by_contra h
      exact hn ((hp n).2 x eta h)
    rw [hz,hz,neg_zero,add_zero]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceDemodulatedCellEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Long-cell energy with constants independent of the carrier locations
and of the ratio between spatial and angular widths. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators FourierTransform ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem finite_demodulated_long_cell_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (s : Finset ((ℤ×ℤ)×ℤ)) (b : ℝ) (q : ℕ)
    (hWhitney : ∀ p∈s, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun a => P.actualX a.1 a.2.1 a.2.2) (fun a => P.length a.1) p.1.1 p.1.2)
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0 ≤ cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l u k ξ η, planarAngularFourier (P.physicalPacket 0 j l u k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l u k ξ η, planarAngularFourier (P.physicalPacket 0 j l u k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (U : ℝ×ℝ → ℝ) (hUm : Measurable U) (hU2 : MemLp U 2 (volume.prod volume))
    (B : ℝ) (hB : 0≤B) (hU0 : ∀ z, 0≤U z) (hUb : ∀ z, ‖U z‖≤B)
    (hU : ∀ z, polynomialWeight b (2*P.width) q z.2*P.physicalTreeMaximal 0 c z≤U z) :
    (∑ p∈s, (1+|(p.2:ℝ)|)^(4*q)*
      (packetNormSup (fun a : ℕ×ℕ => P.physicalLongIntervalSchwartz 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2)
        (coordinateBox (center p.1.1 p.1.2) (b+(p.2:ℝ)*P.width)
          (DyadicLineGrid.scale p.1.1/2) (P.width/2)))^2*(DyadicLineGrid.scale p.1.1*P.width))≤
      32^(2*q)*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*
        (1296*∫ z, (U z)^2 ∂volume.prod volume) := by
  let F := fun (p : (ℤ×ℤ)×ℤ) (a : ℕ×ℕ) =>
    P.physicalLongIntervalSchwartz 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2
  have hband (p : (ℤ×ℤ)×ℤ) (a : ℕ×ℕ) :=
    P.physicalLongIntervalSchwartz_demodulated_bands c a.1 a.2 (DyadicLineGrid.scale p.1.1) w
      cStar CEta Cb Cv nu (scale_pos _) hw hcStar hCEta hCb hspectrum hselector hbin
  have hFx : ∀ p∈s, ∀ a y ξ, 𝓕 (vectorHorizontalSlice (verticalDemodulation nu (F p a)) y) ξ≠0 →
      |ξ|≤((cStar+Cb*CEta)/(4*Real.pi))/(DyadicLineGrid.scale p.1.1/2) := by
    intro p _ a y ξ hξ
    have h := (hband p a).1 y ξ hξ
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp; ring)
  have hFy : ∀ p∈s, ∀ a x η, 𝓕 (vectorVerticalSlice (verticalDemodulation nu (F p a)) x) η≠0 →
      |η|≤(Cv/(4*Real.pi))/(P.width/2) := by
    intro p _ a x η hη
    have h := (hband p a).2 x η hη
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp; ring)
  have hFU : ∀ p∈s, ∀ a z, polynomialWeight b (2*P.width) q z.2*‖F p a z‖≤U z := by
    intro p _ a z
    apply le_trans _ (hU z)
    exact mul_le_mul_of_nonneg_left (P.physicalLongIntervalSchwartz_norm 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2 z)
      ((polynomialWeight_one_le b (2*P.width) q z.2).trans' (by norm_num))
  have h := finite_weighted_box_supremum_energy s Kx Ky (fun p a => verticalDemodulation nu (F p a)) q b P.width
    ((cStar+Cb*CEta)/(4*Real.pi)) (Cv/(4*Real.pi)) P.width_pos
    (fun p => center p.1.1 p.1.2) (fun p => DyadicLineGrid.scale p.1.1/2) (fun p => (p.2:ℝ))
    (fun p _ => div_pos (scale_pos _) (by norm_num)) hKx hKy hFx hFy (partitionCell b P.width)
    (fun p _ => partitionCell_measurable b P.width p)
    (fun p _ => partitionCell_finite b P.width p)
    (fun p _ => partitionCell_subset_box b P.width p)
    (partitionCell_disjoint (Finset.univ : Finset P.PacketIndex)
      (fun a => P.actualX a.1 a.2.1 a.2.2) (fun a => P.length a.1)
      b P.width P.width_pos (↑s) hWhitney)
    U hUm hU2 B hB hU0 hUb (by simpa only [verticalDemodulation_norm] using hFU)
  simpa only [packetNormSup_verticalDemodulation,partitionCell_area b P.width _ P.width_pos] using h


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularFrozenIntegration
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frozen long-tree integration keeps angular and spatial widths
separate. Carrier removal supplies uniform reproduction on spatial cells. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem finite_angular_frozen_density_integral
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (angularWidth : ℝ) (hangularWidth : 0≤angularWidth)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ) (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hWhitney : ∀ p∈S, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2)
    (hscale : ∀ p∈S, DyadicLineGrid.scale p.1≤P.topLength)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : ℤ×ℤ → Set ℝ)
    (hOmega : ∀ p∈S, MeasurableSet (Omega p))
    (hmass : ∀ p∈S×ˢT, (volume.prod volume).real
      (partitionCell b P.width p∩(E∩u ⁻¹' Omega p.1))≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*P.width)
    (henergy : (∑ p∈S×ˢT, (1+|(p.2:ℝ)|)^412*(P.longCellSup c b p)^2*
      (DyadicLineGrid.scale p.1.1*P.width))≤E0) :
    (∀ p∈S×ˢT, IntegrableOn
      ((E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) angularWidth (u z) c z))
      (partitionCell b P.width p) (volume.prod volume)) ∧
    (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) angularWidth (u z) c z) z‖
      ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*E0*(9*P.topLength*P.width*transverseTailConstant) := by
  let mask := fun p : (ℤ×ℤ)×ℤ => E∩u ⁻¹' Omega p.1
  let m := fun p : (ℤ×ℤ)×ℤ => DyadicLineGrid.scale p.1.1*P.width
  let d := fun p : (ℤ×ℤ)×ℤ => (volume.prod volume).real (partitionCell b P.width p∩mask p)
  let w := fun p : (ℤ×ℤ)×ℤ => 1+|(p.2:ℝ)|
  have hlocal (p : (ℤ×ℤ)×ℤ) (hp : p∈S×ˢT) :=
    P.frozen_cell_integral angularWidth hangularWidth c u hu b p (mask p)
      (hE.inter ((hOmega p.1 (Finset.mem_product.mp hp).1).preimage hu))
  refine ⟨fun p hp => (hlocal p hp).1,?_⟩
  have hsum : (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(mask p).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) angularWidth (u z) c z) z‖
      ∂volume.prod volume)≤∑ p∈S×ˢT, P.longCellSup c b p*d p :=
    Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
  have hene : (∑ p∈S×ˢT, (P.longCellSup c b p)^2*m p*(w p)^412)≤E0 := by
    convert henergy using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro p _
    dsimp [m,w]
    ac_rfl
  have hvol : (∑ p∈S×ˢT, m p/(w p)^6)≤9*P.topLength*P.width*transverseTailConstant :=
    finite_whitney_transverse_budget (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) a P.topLength P.width
      P.topLength_pos.le P.width_pos.le (fun q _ => hcenter q) S T hWhitney hscale
  have hb := finite_density_supremum_sum (S×ˢT) (P.longCellSup c b) d m w
    (32*(2:ℝ)^203*eta) E0 (9*P.topLength*P.width*transverseTailConstant)
    (fun p _ => P.longCellSup_nonneg c b p) (fun _ _ => measureReal_nonneg)
    (fun p _ => mul_nonneg (DyadicLineGrid.scale_pos _).le P.width_pos.le)
    (fun p _ => by dsimp [w]; positivity) hE0 (by
      intro p hp
      convert hmass p hp using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [m,w,d,mask]
      simp only [mul_assoc]) hene hvol
  apply le_trans _ hb
  apply pow_le_pow_left₀ _ hsum 2
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))


theorem finite_angular_frozen_long_tree_bound
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ) (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hWhitney : ∀ p∈S, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2)
    (hscale : ∀ p∈S, DyadicLineGrid.scale p.1≤P.topLength)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : ℤ×ℤ → Set ℝ)
    (hOmega : ∀ p∈S, MeasurableSet (Omega p))
    (hmass : ∀ p∈S×ˢT, (volume.prod volume).real
      (partitionCell b P.width p∩(E∩u ⁻¹' Omega p.1))≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*P.width)
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0 ≤ cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z) z‖
      ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant) := by
  let U := P.transverseTreeMajorant b 103 c
  have hUI : Integrable (fun z => U z^2) (volume.prod volume) := by
    simpa only [U,transverseTreeMajorant,mul_pow] using hI
  have hU2 : (∫ z, U z^2 ∂volume.prod volume)≤E0 := by
    simpa only [U,transverseTreeMajorant,mul_pow] using hEnergy
  have hUmem : MemLp U 2 (volume.prod volume) :=
    (memLp_two_iff_integrable_sq
      (P.transverseTreeMajorant_continuous b 103 c).aestronglyMeasurable).mpr hUI
  obtain ⟨B,hB,hBound⟩ := P.transverseTreeMajorant_bounded b 103 c
  have he := P.finite_demodulated_long_cell_energy c (S×ˢT) b 103
    (fun p hp => hWhitney p.1 (Finset.mem_product.mp hp).1)
    w cStar CEta Cb Cv nu hw hcStar hCEta hCb hspectrum hselector hbin Kx Ky hKx hKy
    U (P.transverseTreeMajorant_continuous b 103 c).measurable hUmem B hB
    (P.transverseTreeMajorant_nonneg b 103 c) hBound (fun _ => le_rfl)
  let C := (32:ℝ)^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296
  have hC : 0≤C :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤32) 206) (sq_nonneg _))
      (by norm_num)
  have he' : (∑ p∈S×ˢT, (1+|(p.2:ℝ)|)^412*(P.longCellSup c b p)^2*
      (DyadicLineGrid.scale p.1.1*P.width))≤C*E0 := by
    have heq : (4*(103:ℕ))=412 := rfl
    have heq' : (2*(103:ℕ))=206 := rfl
    simp only [heq,heq'] at he
    apply he.trans
    simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hU2 hC
  exact (P.finite_angular_frozen_density_integral c w hw.le S T a b eta (C*E0) (mul_nonneg hC hE0)
    hcenter hWhitney hscale E hE u hu Omega hOmega hmass he').2


theorem frozenWhitneyLocalAtWidth_integrable (w : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (b : ℝ) (i : P.DensityWhitneyCell) (n : ℤ) :
    IntegrableOn (P.frozenWhitneyLocalAtWidth w c E u Omega i)
      (partitionCell b P.width (i.val,n)) (volume.prod volume) :=
  (P.frozen_cell_integral w hw c u hu b (i.val,n)
    (E∩u ⁻¹' Omega i) (hE.inter ((hOmega i).preimage hu))).1

private theorem angular_sum_subtype_product {α β : Type*} [DecidableEq α] {p : α → Prop}
    (S : Finset {a // p a}) (T : Finset β) (f : α×β → ℝ) :
    (∑ j∈S.image Subtype.val×ˢT, f j)=(∑ j∈S×ˢT, f (j.1.val,j.2)) := by
  classical
  rw [Finset.sum_product,Finset.sum_product,Finset.sum_image]
  intro i _ j _ h
  exact Subtype.ext h

theorem finite_angular_frozenWhitney_bound
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset P.DensityWhitneyCell) (T : Finset ℤ) (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hLong : ∀ i∈S, P.HasLongPacket i)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : P.DensityWhitneyCell → Set ℝ)
    (hOmega : ∀ i, MeasurableSet (Omega i))
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width)
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0 ≤ cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    (∑ j∈S×ˢT, ∫ z in partitionCell b P.width (j.1.val,j.2),
      ‖P.frozenWhitneyLocalAtWidth w c E u Omega j.1 z‖ ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant) := by
  classical
  let raw := S.image Subtype.val
  let O := P.extendWhitneyMask Omega
  have hW : ∀ p∈raw, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2 := by
    intro p hp
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hp
    exact i.property
  have hscale : ∀ p∈raw, DyadicLineGrid.scale p.1≤P.topLength := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact P.long_cell_scale_le_top i (hLong i hi)
  have hO : ∀ p∈raw, MeasurableSet (O p) := by
    intro p hp
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hp
    simpa only [O,extendWhitneyMask_val] using hOmega i
  have hm : ∀ p∈raw×ˢT, (volume.prod volume).real
      (partitionCell b P.width p∩(E∩u ⁻¹' O p.1))≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*P.width := by
    intro p hp
    obtain ⟨i,_hi,heq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hp).1
    rcases p with ⟨p,n⟩
    dsimp at heq
    subst p
    simpa only [O,extendWhitneyMask_val] using hmass i n
  have h := P.finite_angular_frozen_long_tree_bound c raw T a b eta E0 hE0 hcenter hW hscale
    E hE u hu O hO hm w cStar CEta Cb Cv nu hw hcStar hCEta hCb hspectrum hselector hbin
    Kx Ky hKx hKy hI hEnergy
  rw [angular_sum_subtype_product] at h
  simpa only [O,extendWhitneyMask_val,frozenWhitneyLocalAtWidth] using h


theorem angular_frozen_tree_integrable_bound (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : P.DensityWhitneyCell → Set ℝ)
    (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width)
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0 ≤ cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    Integrable (P.frozenTreeValueAtWidth w hne c E u Omega) (volume.prod volume) ∧
    (∫ z, ‖P.frozenTreeValueAtWidth w hne c E u Omega z‖ ∂volume.prod volume)≤
      Real.sqrt ((32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant)) := by
  classical
  let tiles := (Finset.univ : Finset P.PacketIndex)
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let ell := fun q : P.PacketIndex => P.length q.1
  let F := P.frozenWhitneyLocalAtWidth w c E u Omega
  let J := fun (i : P.DensityWhitneyCell) (n : ℤ) =>
    ∫ z in partitionCell b P.width (i.val,n), ‖F i z‖ ∂volume.prod volume
  have hzero (i : P.DensityWhitneyCell) (hi : ¬P.HasLongPacket i) (n : ℤ) : J i n=0 := by
    dsimp [J,F,frozenWhitneyLocalAtWidth]
    rw [hEmpty i hi,preimage_empty,inter_empty]
    simp only [indicator_empty,norm_zero,integral_zero]
  apply product_paste_integrable_bound tiles X ell
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) b P.width P.width_pos F
    (fun i => P.frozenWhitneyLocalAtWidth_integrable w hw.le c E hE u hu Omega hOmega b i.1 i.2)
  intro S T
  let SL := S.filter P.HasLongPacket
  have heq : (∑ j∈S×ˢT, J j.1 j.2)=(∑ j∈SL×ˢT, J j.1 j.2) := by
    simp only [Finset.sum_product,SL,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : P.HasLongPacket i
    · simp only [hi,ite_true, if_true]
    · simp only [hi,ite_false, if_false]
      exact Finset.sum_eq_zero (fun n _ => hzero i hi n)
  change (∑ j∈S×ˢT, J j.1 j.2)≤_
  rw [heq]
  apply Real.le_sqrt_of_sq_le
  exact P.finite_angular_frozenWhitney_bound c SL T a b eta E0 hE0 hcenter
    (fun i hi => (Finset.mem_filter.mp hi).2) E hE u hu Omega hOmega hmass
    w cStar CEta Cb Cv nu hw hcStar hCEta hCb hspectrum hselector hbin Kx Ky hKx hKy hI hEnergy


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedFrozenEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen integration for the actual masks supplied by a reference
coordinate change. No grid assumption is needed after the mass bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney

theorem exists_masked_frozen_tree_estimate_oai (hL : LepingleInput)
    (cStar cEta CEta cb Cb Cv : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0≤CEta) (hCv : 0≤Cv) (hcb : 0 ≤ cb) (hCb : 0≤Cb) (hgap : cStar < cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → 207≤P.order →
    ∀ (hne : Nonempty P.PacketIndex)
      (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (a b w eta sigma : ℝ),
      0<w → 0≤eta → 0 ≤ sigma →
      (∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2) →
      (∀ q : P.PacketIndex, |P.actualZ q.1 q.2.1 q.2.2-b|≤P.width/2) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |ξ+P.rowSlope j l*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j (l : P.labels j), |P.rowSlope j l|≤Cb*w/P.length j) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
        |η-P.frequency k|≤Cv/P.width) →
      (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l|) →
      (∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width)≤
        sigma^2*(P.topLength*P.width) →
    ∀ (E : Set (ℝ×ℝ)), MeasurableSet E → ∀ (u : ℝ×ℝ → ℝ), Measurable u →
    ∀ (Omega : P.DensityWhitneyCell → Set ℝ),
      (∀ i, MeasurableSet (Omega i)) →
      (∀ i, ¬P.HasLongPacket i → Omega i=∅) →
      (∀ i n, (volume.prod volume).real
        (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) →
      Integrable (P.frozenTreeValueAtWidth w hne c E u Omega) (volume.prod volume) ∧
      (∫ z, ‖P.frozenTreeValueAtWidth w hne c E u Omega z‖ ∂volume.prod volume)≤
        Real.sqrt (C*(B:ℝ))*P.absoluteConstant*eta*sigma*(P.topLength*P.width) := by
  obtain ⟨CV,hCV,hvariation⟩ := exists_supported_transverse_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  let Rx := (cStar+Cb*CEta)/(4*Real.pi)
  let Ry := Cv/(4*Real.pi)
  have hRx : 0≤Rx := div_nonneg (add_nonneg hcStar (mul_nonneg hCb hCEta)) (by positivity)
  have hRy : 0≤Ry := div_nonneg hCv (by positivity)
  obtain ⟨Kx,hKx⟩ := exists_schwartz_reproducing_kernel (Rx+1) (by linarith)
  obtain ⟨Ky,hKy⟩ := exists_schwartz_reproducing_kernel (Ry+1) (by linarith)
  let A := (32*(2:ℝ)^203)^2*
    (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*CV)*
    (9*transverseTailConstant)
  have hA : 0≤A := mul_nonneg (mul_nonneg (sq_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 206)
      (sq_nonneg _)) (by norm_num)) hCV.le))
    (mul_nonneg (by norm_num) transverseTailConstant_nonneg)
  refine ⟨A+1,by linarith,?_⟩
  intro N κ Label Item _ _ P B hcard horder hne c a b w eta sigma
    hw heta hsigma hX hY hspectrum hselector hbin hlower hsize E hE u hu
    Omega hOm hEmpty hmass
  have hZ (j : Fin N) (l : P.labels j) (v : Item j l) : |P.actualZ j l v-b|≤P.width :=
    (hY ⟨j,⟨l,v⟩⟩).trans (by linarith [P.width_pos])
  have hspectrum' : ∀ j l v k ξ η,
      planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+(0+P.rowSlope j l)*η| ≤ cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta := by
    simpa only [zero_add] using hspectrum
  obtain ⟨hI,hEnergy⟩ := hvariation N κ Label Item P B hcard 0 w b
    hw horder c hZ hspectrum' (fun j l v hv => ⟨hlower j l v hv,hselector j l⟩)
  let mass := ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width
  let E0 := (B:ℝ)*CV*P.absoluteConstant^2*mass
  have hmass0 : 0 ≤ mass := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
    Finset.sum_nonneg fun v _ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (P.length_pos j).le) P.width_pos.le
  have hE0 : 0≤E0 := mul_nonneg (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg B) hCV.le) (sq_nonneg _)) hmass0
  have hbound := P.angular_frozen_tree_integrable_bound hne c a b eta E0 hE0 hX E hE u hu
    Omega hOm hEmpty hmass w cStar CEta Cb Cv P.frequency hw hcStar hCEta hCb (by
      intro j l v k ξ η hn
      obtain ⟨hx, hlo, hhi⟩ := hspectrum j l v k ξ η hn
      refine ⟨hx, ?_⟩
      have hη : 0≤η := ((mul_pos_iff_of_pos_left hw).mp (hcEta.trans_le hlo)).le
      rw [abs_of_nonneg hη]
      exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hhi))
    hselector hbin
    Kx Ky (fun ξ hξ => hKx ξ (hξ.trans (by dsimp [Rx]; linarith)))
    (fun η hη => hKy η (hη.trans (by dsimp [Ry]; linarith)))
    (by simpa only [zero_mul,sub_zero] using hI)
    (by simpa only [zero_mul,sub_zero,E0,mass] using hEnergy)
  refine ⟨hbound.1,hbound.2.trans ?_⟩
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      P.absoluteConstant_pos.le) heta) hsigma) (mul_pos P.topLength_pos P.width_pos).le
  · have harea : 0≤P.topLength*P.width := (mul_pos P.topLength_pos P.width_pos).le
    have hfactor : 0≤(A+1)*(B:ℝ)*P.absoluteConstant^2*eta^2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg B))
        (sq_nonneg _)) (sq_nonneg _)
    calc
      _ = A*(B:ℝ)*P.absoluteConstant^2*eta^2*mass*(P.topLength*P.width) := by
        dsimp only [A,E0]
        simp only [mul_pow]
        simp only [mul_assoc,mul_comm,mul_left_comm]
      _ ≤ (A+1)*(B:ℝ)*P.absoluteConstant^2*eta^2*mass*(P.topLength*P.width) := by
        gcongr; linarith
      _ ≤ (A+1)*(B:ℝ)*P.absoluteConstant^2*eta^2*
          (sigma^2*(P.topLength*P.width))*(P.topLength*P.width) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hfactor)
          (mul_pos P.topLength_pos P.width_pos).le
      _ = _ := by
        rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt
          (mul_nonneg (by linarith : 0≤A+1) (Nat.cast_nonneg B))]
        simp only [pow_two]
        simp only [mul_assoc,mul_comm,mul_left_comm]


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate_oai := @OAI.LipschitzHilbert.SourceLabeledLattice.exists_masked_frozen_tree_estimate_oai
