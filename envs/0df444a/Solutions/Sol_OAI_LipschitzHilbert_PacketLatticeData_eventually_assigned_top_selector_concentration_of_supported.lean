-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:16:23.468803+00:00
-- url     : https://prove2.me/submissions/8f52b52e-937a-46b4-a1ae-439c33b71dd9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PlanarPacketFamily_analyzed_interval_neighborhood_of_supported
import Theorems.Thm_OAI_LipschitzHilbert_SourceLabeledLattice_eventually_selector_error_family_concentration_of_supported

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxVariationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable weights for the fixed-box variation estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem boxVariationWeight_pos (p : ℤ × ℤ) : 0 < boxVariationWeight p := by
  unfold boxVariationWeight lineEnvelope
  positivity

theorem boxVariationWeight_sum {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index) :
    (∑ i, boxVariationWeight (index i)) ≤ (4 * Real.pi) ^ 2 := by
  have h := injective_tile_lattice_overlap index hinj 0 0 1 1 0 0 (by norm_num)
    (by norm_num) (by norm_num : 1 ≤ (1 : ℕ)) (by norm_num : 1 ≤ (1 : ℕ))
  have heq (k : ℤ) : lineEnvelope (0 + 1 * k) 1 1 0 = lineEnvelope 0 1 1 k := by
    simp [lineEnvelope]
  simpa only [heq, boxVariationWeight] using h

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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CoefficientDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coefficient decomposes exactly into its frozen main part
and the angular error whose positive majorant was proved above. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem analyzingCoefficient_sub {Ω σ κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (area : σ → ℝ) (f h : σ → κ → Ω → ℂ)
    (g : Ω → EuclideanSpace ℂ κ)
    (hf : ∀ i k, Integrable (fun z => g z k * conj (f i k z)) μ)
    (hh : ∀ i k, Integrable (fun z => g z k * conj (h i k z)) μ) (i : σ) :
    analyzingCoefficient μ area (fun i k z => f i k z-h i k z) g i =
      analyzingCoefficient μ area f g i - analyzingCoefficient μ area h g i := by
  ext k
  change ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z-h i k z) ∂μ) =
    ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (f i k z) ∂μ) -
      ((area i)⁻¹ : ℂ) * (∫ z, g z k * conj (h i k z) ∂μ)
  simp only [map_sub, mul_sub]
  rw [integral_sub (hf i k) (hh i k)]
  ring

theorem angularErrorWave_eq_sub {ι κ : Type*} (b : ι → κ → ℝ → ℂ)
    (ψ : ι → κ → ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (i : ι) (k : κ) (z : ℝ × ℝ) :
    angularErrorWave b ψ u t d i k z =
      b i k (u z) * ψ i k z - (if |u z-t| ≤ d then b i k t * ψ i k z else 0) := by
  unfold angularErrorWave multiplierError
  split_ifs <;> ring

theorem angularCoefficient_decomposition {ι κ : Type*}
    (area : ι → ℝ) (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (hOriginal : ∀ i k, Integrable (fun z => g z k * conj (b i k (u z) * ψ i k z)))
    (hMain : ∀ i k, Integrable (fun z => g z k *
      conj (if |u z-t| ≤ d then b i k t * ψ i k z else 0))) (i : ι) :
    analyzingCoefficient volume area (fun i k z => b i k (u z)*ψ i k z) g i =
      analyzingCoefficient volume area (fun i k z =>
        if |u z-t| ≤ d then b i k t*ψ i k z else 0) g i +
      analyzingCoefficient volume area (angularErrorWave b ψ u t d) g i := by
  have heq : angularErrorWave b ψ u t d = (fun i k z =>
      b i k (u z)*ψ i k z - (if |u z-t| ≤ d then b i k t*ψ i k z else 0)) := by
    funext i k z
    exact angularErrorWave_eq_sub b ψ u t d i k z
  rw [heq, analyzingCoefficient_sub volume area _ _ g hOriginal hMain]
  abel

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PolynomialPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial weights preserve the required packet decay and
horizontal derivative bounds, after choosing the original packet order. -/

noncomputable section

namespace LipschitzHilbert

theorem polynomialWeight_derivative (a r x : ℝ) (q : ℕ) (hr : 0 < r) :
    |deriv (polynomialWeight a r q) x| ≤
      (2*(q:ℝ)/r)*polynomialWeight a r q x := by
  cases q with
  | zero =>
    change |deriv (fun _ : ℝ => (1:ℝ)) x| ≤ _
    simp
  | succ q =>
    let t := (x-a)/r
    let B := 1+t^2
    have hB : 0 < B := by dsimp [B]; positivity
    have ht : |t| ≤ B := by dsimp [B]; nlinarith [sq_nonneg (|t|-1), sq_abs t]
    have hd := ((((hasDerivAt_id x).sub_const a).div_const r).pow 2).const_add 1 |>.pow (q+1)
    dsimp only [Pi.pow_apply, id_eq] at hd
    change HasDerivAt (fun y : ℝ => (1+((y-a)/r)^2)^(q+1)) _ x at hd
    have heq : (fun y : ℝ => (1+((y-a)/r)^2)^(q+1)) = polynomialWeight a r (q+1) := by
      funext y
      simp only [polynomialWeight, div_pow]
    rw [heq] at hd
    rw [hd.deriv]
    have habs : |(q+1:ℝ) * B^q * (2*t*(1/r))| =
        (2*(q+1:ℝ)/r)*B^q*|t| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (q+1:ℝ)),
        abs_of_nonneg (pow_nonneg hB.le q), abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (by positivity : 0 < 1/r)]
      ring
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Nat.cast_ofNat] at *
    simp only [Nat.reduceSub, pow_one, polynomialWeight, ← div_pow]
    change |(q+1:ℝ)*B^q*(2*t*(1/r))| ≤ (2*(q+1:ℝ)/r)*B^(q+1)
    rw [habs, pow_succ]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht
      (show 0 ≤ (2*(q+1:ℝ)/r)*B^q by positivity)

theorem polynomialWeight_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s-a| ≤ r) :
    polynomialWeight a r q x * lineEnvelope s l (n+2*q) x ≤
      16^q * lineEnvelope s l n x := by
  have hP := polynomialWeight_one_le a r q x
  have hsq : polynomialWeight a r q x ≤ polynomialWeight a r q x^2 := by nlinarith
  exact (mul_le_mul_of_nonneg_right hsq (lineEnvelope_nonneg _ _ _ _)).trans
    (polynomialWeight_sq_mul_envelope x s a l r q n hl hr hlr hsa)

theorem polynomialLocalization_packet_bound (f : SchwartzMap ℝ ℂ)
    (a r s l C : ℝ) (q n : ℕ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hsa : |s-a| ≤ r) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*lineEnvelope s l (n+2*q) x) (x : ℝ) :
    ‖polynomialLocalization a r q f x‖ ≤ (16^q*C)*lineEnvelope s l n x := by
  rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((polynomialWeight_one_le a r q x).trans' (by norm_num))]
  calc
    _ ≤ polynomialWeight a r q x * (C*lineEnvelope s l (n+2*q) x) :=
      mul_le_mul_of_nonneg_left (hf x) (zero_le_one.trans (polynomialWeight_one_le a r q x))
    _ = C*(polynomialWeight a r q x * lineEnvelope s l (n+2*q) x) := by ring
    _ ≤ C*(16^q*lineEnvelope s l n x) := mul_le_mul_of_nonneg_left
      (polynomialWeight_mul_envelope x s a l r q n hl hr hlr hsa) hC
    _ = _ := by ring

theorem polynomialWeight_differentiable (a r : ℝ) (q : ℕ) :
    Differentiable ℝ (polynomialWeight a r q) := by
  unfold polynomialWeight
  fun_prop

theorem polynomialLocalization_deriv (f : SchwartzMap ℝ ℂ) (a r : ℝ) (q : ℕ) (x : ℝ) :
    deriv (polynomialLocalization a r q f) x =
      ((deriv (polynomialWeight a r q) x : ℝ) : ℂ)*f x +
        (polynomialWeight a r q x : ℂ)*deriv f x := by
  have hd := (((polynomialWeight_differentiable a r q) x).hasDerivAt.ofReal_comp).mul
    ((f.differentiable x).hasDerivAt)
  have heq : (fun y => (polynomialWeight a r q y : ℂ)*f y) =
      polynomialLocalization a r q f := by
    funext y
    exact (polynomialLocalization_apply a r q f y).symm
  change HasDerivAt (fun y => (polynomialWeight a r q y : ℂ)*f y) _ x at hd
  rw [heq] at hd
  exact hd.deriv

theorem polynomialLocalization_derivative_bound (f : SchwartzMap ℝ ℂ)
    (a r s l C : ℝ) (q n : ℕ) (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r)
    (hsa : |s-a| ≤ r) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*lineEnvelope s l (n+2*q) x)
    (hdf : ∀ x, ‖deriv f x‖ ≤ (C/l)*lineEnvelope s l (n+2*q) x) (x : ℝ) :
    ‖deriv (polynomialLocalization a r q f) x‖ ≤
      ((16^q*(1+2*(q:ℝ))*C)/l)*lineEnvelope s l n x := by
  rw [polynomialLocalization_deriv]
  have hP : 0 ≤ polynomialWeight a r q x :=
    zero_le_one.trans (polynomialWeight_one_le a r q x)
  have hq : 0 ≤ 2*(q:ℝ) := by positivity
  have hradius : 2*(q:ℝ)/r ≤ 2*(q:ℝ)/l :=
    div_le_div_of_nonneg_left hq hl hlr
  have hw := (polynomialWeight_derivative a r x q hr).trans
    (mul_le_mul_of_nonneg_right hradius hP)
  calc
    _ ≤ ‖((deriv (polynomialWeight a r q) x : ℝ) : ℂ)*f x‖ +
        ‖(polynomialWeight a r q x : ℂ)*deriv f x‖ := norm_add_le _ _
    _ = |deriv (polynomialWeight a r q) x| * ‖f x‖ +
        polynomialWeight a r q x * ‖deriv f x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP]
    _ ≤ ((2*(q:ℝ)/l)*polynomialWeight a r q x) *
        (C*lineEnvelope s l (n+2*q) x) + polynomialWeight a r q x *
        ((C/l)*lineEnvelope s l (n+2*q) x) :=
      add_le_add (mul_le_mul hw (hf x) (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left (hdf x) hP)
    _ = ((1+2*(q:ℝ))*C/l) *
        (polynomialWeight a r q x * lineEnvelope s l (n+2*q) x) := by ring
    _ ≤ ((1+2*(q:ℝ))*C/l) * (16^q*lineEnvelope s l n x) :=
      mul_le_mul_of_nonneg_left (polynomialWeight_mul_envelope x s a l r q n hl hr hlr hsa)
        (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorb the transverse factor of the top polynomial into fixed packet
decay. The resulting constant is uniform over the reference line. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem vertical_weighted_envelope (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X) :
    polynomialWeight a R q y * (X*lineEnvelope s W (n+2*q) y) ≤
      (16^q*X)*lineEnvelope s W n y := by
  have h := mul_le_mul_of_nonneg_left
    (polynomialWeight_mul_envelope y s a W R q n hW hR hWR hs) hX
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem vertical_weighted_wave (f : SchwartzMap ℝ ℂ)
    (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X)
    (x : ℝ) (hf : ‖f x‖ ≤ X*lineEnvelope s W (n+2*q) y) :
    ‖((polynomialWeight a R q y : ℂ) • f) x‖ ≤
      (16^q*X)*lineEnvelope s W n y := by
  rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (polynomialWeight_one_le a R q y))]
  exact (mul_le_mul_of_nonneg_left hf
    (zero_le_one.trans (polynomialWeight_one_le a R q y))).trans
      (vertical_weighted_envelope y s a W R X q n hW hR hWR hs hX)

theorem vertical_weighted_derivative (f : SchwartzMap ℝ ℂ)
    (y s a W R X : ℝ) (q n : ℕ)
    (hW : 0 < W) (hR : 0 < R) (hWR : W ≤ R) (hs : |s-a| ≤ R) (hX : 0 ≤ X)
    (x : ℝ) (hf : ‖deriv f x‖ ≤ X*lineEnvelope s W (n+2*q) y) :
    ‖deriv ((polynomialWeight a R q y : ℂ) • f) x‖ ≤
      (16^q*X)*lineEnvelope s W n y := by
  have hd := (f.differentiable x).hasDerivAt.const_mul (polynomialWeight a R q y : ℂ)
  change ‖deriv (fun t => (polynomialWeight a R q y : ℂ)*f t) x‖ ≤ _
  rw [hd.deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (polynomialWeight_one_le a R q y))]
  exact (mul_le_mul_of_nonneg_left hf
    (zero_le_one.trans (polynomialWeight_one_le a R q y))).trans
      (vertical_weighted_envelope y s a W R X q n hW hR hWR hs hX)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopWeightedPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both factors of a fixed top polynomial can be absorbed into the
original packet orders, uniformly in the horizontal reference line. -/

noncomputable section
open scoped BigOperators
open FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem topWeightedWave_apply (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) (x : ℝ) :
    topWeightedWave f a r b R y q x =
      (polynomialWeight a r q x * polynomialWeight b R q y : ℝ) * f x := by
  rw [topWeightedWave, polynomialLocalization_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

theorem topWeightedWave_bound (f : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖topWeightedWave f a r b R y q x‖ ≤
      (16^q*(16^q*C))*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have hv (z : ℝ) : ‖((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      (16^q*C*lineEnvelope t W n y)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_wave f y t b W R (C*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg hC (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hf z)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := polynomialLocalization_packet_bound
    ((polynomialWeight b R q y : ℂ) • f) a r s l
    (16^q*C*lineEnvelope t W n y) q m hl hr hlr hs
    (mul_nonneg (mul_nonneg (by positivity) hC) (lineEnvelope_nonneg _ _ _ _)) hv x
  convert h using 1
  · rfl
  · ring

theorem topWeightedWave_derivative_bound (f : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖deriv f x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖deriv (topWeightedWave f a r b R y q) x‖ ≤
      ((16^q*(1+2*(q:ℝ))*(16^q*C))/l)*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have hv (z : ℝ) : ‖((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      (16^q*C*lineEnvelope t W n y)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_wave f y t b W R (C*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg hC (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hf z)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hd (z : ℝ) : ‖deriv ((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      ((16^q*C*lineEnvelope t W n y)/l)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_derivative f y t b W R ((C/l)*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg (div_nonneg hC hl.le) (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hdf z)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have h := polynomialLocalization_derivative_bound
    ((polynomialWeight b R q y : ℂ) • f) a r s l
    (16^q*C*lineEnvelope t W n y) q m hl hr hlr hs
    (mul_nonneg (mul_nonneg (by positivity) hC) (lineEnvelope_nonneg _ _ _ _)) hv hd x
  convert h using 1
  · rfl
  · ring

theorem topWeightedWave_low (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (topWeightedWave f a r b R y q) ξ = 0 := by
  apply polynomialLocalization_low a r q _ lo hi ?_ ?_ ξ hξ
  · intro z hz
    rw [fourier_smul, smul_apply, hlow z hz, smul_zero]
  · intro z hz
    rw [fourier_smul, smul_apply, hhigh z hz, smul_zero]

theorem topWeightedWave_high (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (topWeightedWave f a r b R y q) ξ = 0 := by
  apply polynomialLocalization_high a r q _ lo hi ?_ ?_ ξ hξ
  · intro z hz
    rw [fourier_smul, smul_apply, hlow z hz, smul_zero]
  · intro z hz
    rw [fourier_smul, smul_apply, hhigh z hz, smul_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem lineMomentBase_pos (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching) :
    0 < lineMomentBase C D branching := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold lineMomentBase
  positivity

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MomentSuperlevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Use a natural moment at its chosen order to obtain a geometric
exceptional-set bound. No asymptotic or unspecified tail input is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem quarter_pow_exp (n : ℕ) :
    (1/4:ℝ)^n = Real.exp (-(Real.log 4)*(n:ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), Real.log_one]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ExponentialThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select the moment order explicitly to absorb a positive global
prefactor into the prescribed exponential exceptional-area budget. -/

noncomputable section

namespace LipschitzHilbert

theorem quarter_ceil_bound (x : ℝ) :
    (1/4:ℝ)^⌈x / Real.log 4⌉₊ ≤ Real.exp (-x) := by
  rw [quarter_pow_exp]
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc := (div_le_iff₀ hlog).mp (Nat.le_ceil (x / Real.log 4))
  nlinarith

theorem prefactor_quarter_ceil_bound (M x : ℝ) (hM : 0 < M) :
    M * (1/4:ℝ)^⌈(x+Real.log M) / Real.log 4⌉₊ ≤ Real.exp (-x) := by
  calc
    _ ≤ M * Real.exp (-(x+Real.log M)) :=
      mul_le_mul_of_nonneg_left (quarter_ceil_bound (x+Real.log M)) hM.le
    _ = Real.exp (Real.log M) * Real.exp (-(x+Real.log M)) := by
      rw [Real.exp_log hM]
    _ = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The extra successor guarantees a positive moment order and retains
the requested exponential bound. -/
theorem prefactor_quarter_successor_bound (M x : ℝ) (hM : 0 < M) :
    M * (1/4:ℝ)^(⌈(x+Real.log M) / Real.log 4⌉₊+1) ≤ Real.exp (-x) := by
  calc
    _ ≤ M * (1/4:ℝ)^⌈(x+Real.log M) / Real.log 4⌉₊ := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4)
        ⌈(x+Real.log M) / Real.log 4⌉₊]
    _ ≤ _ := prefactor_quarter_ceil_bound M x hM

theorem exponential_moment_order_le (J c L M : ℝ)
    (hJ : 0 ≤ J) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hlog : Real.log M ≤ c*L) :
    ((⌈(J*L+Real.log M) / Real.log 4⌉₊+1:ℕ):ℝ) ≤
      ((J+c)/Real.log 4+2)*L := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnum : 0 ≤ J*L+Real.log M :=
    add_nonneg (mul_nonneg hJ (by linarith)) (Real.log_nonneg hM)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hnum h4.le)
  have hdiv : (J*L+Real.log M)/Real.log 4 ≤ ((J+c)/Real.log 4)*L := by
    calc
      _ ≤ (J*L+c*L)/Real.log 4 := div_le_div_of_nonneg_right (by linarith) h4.le
      _ = _ := by ring
  push_cast
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GlobalExceptionalArea
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the decaying top-box exceptional areas over the entire plane.
This uses the actual summable lattice weight, rather than discarding
the boxes outside the top rectangle. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace LipschitzHilbert

theorem boxVariationWeight_tsum :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (boxVariationWeight p)) ≤
      ENNReal.ofReal ((4*Real.pi)^2) := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => (boxVariationWeight_pos p).le)]
  apply ENNReal.ofReal_le_ofReal
  have h := boxVariationWeight_sum (fun p : s => (p : ℤ × ℤ)) Subtype.val_injective
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using h

theorem global_exceptional_area {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : ℤ × ℤ → Set Ω) (A : ℝ≥0∞)
    (hbad : ∀ p, μ (bad p) ≤ A * ENNReal.ofReal (boxVariationWeight p)) :
    μ (⋃ p, bad p) ≤ A * ENNReal.ofReal ((4*Real.pi)^2) := by
  calc
    _ ≤ ∑' p, μ (bad p) := measure_iUnion_le _
    _ ≤ ∑' p, A * ENNReal.ofReal (boxVariationWeight p) := ENNReal.tsum_le_tsum hbad
    _ = A * ∑' p, ENNReal.ofReal (boxVariationWeight p) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl boxVariationWeight_tsum

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedExceptionalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Raising the box threshold by the reciprocal lattice weight gives
summable exceptional areas, with a fixed spatial decay order. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem boxVariationWeight_le_one (p : ℤ × ℤ) : boxVariationWeight p ≤ 1 := by
  have h (x : ℝ) : lineEnvelope 0 1 1 x ≤ 1 := by
    simp only [lineEnvelope, sub_zero, div_one, pow_one]
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  exact (mul_le_mul (h p.1) (h p.2) (lineEnvelope_nonneg _ _ _ _) (by norm_num)).trans_eq
    (one_mul _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopBoxPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed polynomial top weights dominate the reciprocal lattice decay
uniformly on a whole box and all its allowed vertical shifts. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base_two (a r k x : ℝ) (hr : 0 < r)
    (hx : |x-(a+r*k)| ≤ 2*r) :
    (1+k^2)/16 ≤ 1+((x-a)/r)^2 := by
  let t := (x-a)/r
  have hd : |t-k| ≤ 2 := by
    have heq : t-k = (x-(a+r*k))/r := by dsimp [t]; field_simp; ring
    rw [heq, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    exact hx
  have hs : (t-k)^2 ≤ 4 := by nlinarith [abs_le.mp hd, sq_abs (t-k)]
  dsimp only [t] at *
  nlinarith [sq_nonneg (k-2*((x-a)/r)), sq_nonneg ((x-a)/r)]

theorem topWeight_box_lower (a b r R x z v : ℝ) (p : ℤ × ℤ) (q : ℕ)
    (hr : 0 < r) (hR : 0 < R)
    (hx : |x-(a+r*p.1)| ≤ r) (hz : |z-(b+R*p.2)| ≤ R) (hv : |v| ≤ R) :
    ((boxVariationWeight p)⁻¹/256)^q ≤
      polynomialWeight a r q x * polynomialWeight b R q (z+v) := by
  have hx2 : |x-(a+r*p.1)| ≤ 2*r := hx.trans (by linarith)
  have hz2 : |(z+v)-(b+R*p.2)| ≤ 2*R := by
    calc
      _ = |(z-(b+R*p.2))+v| := by congr 1; ring
      _ ≤ |z-(b+R*p.2)|+|v| := abs_add_le _ _
      _ ≤ 2*R := by linarith
  have h1 := box_polynomial_base_two a r p.1 x hr hx2
  have h2 := box_polynomial_base_two b R p.2 (z+v) hR hz2
  have hprod := mul_le_mul h1 h2 (by positivity : 0 ≤ (1+(p.2:ℝ)^2)/16)
    (by positivity : 0 ≤ 1+((x-a)/r)^2)
  have hinv : (boxVariationWeight p)⁻¹ = (1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2) := by
    simp only [boxVariationWeight, lineEnvelope, sub_zero, div_one, pow_one, mul_inv_rev, inv_inv]
    ring
  rw [hinv]
  have hbase : ((1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2))/256 ≤
      (1+((x-a)/r)^2)*(1+((z+v-b)/R)^2) := by nlinarith [hprod]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤
    ((1+(p.1:ℝ)^2)*(1+(p.2:ℝ)^2))/256) hbase q
  simpa only [polynomialWeight, ← div_pow, mul_pow] using hp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopBoxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a weighted top bound to a decaying unweighted bound, using
one fixed polynomial degree independently of the moment order. -/

noncomputable section

namespace LipschitzHilbert

theorem weighted_bound_to_box_decay (A S w P : ℝ) (hS : 0 ≤ S) (hw : 0 < w)
    (q : ℕ) (hq : 1 ≤ q) (hP : (w⁻¹/256)^q ≤ P) (hbound : P*S ≤ A/w) :
    S ≤ 256^q*A*w^(q-1) := by
  have hL : 0 < (w⁻¹/256)^q := by positivity
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    ((w⁻¹/256)^q)*S ≤ P*S := mul_le_mul_of_nonneg_right hP hS
    _ ≤ A/w := hbound
    _ = ((w⁻¹/256)^q)*(256^q*A*w^(q-1)) := by
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      subst q
      simp only [Nat.succ_sub_one, pow_succ, div_pow, inv_pow]
      field_simp [hw.ne']

theorem topWeight_bound_to_box_decay (a b r R x z v A S : ℝ) (p : ℤ × ℤ)
    (q : ℕ) (hq : 1 ≤ q) (hS : 0 ≤ S) (hr : 0 < r) (hR : 0 < R)
    (hx : |x-(a+r*p.1)| ≤ r) (hz : |z-(b+R*p.2)| ≤ R) (hv : |v| ≤ R)
    (hbound : (polynomialWeight a r q x * polynomialWeight b R q (z+v))*S ≤
      A/boxVariationWeight p) :
    S ≤ 256^q*A*boxVariationWeight p^(q-1) :=
  weighted_bound_to_box_decay A S (boxVariationWeight p) _ hS (boxVariationWeight_pos p)
    q hq (topWeight_box_lower a b r R x z v p q hr hR hx hz hv) hbound

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GlobalTopBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue the measurable box exceptions across the full plane, retaining
both the summable area estimate and polynomial decay away from the top. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem floor_box_mem_Ico (a r x : ℝ) (hr : 0 < r) :
    x ∈ Ico (a+r*(⌊(x-a)/r⌋:ℤ)) (a+r*((⌊(x-a)/r⌋:ℤ)+1)) := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le ((x-a)/r)) hr.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x-a)/r)) hr
  rw [div_mul_cancel₀ _ hr.ne'] at hlo hhi
  constructor <;> linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedMomentIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A spatially varying natural moment order turns uniform local
exponential tails into a summable global exceptional set. -/

noncomputable section
open scoped ENNReal
namespace LipschitzHilbert

theorem quarter_pow_ceil_inv_le (w : ℝ) (hw : 0 < w) :
    (1/4:ℝ)^(⌈w⁻¹⌉₊) ≤ w := by
  have hceil : w⁻¹ ≤ (⌈w⁻¹⌉₊:ℝ) := Nat.le_ceil _
  have hpow : (⌈w⁻¹⌉₊:ℝ) ≤ (4:ℝ)^⌈w⁻¹⌉₊ := by
    have hb := one_add_mul_le_pow (by norm_num : (-2:ℝ) ≤ 3) ⌈w⁻¹⌉₊
    norm_num at hb
    nlinarith [inv_pos.mpr hw]
  rw [div_pow, one_pow]
  apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)^⌈w⁻¹⌉₊)).mpr
  have h := mul_le_mul_of_nonneg_left (hceil.trans hpow) hw.le
  simpa only [mul_inv_cancel₀ hw.ne'] using h

theorem weightedMomentIndex_pos (n : ℕ) (hn : 1 ≤ n) (w : ℝ) :
    1 ≤ weightedMomentIndex n w := hn.trans (Nat.le_add_right _ _)

theorem weightedMomentIndex_le (n : ℕ) (hn : 1 ≤ n) (w : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    (weightedMomentIndex n w : ℝ) ≤ 3*(n:ℝ)/w := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hceil : (⌈w⁻¹⌉₊:ℝ) ≤ w⁻¹+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hm := mul_le_mul_of_nonneg_right hceil hw.le
  rw [add_mul, inv_mul_cancel₀ hw.ne', one_mul] at hm
  have hnw := mul_le_mul_of_nonneg_left hw1 (Nat.cast_nonneg n)
  apply (le_div_iff₀ hw).mpr
  simp only [weightedMomentIndex, Nat.cast_add]
  nlinarith

theorem weightedMomentIndex_tail (n : ℕ) (w : ℝ) (hw : 0 < w) :
    (1/4:ℝ≥0∞)^(weightedMomentIndex n w) ≤
      (1/4:ℝ≥0∞)^n*ENNReal.ofReal w := by
  have h := ENNReal.ofReal_le_ofReal (quarter_pow_ceil_inv_le w hw)
  have heq : ENNReal.ofReal ((1/4:ℝ)^⌈w⁻¹⌉₊) = (1/4:ℝ≥0∞)^⌈w⁻¹⌉₊ := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [heq] at h
  simpa only [weightedMomentIndex, pow_add] using mul_le_mul' (le_refl ((1/4:ℝ≥0∞)^n)) h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GlobalLocalNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globalize the proved local neighborhood estimates by increasing the
natural moment order on distant boxes. The total exceptional area stays
exponentially small and the top's polynomial decay is retained. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem global_top_neighborhood_of_local {α E : Type*} [NormedAddCommGroup E]
    (F : α → ℝ → ℝ → E) (a b r R B : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hB : 0 ≤ B) (M : ℝ≥0∞) (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hlocal : ∀ (p : ℤ × ℤ) (m : ℕ), 1 ≤ m →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^m*M ∧
        ∀ i x z v, x ∈ Ico (a+r*p.1) (a+r*((p.1:ℝ)+1)) →
          |z-(b+R*p.2)| ≤ R → |v| ≤ R → (x,z) ∉ bad →
          (polynomialWeight a r q x*polynomialWeight b R q (z+v))*‖F i x (z+v)‖ ≤
            B*(m:ℝ)) :
    ∃ exceptional : Set (ℝ × ℝ), MeasurableSet exceptional ∧
      (volume.prod volume) exceptional ≤
        (1/4:ℝ≥0∞)^n*M*ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x z v, |v| ≤ R → (x,z) ∉ exceptional →
        ‖F i x (z+v)‖ ≤ 256^q*(3*B*(n:ℝ))*
          boxVariationWeight (packetBoxIndex a b r R x z)^(q-1) := by
  classical
  choose bad hbad using fun p : ℤ × ℤ => hlocal p
    (weightedMomentIndex n (boxVariationWeight p)) (weightedMomentIndex_pos n hn _)
  have harea (p : ℤ × ℤ) : (volume.prod volume) (bad p) ≤
      ((1/4:ℝ≥0∞)^n*M)*ENNReal.ofReal (boxVariationWeight p) := by
    calc
      _ ≤ (1/4:ℝ≥0∞)^(weightedMomentIndex n (boxVariationWeight p))*M := (hbad p).2.1
      _ ≤ ((1/4:ℝ≥0∞)^n*ENNReal.ofReal (boxVariationWeight p))*M :=
        mul_le_mul' (weightedMomentIndex_tail n _ (boxVariationWeight_pos p)) le_rfl
      _ = _ := by ring
  refine ⟨⋃ p, bad p, MeasurableSet.iUnion (fun p => (hbad p).1),
    global_exceptional_area (volume.prod volume) bad _ harea, ?_⟩
  intro i x z v hv hout
  let p := packetBoxIndex a b r R x z
  have hpout : (x,z) ∉ bad p := fun h => hout (mem_iUnion.mpr ⟨p,h⟩)
  have hx := floor_box_mem_Ico a r x hr
  have hz := packetBoxIndex_vertical a b r R x z hR
  have hbound := (hbad p).2.2 i x z v hx hz hv hpout
  apply topWeight_bound_to_box_decay a b r R x z v (3*B*(n:ℝ)) _ p q hq
    (norm_nonneg _) hr hR (packetBoxIndex_horizontal a b r R x z hr) hz hv
  apply hbound.trans
  have hm := mul_le_mul_of_nonneg_left
    (weightedMomentIndex_le n hn _ (boxVariationWeight_pos p) (boxVariationWeight_le_one p)) hB
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HorizontalDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact product-measure dilation in the horizontal coordinate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem map_horizontalDilation (r : ℝ) (hr : r ≠ 0) :
    Measure.map (horizontalDilation r hr) (volume.prod volume) =
      ENNReal.ofReal |r⁻¹| • (volume.prod volume) := by
  change Measure.map (Prod.map (fun x : ℝ => r*x) id) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) measurable_id,Measure.map_id]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,Measure.prod_smul_left]

theorem measure_horizontalDilation_preimage (r : ℝ) (hr : r ≠ 0)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    (volume.prod volume) (horizontalDilation r hr ⁻¹' s) =
      ENNReal.ofReal |r⁻¹| * (volume.prod volume) s := by
  rw [← Measure.map_apply (horizontalDilation r hr).measurable hs,map_horizontalDilation]
  rfl

theorem map_referenceHorizontalDilation (r : ℝ) (hr : r ≠ 0) :
    Measure.map (referenceHorizontalDilation r hr) (volume.prod volume) =
      ENNReal.ofReal |r⁻¹| • (volume.prod volume) := by
  change Measure.map (Prod.map id (fun x : ℝ => r*x)) (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume measurable_id (by fun_prop),Measure.map_id]
  have hm : Measure.map (fun x : ℝ => r*x) volume = ENNReal.ofReal |r⁻¹| • volume := by
    simpa only [smul_eq_mul,Module.finrank_self,pow_one] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) hr)
  rw [hm,Measure.prod_smul_right]

theorem integral_referenceHorizontalDilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) (r : ℝ) (hr : r ≠ 0) :
    (∫ z, f (referenceHorizontalDilation r hr z) ∂volume.prod volume) =
      |r⁻¹| • (∫ z, f z ∂volume.prod volume) := by
  rw [← integral_map_equiv (referenceHorizontalDilation r hr),map_referenceHorizontalDilation,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarHorizontalRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a top's horizontal length while retaining its packet
lattice and its original analyzing coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem horizontalRescale_mainCoefficient (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).mainCoefficient d
      (fun z => v (z.1,r*z.2)) (fun z => g (z.1,r*z.2)) j i = P.mainCoefficient d v g j i := by
  ext k
  simp only [mainCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑((P.horizontalRescale r hr).length j*P.width) : ℂ)⁻¹)*
      (∫ z, g (z.1,r*z.2) k * conj ((P.horizontalRescale r hr).selectedWave d
        (fun z => v (z.1,r*z.2)) ⟨j,i⟩ k z) ∂volume.prod volume) = _
  have heq : (fun z : ℝ × ℝ => g (z.1,r*z.2) k * conj
      ((P.horizontalRescale r hr).selectedWave d (fun z => v (z.1,r*z.2)) ⟨j,i⟩ k z)) =
      (fun z => (fun w : ℝ × ℝ => g w k*conj (P.selectedWave d v ⟨j,i⟩ k w))
        (referenceHorizontalDilation r hr.ne' z)) := by
    funext z
    rfl
  have hint := integral_referenceHorizontalDilation
    (fun w : ℝ × ℝ => g w k*conj (P.selectedWave d v ⟨j,i⟩ k w)) r hr.ne'
  rw [heq,hint,horizontalRescale_length,abs_of_pos (inv_pos.mpr hr)]
  change ((↑((P.length j/r)*P.width) : ℂ)⁻¹)*(r⁻¹ • _) =
    ((↑(P.length j*P.width) : ℂ)⁻¹)*_
  rw [Complex.real_smul]
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  rfl

end PlanarPacketFamily
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

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopLatticeDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the lattice decay in the global concentration estimate into
the eighth power of the manuscript's actual slope-box weight. -/

noncomputable section
namespace LipschitzHilbert

theorem floor_abs_bound (x : ℝ) : |x| ≤ |((⌊x⌋:ℤ):ℝ)|+1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  exact abs_le.mpr ⟨by linarith [neg_abs_le (⌊x⌋:ℝ)],
    by linarith [le_abs_self (⌊x⌋:ℝ)]⟩

theorem boxVariationWeight_floor_bound (x y : ℝ) :
    (1+|x|+|y|)*boxVariationWeight (⌊x⌋,⌊y⌋) ≤ 5 := by
  let i : ℝ := ⌊x⌋
  let j : ℝ := ⌊y⌋
  have hi : |i| ≤ 1+i^2 := by nlinarith [sq_nonneg (|i|-1), sq_abs i]
  have hj : |j| ≤ 1+j^2 := by nlinarith [sq_nonneg (|j|-1), sq_abs j]
  have hbase : 1+|x|+|y| ≤ 5*((1+i^2)*(1+j^2)) := by
    have hx := floor_abs_bound x
    have hy := floor_abs_bound y
    change |x| ≤ |i|+1 at hx
    change |y| ≤ |j|+1 at hy
    nlinarith [sq_nonneg i, sq_nonneg j, mul_nonneg (sq_nonneg i) (sq_nonneg j)]
  have hden : 0 < (1+i^2)*(1+j^2) := by positivity
  have heq : boxVariationWeight (⌊x⌋,⌊y⌋) = ((1+i^2)*(1+j^2))⁻¹ := by
    simp [boxVariationWeight, lineEnvelope, i, j, mul_comm]
  rw [heq, ← div_eq_mul_inv]
  exact (div_le_iff₀ hden).mpr hbase

theorem boxVariationWeight_floor_power (x y : ℝ) (m : ℕ) :
    boxVariationWeight (⌊x⌋,⌊y⌋)^m ≤ 5^m/(1+|x|+|y|)^m := by
  have hb : 0 < 1+|x|+|y| := by positivity
  apply (le_div_iff₀ (pow_pos hb m)).mpr
  have hp := pow_le_pow_left₀
    (mul_nonneg (by positivity) (boxVariationWeight_pos (⌊x⌋,⌊y⌋)).le)
    (boxVariationWeight_floor_bound x y) m
  simpa only [mul_pow, mul_comm] using hp

namespace SlopeBox

theorem weight_nat_eighth (T : SlopeBox) (K : ℝ) (hK : 0 < K) (d : ℕ) (z : ℝ × ℝ) :
    (T.weight K (d:ℝ) z)^8 = (2:ℝ)^(8*d)/(1+T.radius z/K)^(8*d) := by
  have hb : 0 ≤ 1+T.radius z/K := by
    have := T.radius_nonnegative z
    positivity
  simp only [weight, Real.rpow_neg hb, Real.rpow_natCast, mul_pow, inv_pow, ← pow_mul]
  rw [mul_comm d 8]
  simp only [div_eq_mul_inv]

theorem lattice_decay_le_weight (T : SlopeBox) (K : ℝ) (hK : 0 < K)
    (d : ℕ) (z : ℝ × ℝ) :
    boxVariationWeight (packetBoxIndex T.x (T.y-T.slope*T.x)
      (K*T.length) (K*T.width) z.1 (z.2-T.slope*z.1))^(8*d) ≤
        (5:ℝ)^(8*d)*(T.weight K (d:ℝ) z)^8 := by
  let X := (z.1-T.x)/(K*T.length)
  let Y := ((z.2-T.slope*z.1)-(T.y-T.slope*T.x))/(K*T.width)
  have hr : 1+|X|+|Y| = 1+T.radius z/K := by
    unfold radius horizontal transverse
    dsimp [X,Y]
    rw [abs_div, abs_div, abs_of_pos (mul_pos hK T.length_pos),
      abs_of_pos (mul_pos hK T.width_pos), abs_div, abs_div,
      abs_of_pos T.length_pos, abs_of_pos T.width_pos]
    have heq : (z.2-T.slope*z.1)-(T.y-T.slope*T.x) =
        (z.2-T.y)-T.slope*(z.1-T.x) := by ring
    rw [heq]
    ring
  have hp := boxVariationWeight_floor_power X Y (8*d)
  change boxVariationWeight (⌊X⌋,⌊Y⌋)^(8*d) ≤ _
  apply hp.trans
  rw [hr, T.weight_nat_eighth K hK]
  have hden : 0 < (1+T.radius z/K)^(8*d) := by
    have := T.radius_nonnegative z
    positivity
  have htwo : (1:ℝ) ≤ 2^(8*d) := one_le_pow₀ (by norm_num)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hden.le
  exact le_mul_of_one_le_right (by positivity) htwo

end SlopeBox
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopCovariantPacket
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scaled covariant derivative of a top-weighted packet is another
Schwartz packet. Its extra scalar factor is bounded by 8q independently
of the top size and the vertical carrier frequency. -/

noncomputable section
open FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

theorem topCovariantFactor_bound (b R y : ℝ) (q : ℕ) (hR : 0 < R) :
    |topCovariantFactor b R y q| ≤ 8*(q:ℝ) := by
  have hY : 0 < polynomialWeight b R q y :=
    zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)
  unfold topCovariantFactor
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4),
    abs_of_pos hR, abs_of_pos hY]
  apply (div_le_iff₀ hY).mpr
  calc
    _ ≤ 4*R*((2*(q:ℝ)/R)*polynomialWeight b R q y) :=
      mul_le_mul_of_nonneg_left (polynomialWeight_derivative b R y q hR) (by positivity)
    _ = _ := by field_simp; ring

theorem topCovariantWave_bound (f df : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖df x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖topCovariantWave f df a r b R y q x‖ ≤
      ((8*(q:ℝ)+1)*(16^q*(16^q*C)))*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have h1 := topWeightedWave_bound f a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC hf x
  have h2 := topWeightedWave_bound df a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC hdf x
  change ‖(topCovariantFactor b R y q:ℂ)*topWeightedWave f a r b R y q x +
    topWeightedWave df a r b R y q x‖ ≤ _
  calc
    _ ≤ ‖(topCovariantFactor b R y q:ℂ)*topWeightedWave f a r b R y q x‖ +
        ‖topWeightedWave df a r b R y q x‖ := norm_add_le _ _
    _ = |topCovariantFactor b R y q| *‖topWeightedWave f a r b R y q x‖ +
        ‖topWeightedWave df a r b R y q x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (8*(q:ℝ))*((16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y)) +
        (16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y) :=
      add_le_add (mul_le_mul (topCovariantFactor_bound b R y q hR) h1 (norm_nonneg _)
        (by positivity)) h2
    _ = _ := by ring

theorem topCovariantWave_derivative_bound (f df : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖df x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hfx : ∀ x, ‖deriv f x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hdfx : ∀ x, ‖deriv df x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖deriv (topCovariantWave f df a r b R y q) x‖ ≤
      (((8*(q:ℝ)+1)*(16^q*(1+2*(q:ℝ))*(16^q*C)))/l)*
        (lineEnvelope s l m x*lineEnvelope t W n y) := by
  have h1 := topWeightedWave_derivative_bound f a r b R y s l t W C q m n
    hl hr hW hR hlr hWR hs ht hC hf hfx x
  have h2 := topWeightedWave_derivative_bound df a r b R y s l t W C q m n
    hl hr hW hR hlr hWR hs ht hC hdf hdfx x
  have hd := (((topWeightedWave f a r b R y q).differentiable x).hasDerivAt.const_mul
    (topCovariantFactor b R y q:ℂ)).add
      ((topWeightedWave df a r b R y q).differentiable x).hasDerivAt
  change HasDerivAt (topCovariantWave f df a r b R y q) _ x at hd
  rw [hd.deriv]
  calc
    _ ≤ ‖(topCovariantFactor b R y q:ℂ)*deriv (topWeightedWave f a r b R y q) x‖ +
        ‖deriv (topWeightedWave df a r b R y q) x‖ := norm_add_le _ _
    _ = |topCovariantFactor b R y q| * ‖deriv (topWeightedWave f a r b R y q) x‖ +
        ‖deriv (topWeightedWave df a r b R y q) x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (8*(q:ℝ))*(((16^q*(1+2*(q:ℝ))*(16^q*C))/l)*
        (lineEnvelope s l m x*lineEnvelope t W n y)) +
        ((16^q*(1+2*(q:ℝ))*(16^q*C))/l)*(lineEnvelope s l m x*lineEnvelope t W n y) :=
      add_le_add (mul_le_mul (topCovariantFactor_bound b R y q hR) h1 (norm_nonneg _)
        (by positivity)) h2
    _ = _ := by ring

theorem topWeightedWave_covariant (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R y frequency x : ℝ) (q : ℕ)
    (hf : DifferentiableAt ℝ (fun t => f t x) y)
    (hdf : (4*R:ℂ)*(deriv (fun t => f t x) y-(frequency:ℂ)*Complex.I*f y x) = df y x) :
    (4*R:ℂ)*(deriv (fun t => topWeightedWave (f t) a r b R t q x) y -
      (frequency:ℂ)*Complex.I*topWeightedWave (f y) a r b R y q x) =
        topCovariantWave (f y) (df y) a r b R y q x := by
  have hY : polynomialWeight b R q y ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
  have hc : topCovariantFactor b R y q*polynomialWeight b R q y =
      4*R*deriv (polynomialWeight b R q) y := by
    exact div_mul_cancel₀ _ hY
  have hcC := congrArg (fun t : ℝ => (t:ℂ)) hc
  push_cast at hcC
  have hv := ((((polynomialWeight_differentiable b R q) y).hasDerivAt.ofReal_comp).mul
    hf.hasDerivAt).const_mul (polynomialWeight a r q x:ℂ)
  have heq : (fun t => (polynomialWeight a r q x:ℂ)*((polynomialWeight b R q t:ℂ)*f t x)) =
      (fun t => topWeightedWave (f t) a r b R t q x) := by
    funext t
    rw [topWeightedWave_apply]
    push_cast
    ring
  change HasDerivAt (fun t => (polynomialWeight a r q x:ℂ)*
    ((polynomialWeight b R q t:ℂ)*f t x)) _ y at hv
  rw [heq] at hv
  rw [hv.deriv]
  change _ = (topCovariantFactor b R y q:ℂ)*topWeightedWave (f y) a r b R y q x +
    topWeightedWave (df y) a r b R y q x
  simp only [topWeightedWave_apply]
  rw [← hdf]
  push_cast
  linear_combination -(polynomialWeight a r q x:ℂ)*(f y x)*hcC

theorem topCovariantWave_low (f df : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hflo : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hfhi : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0)
    (hdlo : ∀ ξ, |ξ| < lo → 𝓕 df ξ = 0)
    (hdhi : ∀ ξ, hi < |ξ| → 𝓕 df ξ = 0) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (topCovariantWave f df a r b R y q) ξ = 0 := by
  have hadd : (𝓕 (topCovariantWave f df a r b R y q) : SchwartzMap ℝ ℂ) =
      (topCovariantFactor b R y q:ℂ) • 𝓕 (topWeightedWave f a r b R y q) +
        𝓕 (topWeightedWave df a r b R y q) := by
    exact (fourier_add _ _).trans (congrArg (fun h : SchwartzMap ℝ ℂ =>
      h + 𝓕 (topWeightedWave df a r b R y q)) (fourier_smul _ _))
  rw [hadd]
  change (topCovariantFactor b R y q:ℂ)*𝓕 (topWeightedWave f a r b R y q) ξ +
    𝓕 (topWeightedWave df a r b R y q) ξ = 0
  rw [topWeightedWave_low f a r b R y q lo hi hflo hfhi ξ hξ,
    topWeightedWave_low df a r b R y q lo hi hdlo hdhi ξ hξ]
  simp

theorem topCovariantWave_high (f df : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hflo : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hfhi : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0)
    (hdlo : ∀ ξ, |ξ| < lo → 𝓕 df ξ = 0)
    (hdhi : ∀ ξ, hi < |ξ| → 𝓕 df ξ = 0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (topCovariantWave f df a r b R y q) ξ = 0 := by
  have hadd : (𝓕 (topCovariantWave f df a r b R y q) : SchwartzMap ℝ ℂ) =
      (topCovariantFactor b R y q:ℂ) • 𝓕 (topWeightedWave f a r b R y q) +
        𝓕 (topWeightedWave df a r b R y q) := by
    exact (fourier_add _ _).trans (congrArg (fun h : SchwartzMap ℝ ℂ =>
      h + 𝓕 (topWeightedWave df a r b R y q)) (fourier_smul _ _))
  rw [hadd]
  change (topCovariantFactor b R y q:ℂ)*𝓕 (topWeightedWave f a r b R y q) ξ +
    𝓕 (topWeightedWave df a r b R y q) ξ = 0
  rw [topWeightedWave_high f a r b R y q lo hi hflo hfhi ξ hξ,
    topWeightedWave_high df a r b R y q lo hi hdlo hdhi ξ hξ]
  simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopCovariantContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity and vertical differentiability of the constructed weighted
packet pair, derived from the original packets and their covariant waves. -/

noncomputable section
namespace LipschitzHilbert

theorem topCovariantFactor_continuous (b R : ℝ) (q : ℕ) :
    Continuous (fun y => topCovariantFactor b R y q) := by
  have hp : ContDiff ℝ 1 (polynomialWeight b R q) := by
    unfold polynomialWeight
    fun_prop
  exact (continuous_const.mul hp.continuous_deriv_one).div hp.continuous
    (fun y => ne_of_gt (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)))

theorem topWeightedWave_jointContinuous (f : ℝ → SchwartzMap ℝ ℂ)
    (a r b R : ℝ) (q : ℕ)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => topWeightedWave (f z.1) a r b R z.1 q z.2) := by
  simp only [topWeightedWave_apply]
  unfold polynomialWeight
  fun_prop

theorem topCovariantWave_jointContinuous (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R : ℝ) (q : ℕ)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hdf : Continuous (fun z : ℝ × ℝ => df z.1 z.2)) :
    Continuous (fun z : ℝ × ℝ => topCovariantWave (f z.1) (df z.1) a r b R z.1 q z.2) := by
  have h1 := topWeightedWave_jointContinuous f a r b R q hf
  have h2 := topWeightedWave_jointContinuous df a r b R q hdf
  have hc : Continuous (fun z : ℝ × ℝ => topCovariantFactor b R z.1 q) :=
    (topCovariantFactor_continuous b R q).comp continuous_fst
  change Continuous (fun z : ℝ × ℝ => (topCovariantFactor b R z.1 q:ℂ)*
    topWeightedWave (f z.1) a r b R z.1 q z.2 +
      topWeightedWave (df z.1) a r b R z.1 q z.2)
  exact ((Complex.continuous_ofReal.comp hc).mul h1).add h2

theorem topWeightedWave_vertical_differentiable (f : ℝ → SchwartzMap ℝ ℂ)
    (a r b R x y : ℝ) (q : ℕ) (hf : DifferentiableAt ℝ (fun t => f t x) y) :
    DifferentiableAt ℝ (fun t => topWeightedWave (f t) a r b R t q x) y := by
  have heq : (fun t => topWeightedWave (f t) a r b R t q x) =
      (fun t => (polynomialWeight a r q x:ℂ)*((polynomialWeight b R q t:ℂ)*f t x)) := by
    funext t
    rw [topWeightedWave_apply]
    push_cast
    ring
  rw [heq]
  exact (((((polynomialWeight_differentiable b R q) y).hasDerivAt.ofReal_comp).mul
    hf.hasDerivAt).const_mul _).differentiableAt

theorem topWeightedWave_covariant_continuous (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R frequency : ℝ) (q : ℕ) (hR : 0 < R)
    (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hdf : Continuous (fun z : ℝ × ℝ => df z.1 z.2))
    (hfd : ∀ x y, DifferentiableAt ℝ (fun t => f t x) y)
    (hcov : ∀ x y, (4*R:ℂ)*(deriv (fun t => f t x) y-(frequency:ℂ)*Complex.I*f y x) = df y x) :
    Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => topWeightedWave (f t) a r b R t q z.2) z.1 -
        (frequency:ℂ)*Complex.I*topWeightedWave (f z.1) a r b R z.1 q z.2) := by
  have heq : (fun z : ℝ × ℝ =>
      deriv (fun t => topWeightedWave (f t) a r b R t q z.2) z.1 -
        (frequency:ℂ)*Complex.I*topWeightedWave (f z.1) a r b R z.1 q z.2) =
      (fun z : ℝ × ℝ => (4*R:ℂ)⁻¹*topCovariantWave (f z.1) (df z.1) a r b R z.1 q z.2) := by
    funext z
    rw [← topWeightedWave_covariant f df a r b R z.1 frequency z.2 q
      (hfd z.2 z.1) (hcov z.2 z.1)]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hR.ne')
  rw [heq]
  exact continuous_const.mul (topCovariantWave_jointContinuous f df a r b R q hf hdf)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightedPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common packet constant for the weighted wave and its constructed
scaled covariant derivative. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

theorem topPairConstant_pos (C : ℝ) (q : ℕ) (hC : 0 < C) :
    0 < topPairConstant C q := by unfold topPairConstant; positivity

theorem topPairConstant_bounds (C : ℝ) (q : ℕ) (hC : 0 ≤ C) :
    16^q*(16^q*C) ≤ topPairConstant C q ∧
    16^q*(1+2*(q:ℝ))*(16^q*C) ≤ topPairConstant C q ∧
    (8*(q:ℝ)+1)*(16^q*(16^q*C)) ≤ topPairConstant C q := by
  have h1 : (1:ℝ) ≤ 1+2*(q:ℝ) := by nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have h8 : (1:ℝ) ≤ 8*(q:ℝ)+1 := by nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have hbase : 0 ≤ 16^q*(16^q*C) := by positivity
  have hder : 0 ≤ 16^q*(1+2*(q:ℝ))*(16^q*C) := by positivity
  have hb : 16^q*(16^q*C) ≤ 16^q*(1+2*(q:ℝ))*(16^q*C) := by
    convert le_mul_of_one_le_left hbase h1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hd : 16^q*(1+2*(q:ℝ))*(16^q*C) ≤ topPairConstant C q :=
    le_mul_of_one_le_left hder h8
  refine ⟨hb.trans hd, hd, ?_⟩
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem topWeightedPair_bound (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ i x, ‖f i x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (i : Fin 2) (x : ℝ) :
    ‖topWeightedPair f a r b R y q i x‖ ≤
      topPairConstant C q*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hconst := topPairConstant_bounds C q hC
  have henv : 0 ≤ lineEnvelope s l m x*lineEnvelope t W n y :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  fin_cases i
  · simpa [topWeightedPair] using
      (topWeightedWave_bound (f 0) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC (hf 0) x).trans
        (mul_le_mul_of_nonneg_right hconst.1 henv)
  · simpa [topWeightedPair] using
      (topCovariantWave_bound (f 0) (f 1) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hf 1) x).trans (mul_le_mul_of_nonneg_right hconst.2.2 henv)

theorem topWeightedPair_derivative_bound (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ i x, ‖f i x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hdf : ∀ i x, ‖deriv (f i) x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (i : Fin 2) (x : ℝ) :
    ‖deriv (topWeightedPair f a r b R y q i) x‖ ≤
      (topPairConstant C q/l)*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hconst := topPairConstant_bounds C q hC
  have henv : 0 ≤ lineEnvelope s l m x*lineEnvelope t W n y :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  fin_cases i
  · simpa [topWeightedPair] using
      (topWeightedWave_derivative_bound (f 0) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hdf 0) x).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hconst.2.1 hl.le) henv)
  · simpa [topWeightedPair, topPairConstant] using
      topCovariantWave_derivative_bound (f 0) (f 1) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hf 1) (hdf 0) (hdf 1) x

theorem topWeightedPair_low (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y : ℝ) (q : ℕ) (lo hi : ℝ)
    (hlow : ∀ i ξ, |ξ| < lo → 𝓕 (f i) ξ = 0)
    (hhigh : ∀ i ξ, hi < |ξ| → 𝓕 (f i) ξ = 0)
    (i : Fin 2) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (topWeightedPair f a r b R y q i) ξ = 0 := by
  fin_cases i
  · simpa [topWeightedPair] using
      topWeightedWave_low (f 0) a r b R y q lo hi (hlow 0) (hhigh 0) ξ hξ
  · simpa [topWeightedPair] using
      topCovariantWave_low (f 0) (f 1) a r b R y q lo hi
        (hlow 0) (hhigh 0) (hlow 1) (hhigh 1) ξ hξ

theorem topWeightedPair_high (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y : ℝ) (q : ℕ) (lo hi : ℝ)
    (hlow : ∀ i ξ, |ξ| < lo → 𝓕 (f i) ξ = 0)
    (hhigh : ∀ i ξ, hi < |ξ| → 𝓕 (f i) ξ = 0)
    (i : Fin 2) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (topWeightedPair f a r b R y q i) ξ = 0 := by
  fin_cases i
  · simpa [topWeightedPair] using
      topWeightedWave_high (f 0) a r b R y q lo hi (hlow 0) (hhigh 0) ξ hξ
  · simpa [topWeightedPair] using
      topCovariantWave_high (f 0) (f 1) a r b R y q lo hi
        (hlow 0) (hhigh 0) (hlow 1) (hhigh 1) ξ hξ

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteBandDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation commutes with the actual finite band sums.
The covariant derivative uses the same carrier in every band of a fixed
coordinate, so no carrier-frequency factor is lost. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem scalarBandPartial_hasDerivAt {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    HasDerivAt (scalarBandPartial F n)
      (scalarBandPartial (fun j => deriv (F j)) n y) y := by
  apply HasDerivAt.fun_sum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true, if_true] using (hF j).hasDerivAt
  · simpa only [hj, ite_false, if_false] using (hasDerivAt_const y (0:ℂ))

theorem scalarBandPartial_covariant {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (frequency y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    deriv (scalarBandPartial F n) y - (frequency:ℂ)*Complex.I*scalarBandPartial F n y =
      scalarBandPartial (fun j t => deriv (F j) t-(frequency:ℂ)*Complex.I*F j t) n y := by
  rw [(scalarBandPartial_hasDerivAt F n y hF).deriv]
  unfold scalarBandPartial
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem bandIntervalSignal_covariant {N : ℕ} {κ : Type*} [Fintype κ]
    (F : Fin N → κ → ℝ → ℂ) (a b : ℕ) (frequency : κ → ℝ) (y : ℝ)
    (hF : ∀ j k, DifferentiableAt ℝ (F j k) y) :
    covariantSignal frequency (fun k t => bandIntervalSignal F a b t k) y =
      bandIntervalSignal (fun j k t => deriv (F j k) t-
        (frequency k:ℂ)*Complex.I*F j k t) a b y := by
  ext k
  change deriv (fun t => scalarBandPartial (fun j => F j k) b t -
      scalarBandPartial (fun j => F j k) a t) y -
      (frequency k:ℂ)*Complex.I*(scalarBandPartial (fun j => F j k) b y -
        scalarBandPartial (fun j => F j k) a y) = _
  have hd := (scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).sub
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k))
  change HasDerivAt (fun t => scalarBandPartial (fun j => F j k) b t -
    scalarBandPartial (fun j => F j k) a t) _ y at hd
  rw [hd.deriv]
  have hb := scalarBandPartial_covariant (fun j => F j k) b (frequency k) y (fun j => hF j k)
  have ha := scalarBandPartial_covariant (fun j => F j k) a (frequency k) y (fun j => hF j k)
  change _ = scalarBandPartial _ b y - scalarBandPartial _ a y
  rw [← hb, ← ha]
  rw [(scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).deriv,
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k)).deriv]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDifferentiation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_hasDerivAt (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    HasDerivAt (planarPacketBand coeff wave j k x)
      (∑ i, coeff j i k * deriv (fun t => wave j i k t x) y) y := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hw i).hasDerivAt.const_mul _

omit [Fintype κ] in
theorem planarPacketBand_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    deriv (planarPacketBand coeff wave j k x) y -
      (frequency k:ℂ)*Complex.I*planarPacketBand coeff wave j k x y =
    planarPacketBand coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) j k x y := by
  rw [(planarPacketBand_hasDerivAt coeff wave j k x y hw).deriv]
  unfold planarPacketBand
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype κ] in
theorem planarPacketInterval_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => (s:ℂ)*wave j i k t z) a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  have hs (j : Fin N) (k : κ) :
      planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y =
        (s:ℂ)*planarPacketBand coeff wave j k x y := by
    simp only [planarPacketBand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp (n : ℕ) (k : κ) :
      scalarBandPartial (fun j => planarPacketBand coeff
        (fun j i k t z => (s:ℂ)*wave j i k t z) j k x) n y =
      (s:ℂ)*scalarBandPartial (fun j => planarPacketBand coeff wave j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hs, mul_zero]
  ext k
  change _ = (s:ℂ)*(_-_)
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, hp, mul_sub]

theorem planarPacketInterval_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (a b : ℕ) (x y : ℝ)
    (hw : ∀ j i k t, DifferentiableAt ℝ (fun z => wave j i k z x) t) :
    covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
    planarPacketInterval coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) a b x y := by
  unfold planarPacketInterval
  rw [bandIntervalSignal_covariant _ _ _ _ _ (fun j k =>
    (planarPacketBand_hasDerivAt coeff wave j k x y (fun i => hw j i k y)).differentiableAt)]
  congr 1
  funext j k t
  exact planarPacketBand_covariant coeff wave frequency j k x t
    (fun i => hw j i k t)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise multiplier identities for the actual finite planar packet
synthesis. A spatially varying multiplier is frozen at the evaluation
point before using linearity of the finite sum. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_congr_at (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ)
    (h : ∀ j i k, f j i k y x = g j i k y x) :
    planarPacketInterval coeff f a b x y = planarPacketInterval coeff g a b x y := by
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp,
    scalarBandPartial, planarPacketBand, h]

omit [Fintype κ] in
theorem planarPacketInterval_multiplier_at (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (M : ℝ → ℝ → ℝ)
    (h : ∀ j i k y x, g j i k y x = (M x y:ℂ)*f j i k y x)
    (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff g a b x y = (M x y) • planarPacketInterval coeff f a b x y := by
  rw [← planarPacketInterval_smul coeff f (M x y) a b x y]
  apply planarPacketInterval_congr_at
  exact fun j i k => h j i k y x

theorem planarPacketInterval_multiplier_norm (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f g : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (M : ℝ → ℝ → ℝ)
    (hM : ∀ x y, 0 ≤ M x y)
    (h : ∀ j i k y x, g j i k y x = (M x y:ℂ)*f j i k y x)
    (a b : ℕ) (x y : ℝ) :
    ‖planarPacketInterval coeff g a b x y‖ =
      M x y*‖planarPacketInterval coeff f a b x y‖ := by
  rw [planarPacketInterval_multiplier_at coeff f g M h, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (hM x y)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the coefficient normalization after the packet concentration
estimate, preserving the original integral-defined analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_coeff_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval (fun j i => s • coeff j i) wave a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  rw [← planarPacketInterval_smul coeff wave s a b x y]
  have hb (j : Fin N) (k : κ) (y : ℝ) :
      planarPacketBand (fun j i => s • coeff j i) wave j k x y =
        planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y := by
    apply Finset.sum_congr rfl
    intro i _
    change ((s:ℂ)*coeff j i k)*wave j i k y x = coeff j i k*((s:ℂ)*wave j i k y x)
    ring
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, scalarBandPartial, hb]

theorem planarPacketInterval_denormalize_bound (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (C B : ℝ) (hC : 0 < C)
    (a b : ℕ) (x y : ℝ)
    (h : ‖planarPacketInterval (fun j i => C⁻¹ • coeff j i) wave a b x y‖ ≤ B) :
    ‖planarPacketInterval coeff wave a b x y‖ ≤ C*B := by
  rw [planarPacketInterval_coeff_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hC)] at h
  have hh := mul_le_mul_of_nonneg_left h hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hh

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_TopRawPacketData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local packet data used by the top concentration argument. Every field
is a raw kernel, geometry, regularity, or Fourier-support condition; no
concentration or coefficient-budget assumption is included. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem topPacketAmplitude_pos (P : PlanarPacketFamily N κ ι) (Ab Am : ℝ) (D : ℕ) :
    0 < P.topPacketAmplitude Ab Am D := by
  have hC := topPairConstant_pos P.constant (8*D+1) P.constant_pos
  have hM := lineMomentBase_pos (topPairConstant P.constant (8*D+1))
    (Am*(topPairConstant P.constant (8*D+1))^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1)
    2 hC.le (by norm_num)
  have := P.coefficientScale_pos
  unfold topPacketAmplitude
  positivity

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelectedTopInterval
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the finite band interval with the selected
scale sum, preserving the actual analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_eq_selected
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (a b : ℕ) (hab : a ≤ b) (x y : ℝ) :
    planarPacketInterval c (fun j u k t s => f j u k t s) a b x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b),
        vectorPacketSynthesis (c j) (fun u k => f j u k y) x := by
  ext k
  simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,scalarBandPartial,
    WithLp.ofLp_sum,Finset.sum_apply,vectorPacketSynthesis,packetSynthesis_apply,
    planarPacketBand,Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp only [hja,hjb,ite_true, if_true,sub_self,not_le.mpr hja,false_and,ite_false, if_false,WithLp.ofLp_zero,Pi.zero_apply]
  · by_cases hjb : j.val < b
    · simp only [hja,hjb,ite_true, if_true,ite_false, if_false,sub_zero,not_lt.mp hja,true_and]
    · simp only [hja,hjb,ite_false, if_false,sub_self,and_false,WithLp.ofLp_zero,Pi.zero_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxHorizontalRescale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance of the physical slope boxes under horizontal dilation. -/

noncomputable section
namespace LipschitzHilbert.SlopeBox

theorem horizontalRescale_horizontal (T : SlopeBox) (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).horizontal z = T.horizontal (r*z.1,z.2) := by
  unfold horizontal horizontalRescale
  dsimp
  field_simp

theorem horizontalRescale_transverse (T : SlopeBox) (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).transverse z = T.transverse (r*z.1,z.2) := by
  unfold transverse horizontalRescale
  dsimp
  field_simp

theorem horizontalRescale_radius (T : SlopeBox) (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).radius z = T.radius (r*z.1,z.2) := by
  simp only [radius,horizontalRescale_horizontal,horizontalRescale_transverse]

theorem horizontalRescale_weight (T : SlopeBox) (r : ℝ) (hr : 0 < r) (K D : ℝ) (z : ℝ × ℝ) :
    (T.horizontalRescale r hr).weight K D z = T.weight K D (r*z.1,z.2) := by
  simp only [weight,horizontalRescale_radius]

end LipschitzHilbert.SlopeBox

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopFamilyException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common moment order sums all actual top exceptional sets with
the total top area. This is independent of the number of tops. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem topExceptionMoment_pos (M J L : ℝ) : 1 ≤ topExceptionMoment M J L := by
  unfold topExceptionMoment
  omega

theorem topExceptionMoment_le (M J L c : ℝ) (hJ : 0 ≤ J) (hL : 1 ≤ L)
    (hM : 1 ≤ M) (hlog : Real.log M ≤ c*L) :
    (topExceptionMoment M J L:ℝ) ≤ ((J+c)/Real.log 4+2)*L :=
  exponential_moment_order_le J c L M hJ hL hM hlog

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeTopNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the global lattice neighborhood bound to physical slope
coordinates and the exact top weight, with an exponential area bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem topAreaPrefactor_pos (K : ℝ) (hK : 0 < K) : 0 < topAreaPrefactor K := by
  unfold topAreaPrefactor
  positivity

theorem slope_top_neighborhood {ι E : Type*} [NormedAddCommGroup E]
    (T : SlopeBox) (K A J L : ℝ) (d : ℕ) (hK : 0 < K) (hA : 0 ≤ A)
    (F : ι → ℝ → ℝ → E)
    (hlocal : ∀ n : ℕ, 1 ≤ n → ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
        (2*ENNReal.ofReal (K*T.length)*ENNReal.ofReal (2*(K*T.width)))*
          ENNReal.ofReal ((4*Real.pi)^2) ∧
      ∀ i x y v, |v| ≤ K*T.width → (x,y) ∉ bad →
        ‖F i x (y+v)‖ ≤ A*(n:ℝ)*
          boxVariationWeight (packetBoxIndex T.x (T.y-T.slope*T.x)
            (K*T.length) (K*T.width) x y)^(8*d)) :
    let n := topExceptionMoment (topAreaPrefactor K) J L
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
      ∀ i z v, |v| ≤ K*T.width → z ∉ bad →
        ‖F i z.1 ((z.2-T.slope*z.1)+v)‖ ≤
          (A*(n:ℝ)*5^(8*d))*(T.weight K (d:ℝ) z)^8 := by
  dsimp only
  let n := topExceptionMoment (topAreaPrefactor K) J L
  obtain ⟨bad,hbad,harea,hpoint⟩ := hlocal n (topExceptionMoment_pos _ _ _)
  let physical := slopeShear T.slope '' bad
  have hphysical : MeasurableSet physical := (slopeShear T.slope).measurableSet_image.mpr hbad
  have hmeasure : (volume.prod volume) physical = (volume.prod volume) bad := by
    have h := (slopeShear_measurePreserving T.slope).measure_preimage_equiv physical
    rw [show (slopeShear T.slope) ⁻¹' physical = bad from
      Equiv.preimage_image _ _] at h
    exact h.symm
  have hfactor :
      (2*ENNReal.ofReal (K*T.length)*ENNReal.ofReal (2*(K*T.width)))*
        ENNReal.ofReal ((4*Real.pi)^2) =
      ENNReal.ofReal (topAreaPrefactor K)*ENNReal.ofReal T.area := by
    have hl := T.length_pos
    have hw := T.width_pos
    have htwo : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by norm_num
    rw [htwo, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(K*T.length)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(K*T.length)*(2*(K*T.width))),
      ← ENNReal.ofReal_mul (topAreaPrefactor_pos K hK).le]
    congr 1
    unfold topAreaPrefactor SlopeBox.area
    ring
  have hexp : (1/4:ℝ≥0∞)^n*ENNReal.ofReal (topAreaPrefactor K) ≤
      ENNReal.ofReal (Real.exp (-J*L)) := by
    have h := ENNReal.ofReal_le_ofReal
      (prefactor_quarter_successor_bound (topAreaPrefactor K) (J*L) (topAreaPrefactor_pos K hK))
    rw [ENNReal.ofReal_mul (topAreaPrefactor_pos K hK).le,
      ENNReal.ofReal_pow (by norm_num)] at h
    have hq : ENNReal.ofReal (1/4:ℝ) = (1/4:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hq, show -(J*L) = -J*L by ring] at h
    simpa only [n, topExceptionMoment, mul_comm] using h
  refine ⟨physical,hphysical,?_,?_⟩
  · rw [hmeasure]
    rw [mul_assoc, hfactor] at harea
    calc
      _ ≤ ((1/4:ℝ≥0∞)^n*ENNReal.ofReal (topAreaPrefactor K))*ENNReal.ofReal T.area := by
        simpa only [mul_assoc] using harea
      _ ≤ ENNReal.ofReal (Real.exp (-J*L))*ENNReal.ofReal T.area := mul_le_mul' hexp le_rfl
      _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  · intro i z v hv hout
    have hcoord : (z.1,z.2-T.slope*z.1) ∉ bad := by
      intro hin
      apply hout
      refine ⟨(z.1,z.2-T.slope*z.1),hin,?_⟩
      simp [slopeShear]
    have hp := hpoint i z.1 (z.2-T.slope*z.1) v hv hcoord
    have hdecay := T.lattice_decay_le_weight K hK d z
    exact hp.trans (by
      have h := mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA (Nat.cast_nonneg n))
      simpa only [mul_assoc] using h)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference-family analyzing coefficients are exactly the
original physical packet integrals. Swapping coordinates and applying
the reference slope shear preserves product Lebesgue measure, including
for the totalized Bochner integral without an integrability premise. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace LipschitzHilbert

theorem sourceReferenceToPhysical_measurePreserving (t : ℝ) :
    MeasurePreserving (sourceReferenceToPhysical t)
      (volume.prod volume) (volume.prod volume) :=
  (slopeShear_measurePreserving t).comp Measure.measurePreserving_swap

theorem integral_sourceReferenceToPhysical (t : ℝ) (F : ℝ × ℝ → ℂ) :
    (∫ z, F (sourceReferenceToPhysical t z) ∂volume.prod volume) =
      ∫ z, F z ∂volume.prod volume :=
  (sourceReferenceToPhysical_measurePreserving t).integral_comp
    (sourceReferenceToPhysical t).measurableEmbedding F

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

theorem family_selectedWave_physical (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (q : Σ j, ι j) (k : κ) (z : ℝ × ℝ) :
    P.family.selectedWave d (fun w => v (sourceReferenceToPhysical t w)) q k z =
      P.physicalSelectedWave t d v q k (sourceReferenceToPhysical t z) := by
  have h := congrArg (fun f : SchwartzMap ℝ ℂ => f z.2)
    (P.raw_eq_physical_slice 0 q.1 q.2 k z.1 t)
  change P.raw 0 q.1 q.2 k z.1 z.2 =
    P.physicalPacket t q.1 q.2 k (sourceReferenceToPhysical t z) at h
  change (if v (sourceReferenceToPhysical t z) ≤ d q.1 then
      P.raw 0 q.1 q.2 k z.1 z.2 else 0) =
    (if v (sourceReferenceToPhysical t z) ≤ d q.1 then
      P.physicalPacket t q.1 q.2 k (sourceReferenceToPhysical t z) else 0)
  split_ifs
  · exact h
  · rfl

/-- The normalized coefficient is unchanged by passing from the
physical packets to their reference-line family. Both the original
field and the original test function are pulled back by the same map. -/
theorem family_mainCoefficient_physical (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (u : ι j) :
    P.family.mainCoefficient d (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) j u =
      P.physicalCoefficient t d v g j u := by
  ext k
  simp only [PlanarPacketFamily.mainCoefficient, physicalCoefficient, analyzingCoefficient,
    WithLp.ofLp_toLp, family_length]
  change ((↑(P.length j * P.width) : ℂ)⁻¹) *
      (∫ z, g (sourceReferenceToPhysical t z) k * conj
        (P.family.selectedWave d (fun w => v (sourceReferenceToPhysical t w)) ⟨j, u⟩ k z)
          ∂volume.prod volume) =
    ((↑(P.length j * P.width) : ℂ)⁻¹) *
      (∫ z, g z k * conj (P.physicalSelectedWave t d v ⟨j, u⟩ k z)
        ∂volume.prod volume)
  congr 1
  simp_rw [P.family_selectedWave_physical]
  exact integral_sourceReferenceToPhysical t
    (fun z => g z k * conj (P.physicalSelectedWave t d v ⟨j, u⟩ k z))

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopCovariantData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A second raw covariant wave supplies the neighborhood estimate for
the first covariant derivative, while the analyzing coefficients stay fixed. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_scaled_covariant_eq
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave replacement : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (frequency : κ → ℝ) (s : ℝ) (a b : ℕ) (x y : ℝ)
    (hd : ∀ j u k t, DifferentiableAt ℝ (fun z => wave j u k z x) t)
    (hcov : ∀ j u k, (s:ℂ)*(deriv (fun z => wave j u k z x) y -
      (frequency k:ℂ)*Complex.I*wave j u k y x) = replacement j u k y x) :
    s • covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
      planarPacketInterval coeff replacement a b x y := by
  rw [planarPacketInterval_covariant coeff wave frequency a b x y hd,
    ← planarPacketInterval_smul]
  exact planarPacketInterval_congr_at coeff _ replacement a b x y hcov

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopAmplitudeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit top concentration amplitude is at most quadratic in
the raw packet constant, uniformly before all finite packet families. -/

noncomputable section
namespace LipschitzHilbert

theorem topPairConstant_linear (C : ℝ) (q : ℕ) :
    topPairConstant C q = topPairConstant 1 q*C := by
  unfold topPairConstant
  ring

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem normalized_coefficient_budget (P : PlanarPacketFamily N κ ι) (A : ℝ) :
    A*P.constant^2*P.coefficientScale⁻¹^2 = A/Real.pi^4 := by
  unfold coefficientScale
  field_simp [P.constant_pos.ne', Real.pi_ne_zero]

end PlanarPacketFamily

theorem uniform_topPacketAmplitude_bound (Ab Am : ℝ) (D : ℕ)
    (hAb : 0 < Ab) (hAm : 0 < Am) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι),
      P.topPacketAmplitude Ab Am D ≤ A*(P.constant+1)^2 := by
  let c := topPairConstant 1 (8*D+1)
  let b := Am*c^2*(Ab/Real.pi^4)+1
  let k := lineMomentBase c b 2
  let A := Real.pi^2*256^(8*D+1)*24*k
  have hc : 0 < c := topPairConstant_pos _ _ (by norm_num)
  have hb : 0 < b := by dsimp [b]; positivity
  have hk : 0 < k := lineMomentBase_pos c b 2 hc.le (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P
  have hconstant := P.constant_pos
  let t := P.constant+1
  have ht : 1 ≤ t := by dsimp [t]; linarith [P.constant_pos]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hpc : P.constant ≤ t := by dsimp [t]; linarith
  have hbudget := P.normalized_coefficient_budget Ab
  let C := topPairConstant P.constant (8*D+1)
  let S := Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1
  have hC : C = c*P.constant := topPairConstant_linear _ _
  have hCbound : C ≤ c*t := by rw [hC]; exact mul_le_mul_of_nonneg_left hpc hc.le
  have hS : S ≤ b*t^2 := by
    have ha : 0 ≤ Am*c^2*(Ab/Real.pi^4) := by positivity
    have hsq : P.constant^2 ≤ t^2 := pow_le_pow_left₀ P.constant_pos.le hpc 2
    have hone : (1:ℝ) ≤ t^2 := one_le_pow₀ ht
    calc
      S = (Am*c^2*(Ab/Real.pi^4))*P.constant^2+1 := by
        dsimp only [S]
        rw [hC,hbudget]
        ring
      _ ≤ (Am*c^2*(Ab/Real.pi^4))*t^2+t^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hsq ha) hone
      _ = b*t^2 := by dsimp [b]; ring
  have hsqrt : Real.sqrt S ≤ Real.sqrt b*t := by
    apply (Real.sqrt_le_sqrt hS).trans_eq
    rw [Real.sqrt_mul hb.le, Real.sqrt_sq ht0.le]
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hline : lineMomentBase C S 2 ≤ k*t := by
    calc
      lineMomentBase C S 2 ≤
          16*((4*(2*(Real.sqrt b*t)+4*((c*t)*(4*Real.pi)^2)))/Real.log (3/2)+
            Real.sqrt b*t+t) := by
        unfold lineMomentBase
        norm_num only
        gcongr
      _ = k*t := by dsimp [k,lineMomentBase]; ring
  calc
    P.topPacketAmplitude Ab Am D =
        P.constant*Real.pi^2*256^(8*D+1)*(24*lineMomentBase C S 2) := by
      rfl
    _ ≤ P.constant*Real.pi^2*256^(8*D+1)*(24*(k*t)) := by gcongr
    _ ≤ t*Real.pi^2*256^(8*D+1)*(24*(k*t)) := by gcongr
    _ = A*(P.constant+1)^2 := by dsimp [A,t]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial threshold pays for both the raw packet constant
and the moment order, before choosing any finite family or later mask. -/

noncomputable section
namespace LipschitzHilbert

theorem topAreaPrefactor_one_le : 1 ≤ topAreaPrefactor 1 := by
  unfold topAreaPrefactor
  nlinarith [Real.pi_pos, Real.two_le_pi]

theorem topAreaPrefactor_scale (K : ℝ) :
    topAreaPrefactor K = topAreaPrefactor 1*K^2 := by
  unfold topAreaPrefactor
  ring

theorem topExceptionMoment_power_le (J a L : ℝ) (hJ : 0 ≤ J)
    (ha : 0 ≤ a) (hL : 1 ≤ L) :
    (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤
      ((J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2)*L := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hK : 1 ≤ L^a := Real.one_le_rpow hL ha
  have hC := topAreaPrefactor_one_le
  have hM : 1 ≤ topAreaPrefactor (L^a) := by
    rw [topAreaPrefactor_scale]
    have hs : (1:ℝ) ≤ (L^a)^2 := one_le_pow₀ hK
    nlinarith
  have hlogbound : Real.log (topAreaPrefactor (L^a)) ≤
      (Real.log (topAreaPrefactor 1)+2*a)*L := by
    rw [topAreaPrefactor_scale (L^a), Real.log_mul (by positivity : topAreaPrefactor 1 ≠ 0)
      (by positivity : (L^a)^2 ≠ 0), Real.log_pow, Real.log_rpow hL0]
    have hlog : Real.log L ≤ L := Real.log_le_self hL0.le
    have hlogC := Real.log_nonneg hC
    norm_num only [Nat.cast_ofNat]
    calc
      _ = Real.log (topAreaPrefactor 1)+(2*a)*Real.log L := by ring
      _ ≤ Real.log (topAreaPrefactor 1)*L+(2*a)*L :=
        add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hlogC)
          (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = _ := by ring
  simpa only [add_assoc] using topExceptionMoment_le (topAreaPrefactor (L^a)) J L
    (Real.log (topAreaPrefactor 1)+2*a) hJ hL hM hlogbound

theorem exists_top_threshold (Ab Am J a p : ℝ) (D : ℕ)
    (hAb : 0 < Ab) (hAm : 0 < Am) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type) [Fintype κ] [∀ j, Fintype (ι j)]
        (P : PlanarPacketFamily N κ ι), P.constant ≤ L^p →
      P.topPacketAmplitude Ab Am D*
          (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ)*5^(8*D) ≤ L^(2*p+2) := by
  obtain ⟨A,hA,hamp⟩ := uniform_topPacketAmplitude_bound Ab Am D hAb hAm
  let B := (J+Real.log (topAreaPrefactor 1)+2*a)/Real.log 4+2
  let C := 4*A*B*5^(8*D)
  have hlogC := Real.log_nonneg topAreaPrefactor_one_le
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro L hL N κ ι _ _ P hP
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hCL : C ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hpow : 1 ≤ L^p := Real.one_le_rpow hL1 hp
  have hraw : P.constant+1 ≤ 2*L^p := by linarith
  have hconst := P.constant_pos
  have hamplitude : P.topPacketAmplitude Ab Am D ≤ 4*A*L^(2*p) := by
    calc
      _ ≤ A*(P.constant+1)^2 := hamp N κ ι P
      _ ≤ A*(2*L^p)^2 := by gcongr
      _ = 4*A*L^(2*p) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
        ring_nf
  have hn := topExceptionMoment_power_le J a L hJ ha hL1
  change (topExceptionMoment (topAreaPrefactor (L^a)) J L:ℝ) ≤ B*L at hn
  calc
    _ ≤ (4*A*L^(2*p))*(B*L)*5^(8*D) := by
      gcongr
    _ = C*L^(2*p+1) := by
      rw [Real.rpow_add hL0, Real.rpow_one]
      dsimp [C]
      ring
    _ ≤ L*L^(2*p+1) := mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0.le _)
    _ = L^(2*p+2) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hL0]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCoefficientIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded measurable tests make the original physical analyzing
integrals integrable, so coefficient polarization uses genuine linearity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem physicalSelectedWave_measurable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (q : Σ j, ι j) (k : κ) :
    Measurable (P.physicalSelectedWave t d v q k) :=
  Measurable.ite (measurableSet_le hv measurable_const)
    (P.physicalPacket t q.1 q.2 k).continuous.measurable measurable_const

theorem physicalSelectedWave_integrable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v) (q : Σ j, ι j) (k : κ) :
    Integrable (P.physicalSelectedWave t d v q k) (volume.prod volume) :=
  (P.physicalPacket t q.1 q.2 k).integrable.indicator (measurableSet_le hv measurable_const)

theorem physical_analyzing_integrable (t : ℝ) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (q : Σ j, ι j) (k : κ) :
    Integrable (fun z => g z k*conj (P.physicalSelectedWave t d v q k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalSelectedWave_integrable t d v hv q k).norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (P.physicalSelectedWave_measurable t d v hv q k))).aestronglyMeasurable
  filter_upwards [] with z
  dsimp only [Pi.mul_apply,Function.comp_apply]
  rw [norm_mul,norm_star]
  have hk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hk (norm_nonneg _)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePolarizedInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cross-profile source intervals and their four self-family
representation. Every coefficient is the original selected integral. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)

theorem rawInterval_scaled_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    P.scale • covariantSignal P.frequency
        (fun k t => P.rawInterval coeff 0 lower upper x t k) y =
      P.rawInterval coeff 1 lower upper x y := by
  apply planarPacketInterval_scaled_covariant_eq
  · intro j u k t
    exact modulatedPlanarJet_differentiable (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale t (P.length_pos j).ne' 0 x
  · intro j u k
    exact modulatedPlanarJet_covariant_zero (P.profile j u k) (P.actualX j u)
      (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
      P.scale y (P.length_pos j).ne' x

end LipschitzHilbert.SourceLatticePacket

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

theorem active_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k, selector i k t ≠ 0 →
      |t - slope i| ≤ radius * d) :
    (active labels selector t).card ≤ (2 * K + 1) * M := by
  classical
  apply (Finset.card_le_card (show active labels selector t ⊆
    window labels slope t d radius from ?_)).trans
    (window_card_le labels slope hd hlocal hK)
  intro i hi
  obtain ⟨hil, k, hk⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hil, by simpa only [abs_sub_comm] using hsupport i hil k hk⟩

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

/-- Selector separation is only needed for existing packets; therefore
it is inherited even when a slot is empty at some scales. -/
theorem slotted_selector (w cb Cb : ℝ)
    (hselector : ∀ j (l : P.labels j) (_u : Item j l),
      cb * w / P.length j ≤ |P.rowSlope j l| ∧
        |P.rowSlope j l| ≤ Cb * w / P.length j)
    (b : Fin B) (j : Fin N) (p : P.SlotItem hcard b j) :
    cb * w / (P.slotted hcard b).length j ≤ |(P.slotted hcard b).rowSlope j| ∧
      |(P.slotted hcard b).rowSlope j| ≤ Cb * w / (P.slotted hcard b).length j := by
  simpa only [P.slotted_rowSlope hcard b j p, P.slotted_length hcard] using
    hselector j p.1.1 p.1.2

end SourceLabeledLattice

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSlottedCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transport of selected analyzing integrals and cross-profile
packet sums through the finite slope-label splitting. These are algebraic
identities and require no concentration or integrability assumptions. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.SourceLabeledLattice

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

variable (P : SourceLabeledLattice N κ Label Item)

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j l u k,
    planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)

/-- Profile replacement commutes with the actual slot constructor. -/
theorem withProfile_slotted (b : Fin B) :
    (P.withProfile alt hAlt).slotted hcard b =
      (P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b) := by
  rfl

theorem slotted_alt_physicalPacket (b : Fin B) (t : ℝ) (j : Fin N)
    (p : P.SlotItem hcard b j) (k : κ) :
    ((P.slotted hcard b).withProfile (P.slottedAlt hcard alt b)
        (P.slottedAlt_bound hcard alt hAlt b)).physicalPacket t j p k =
      (P.withProfile alt hAlt).physicalPacket t j p.1.1 p.1.2 k := by
  rw [← P.withProfile_slotted hcard alt hAlt b]
  exact (P.withProfile alt hAlt).slotted_physicalPacket hcard b t j p k

omit alt hAlt hcard in
theorem rawInterval_scaled_covariant
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    P.scale • covariantSignal P.frequency
      (fun k t => P.rawInterval coeff 0 lower upper x t k) y =
        P.rawInterval coeff 1 lower upper x y := by
  unfold rawInterval
  apply planarPacketInterval_scaled_covariant_eq
  · intro j p k t
    exact modulatedPlanarJet_differentiable (P.profile j p.1 p.2 k) (P.actualX j p.1 p.2)
      (P.actualZ j p.1 p.2) (P.length j) P.width (-P.rowSlope j p.1) (P.frequency k)
      P.scale t (P.length_pos j).ne' 0 x
  · intro j p k
    exact modulatedPlanarJet_covariant_zero (P.profile j p.1 p.2 k) (P.actualX j p.1 p.2)
      (P.actualZ j p.1 p.2) (P.length j) P.width (-P.rowSlope j p.1) (P.frequency k)
      P.scale y (P.length_pos j).ne' x

omit alt hAlt in
theorem sum_slotted_rawInterval
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (∑ b : Fin B, (P.slotted hcard b).rawInterval
      (fun j p => coeff j p.1.1 p.1.2) i lower upper x y) =
      P.rawInterval coeff i lower upper x y := by
  have hband (j : Fin N) (k : κ) (y : ℝ) :
      (∑ b : Fin B, ∑ p : P.SlotItem hcard b j,
        coeff j p.1.1 p.1.2 k * (P.slotted hcard b).raw i j p k y x) =
      ∑ p : Σ l : P.labels j, Item j l, coeff j p.1 p.2 k * P.raw i j p.1 p.2 k y x := by
    simp_rw [P.slotted_raw hcard]
    simpa only [Fintype.sum_sigma] using
      P.sum_slotted hcard j (fun l u => coeff j l u k * P.raw i j l u k y x)
  have hpartial (n : ℕ) (k : κ) :
      (∑ b : Fin B, scalarBandPartial (fun j =>
        planarPacketBand (ι := P.SlotItem hcard b) (fun j p => coeff j p.1.1 p.1.2)
          (fun j p k t s => (P.slotted hcard b).raw i j p k t s) j k x) n y) =
      scalarBandPartial (fun j => planarPacketBand (ι := fun j => Σ l : P.labels j, Item j l)
        (fun j p => coeff j p.1 p.2)
        (fun j p k t s => P.raw i j p.1 p.2 k t s) j k x) n y := by
    unfold scalarBandPartial
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < n
    · simp only [hj, ite_true, if_true, planarPacketBand]
      exact hband j k y
    · simp only [hj, ite_false, if_false, Finset.sum_const_zero]
  ext k
  simp only [SourceLatticePacket.rawInterval, rawInterval, planarPacketInterval,
    bandIntervalSignal, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp]
  rw [Finset.sum_sub_distrib, hpartial, hpartial]

omit alt hAlt in
theorem sum_slotted_covariant (hscale : P.scale ≠ 0)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (lower upper : ℕ) (x y : ℝ) :
    (∑ b : Fin B, covariantSignal P.frequency (fun k t =>
      (P.slotted hcard b).rawInterval (fun j p => coeff j p.1.1 p.1.2)
        0 lower upper x t k) y) =
      covariantSignal P.frequency (fun k t => P.rawInterval coeff 0 lower upper x t k) y := by
  apply smul_right_injective (M := EuclideanSpace ℂ κ) hscale
  calc
    P.scale • (∑ b : Fin B, covariantSignal P.frequency (fun k t =>
        (P.slotted hcard b).rawInterval (fun j p => coeff j p.1.1 p.1.2)
          0 lower upper x t k) y) =
        ∑ b : Fin B, (P.slotted hcard b).rawInterval
          (fun j p => coeff j p.1.1 p.1.2) 1 lower upper x y := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact (P.slotted hcard b).rawInterval_scaled_covariant
        (fun j p => coeff j p.1.1 p.1.2) lower upper x y
    _ = P.rawInterval coeff 1 lower upper x y :=
      P.sum_slotted_rawInterval hcard coeff 1 lower upper x y
    _ = P.scale • covariantSignal P.frequency
        (fun k t => P.rawInterval coeff 0 lower upper x t k) y :=
      (P.rawInterval_scaled_covariant coeff lower upper x y).symm

end LipschitzHilbert.SourceLabeledLattice

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

theorem rawInterval_eq_band_sum (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    P.rawInterval coeff i lower upper x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.rawBand coeff i j x y := by
  have h := planarPacketInterval_eq_selected
    (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2)
    (fun j p k t => P.raw i j p.1 p.2 k t) lower upper hlu x y
  exact h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledCoefficientSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original labeled physical coefficient splits into its centered
frozen selector and angular error, without changing synthesis packets. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

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

theorem physicalMultiplierCoefficient_split (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    P.physicalMultiplierCoefficient t b v g j l u =
      P.physicalFrozenCenteredCoefficient t a b v g j l u+
        P.physicalAngularErrorCoefficient t a b v g j l u := by
  apply angularCoefficient_decomposition (fun _ : Item j l => P.length j*P.width)
    (fun _ k => b j l k) (fun u k => P.physicalPacket t j l u k) v t (a*(2:ℝ)^j.val) g
  · intro u k
    exact P.physical_multiplier_analyzing_integrable t (fun z => b j l k (v z))
      ((hb j l k).comp hv) (fun z => hb1 j l k (v z)) g hg hg1 j l u k
  · intro u k
    have hdist : Measurable (fun z => |v z-t|) := by
      simpa only [Real.norm_eq_abs] using (hv.sub_const t).norm
    have hm : Measurable (fun z : ℝ×ℝ =>
        if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0) :=
      Measurable.ite (measurableSet_le hdist measurable_const)
        measurable_const measurable_const
    have hm1 (z : ℝ×ℝ) :
        ‖if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0‖ ≤ 1 := by
      split_ifs
      · exact hb1 j l k t
      · simp only [norm_zero,zero_le_one]
    have h := P.physical_multiplier_analyzing_integrable t _ hm hm1 g hg hg1 j l u k
    simpa only [Measure.volume_eq_prod,ite_mul,zero_mul] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
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

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen selector values multiply the original Schwartz profiles.
They preserve the common seminorm bound, geometry and physical spectrum;
no new packet or concentration assumption is introduced. -/

noncomputable section
namespace LipschitzHilbert

theorem modulatedPlanarJet_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) :
    modulatedPlanarJet (c • f) a cy l W delta frequency scale y hl i =
      c • modulatedPlanarJet f a cy l W delta frequency scale y hl i := by
  ext x
  simp only [modulatedPlanarJet,modulatedPlanarSlice_apply,planarProfileJet_eq,
    planarVerticalJet_smul,smul_smul,smul_apply,smul_eq_mul]
  ring

theorem physicalPlanarPacket_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a b l W theta frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    physicalPlanarPacket (c • f) a b l W theta frequency hl hW =
      c • physicalPlanarPacket f a b l W theta frequency hl hW := by
  ext z
  simp only [physicalPlanarPacket_apply,smul_apply,smul_eq_mul]
  ring

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

@[simp] theorem frozenProfile_raw (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (P.frozenProfile c hc).raw i j u k y = c j u k • P.raw i j u k y := by
  exact modulatedPlanarJet_smul (P.profile j u k) (c j u k)
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j)
    (P.frequency k) P.scale y (P.length_pos j).ne' i

@[simp] theorem frozenProfile_physicalPacket (t : ℝ) (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).physicalPacket t j u k = c j u k • P.physicalPacket t j u k := by
  exact physicalPlanarPacket_smul (P.profile j u k) (c j u k)
    (P.actualX j u) (P.actualZ j u+t*P.actualX j u) (P.length j) P.width
    (t+P.rowSlope j) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceFrozenSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only a nonzero frozen selector needs annular separation. Zero
selectors give zero packets, so empty scales and unused labels impose no
artificial spectral hypothesis. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

/-- The same physical spectral wedge supplies the annuli of every
frozen raw jet. Separation is required precisely where the selector is
nonzero, rather than on all unused packet labels. -/
theorem frozenProfile_fourier_cutoffs (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hspectrum : ∀ j u k xi eta, planarAngularFourier (P.physicalPacket t j u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (hselector : ∀ j u k, c j u k ≠ 0 →
      cb*w/P.length j ≤ |P.rowSlope j| ∧ |P.rowSlope j| ≤ Cb*w/P.length j)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (∀ xi, |xi| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 ((P.frozenProfile c hc).raw i j u k y) xi = 0) ∧
    (∀ xi, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |xi| →
      𝓕 ((P.frozenProfile c hc).raw i j u k y) xi = 0) := by
  by_cases hz : c j u k = 0
  · rw [P.frozenProfile_raw,hz,zero_smul]
    simp
  have hsel : cb*w/P.length j ≤ |t-(t+P.rowSlope j)| ∧
      |t-(t+P.rowSlope j)| ≤ Cb*w/P.length j := by
    have heq : t-(t+P.rowSlope j) = -P.rowSlope j := by ring
    simpa only [heq,abs_neg] using hselector j u k hz
  have h := sourcePacket_jet_fourier_cutoffs (P.physicalPacket t j u k)
    y t (t+P.rowSlope j) (P.length j) w cStar cEta CEta cb Cb
    (P.length_pos j) hw hcEta hcb hCb (hspectrum j u k) hsel
    (P.frequency k) P.scale i
  have hraw : P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j u k) (P.frequency k) P.scale i) y t :=
    P.raw_eq_physical_slice i j u k y t
  have heq (A : ℝ) : A/(2*Real.pi*P.length j) =
      ((A/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val := by
    rw [length,packet_annulus_dyadic_scale A P.topLength j.val P.topLength_pos.ne']
    ring
  rw [← hraw,heq,heq] at h
  constructor
  · intro xi hxi
    rw [P.frozenProfile_raw,fourier_smul,smul_apply,h.1 xi hxi,smul_zero]
  · intro xi hxi
    rw [P.frozenProfile_raw,fourier_smul,smul_apply,h.2 xi hxi,smul_zero]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCenteredCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A symmetric reference cutoff is exactly three one-sided cutoffs,
including its boundary. No level-set nullity is required. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem physicalCenteredWave_eq (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) :
    P.physicalCenteredWave s t d v q k z =
      P.physicalSelectedWave s (fun j => t+d j) v q k z+
      P.physicalSelectedWave s (fun j => d j-t) (fun z => -v z) q k z-
      P.physicalSelectedWave s (fun _ => 0) (fun _ => 0) q k z := by
  have heq : |v z-t| ≤ d q.1 ↔ v z ≤ t+d q.1 ∧ -v z ≤ d q.1-t := by
    rw [abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  unfold physicalCenteredWave physicalSelectedWave
  simp only [heq]
  by_cases hu : v z ≤ t+d q.1 <;> by_cases hl : -v z ≤ d q.1-t
  · simp [hu,hl]
  · simp [hu,hl]
  · simp [hu,hl]
  · exfalso
    linarith [hd q.1]

/-- Exact coefficient identity used for symmetric frozen selectors.
All three terms have monotone thresholds whenever the original d does. -/
theorem physicalCenteredCoefficient_eq (s t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (u : ι j) :
    P.physicalCenteredCoefficient s t d v g j u =
      P.physicalCoefficient s (fun j => t+d j) v g j u+
      P.physicalCoefficient s (fun j => d j-t) (fun z => -v z) g j u-
      P.physicalCoefficient s (fun _ => 0) (fun _ => 0) g j u := by
  ext k
  have hU := P.physical_analyzing_integrable s (fun j => t+d j) v hv g hg hg1 ⟨j,u⟩ k
  have hD := P.physical_analyzing_integrable s (fun j => d j-t) (fun z => -v z)
    hv.neg g hg hg1 ⟨j,u⟩ k
  have hT := P.physical_analyzing_integrable s (fun _ => 0) (fun _ => 0)
    measurable_const g hg hg1 ⟨j,u⟩ k
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z) ∂volume.prod volume) = _
  simp_rw [P.physicalCenteredWave_eq s t d hd v,map_sub,map_add,mul_sub,mul_add]
  have hsub := integral_sub (hU.add hD) hT
  simp only [Pi.add_apply] at hsub
  rw [hsub,integral_add hU hD]
  change _ = ((↑(P.length j*P.width):ℂ)⁻¹)*_+
    ((↑(P.length j*P.width):ℂ)⁻¹)*_-((↑(P.length j*P.width):ℂ)⁻¹)*_
  ring

theorem centered_upper_monotone (t : ℝ) {d : Fin N → ℝ} (hd : Monotone d) :
    Monotone (fun j => t+d j) := by
  intro i j h
  dsimp only
  linarith [hd h]

theorem centered_lower_monotone (t : ℝ) {d : Fin N → ℝ} (hd : Monotone d) :
    Monotone (fun j => d j-t) := fun _ _ h => sub_le_sub_right (hd h) t

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-line packets are normalized at their actual horizontal
length before applying the published scalar variation input. The local
coefficient budget is independent of that length, the number of scales,
and the Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

variable (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

@[simp] theorem referenceAnalyzedLine_coeff (y : ℝ) (j : Fin N) (u : ι j) :
    (P.referenceAnalyzedLine d v hv g hg hg1 y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • P.family.mainCoefficient d v g j u := by
  dsimp only [referenceAnalyzedLine,PlanarPacketFamily.analyzedLine]
  dsimp only [referencePlanarFamily]
  rw [PlanarPacketFamily.horizontalRescale_mainCoefficient]
  rfl

variable {d v g}

theorem referencePlanarFamily_cutoffs {lo hi : ℝ}
    (hlow : ∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val → 𝓕 (P.raw 0 j u k y) xi = 0)
    (hhigh : ∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| → 𝓕 (P.raw 0 j u k y) xi = 0) :
    (∀ j u k y xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.referencePlanarFamily.wave j u k y) xi = 0) ∧
    (∀ j u k y xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.referencePlanarFamily.wave j u k y) xi = 0) := by
  constructor
  · intro j u k y xi hxi
    apply schwartzDilation_low (P.raw 0 j u k y) P.topLength (lo*(2:ℝ)^j.val) P.topLength_pos _ xi hxi
    intro eta heta
    apply hlow j u k y eta
    convert heta using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro j u k y xi hxi
    apply schwartzDilation_high (P.raw 0 j u k y) P.topLength (hi*(2:ℝ)^j.val) P.topLength_pos _ xi hxi
    intro eta heta
    apply hhigh j u k y eta
    convert heta using 1
    all_goals try with_reducible_and_instances rfl
    ring

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMixedReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference moments with distinct analyzing and synthesizing profiles.
The selector is frozen only in the analyzing coefficient; it is not
multiplied into the synthesis a second time. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

@[simp] theorem mixedReferenceLine_coeff (y : ℝ) (j : Fin N) (u : ι j) :
    (P.mixedReferenceLine c hc alt hAlt d v hv g hg hg1 y).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  (P.frozenProfile c hc).referenceAnalyzedLine_coeff d v hv g hg hg1 y j u

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskedSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The masked reference family synthesizes the original physical top
mask and alternate packet. Its analyzing coefficient is unchanged, so
the normalization is the original `constant * pi^2`, not its doubled
synthesis-envelope constant. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
  (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

variable (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ)

variable (hrate : ∀ j u, 2*(⌈L⌉₊:ℝ)*
  (|(T j u).maskLineA L A|+|(T j u).maskLineC L A t|) ≤ 1/P.length j)

@[simp] theorem maskedMixedReferenceLine_coeff (j : Fin N) (u : ι j) :
    (P.maskedMixedReferenceLine c hc alt hAlt d v hv g hg hg1 T L A t y hrate).coeff j u =
      (P.constant*Real.pi^2)⁻¹ • (P.frozenProfile c hc).family.mainCoefficient d v g j u :=
  P.mixedReferenceLine_coeff c hc alt hAlt d v hv g hg hg1 y j u

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive frozen main sum in the original labeled collection
is exactly the sum of the centered positive scales in its fixed slots.
The physical packets, coefficients and snapped envelopes are unchanged. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)

/-- Slotting and freezing reproduce the original centered physical
coefficient, with no integral or cutoff-boundary exception. -/
theorem frozenSlot_physicalCenteredCoefficient (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (s : Fin B) (j : Fin N) (p : P.SlotItem hcard s j) :
    (P.frozenSlot hcard t b hb s).physicalCenteredCoefficient t t
        (fun j => a*(2:ℝ)^j.val) v g j p =
      P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2 := by
  have hpacket (k : κ) (z : ℝ×ℝ) :
      (P.frozenSlot hcard t b hb s).physicalCenteredWave t t
          (fun j => a*(2:ℝ)^j.val) v ⟨j,p⟩ k z =
        if |v z-t| ≤ a*(2:ℝ)^j.val then
          b j p.1.1 k t*P.physicalPacket t j p.1.1 p.1.2 k z else 0 := by
    unfold SourceLatticePacket.physicalCenteredWave frozenSlot
    rw [(P.slotted hcard s).frozenProfile_physicalPacket,P.slotted_physicalPacket hcard]
    simp only [smul_apply,smul_eq_mul]
  ext k
  simp only [SourceLatticePacket.physicalCenteredCoefficient,
    physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, g z k*star ((P.frozenSlot hcard t b hb s).physicalCenteredWave t t
      (fun j => a*(2:ℝ)^j.val) v ⟨j,p⟩ k z) ∂volume.prod volume) = _
  simp_rw [hpacket]
  rfl

end LipschitzHilbert.SourceLabeledLattice

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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l) := by
  change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) = _
  ring

theorem referenceFamily_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (orig j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · change a ≤ newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) at hlo
      change a ≤ oldSlope+P.rowSlope j (orig j l)
      linarith
    · change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) < a+d at hhi
      change oldSlope+P.rowSlope j (orig j l) < a+d
      linarith
  · intro l _ m _ heq
    apply Subtype.ext
    exact congrArg (fun u : P.labels j => u.val) heq

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

theorem referenceFamily_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ j (l : P.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(oldSlope+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) :
    ∀ j (l : (Q).labels j) (u : Item j l) k ξ η,
      planarAngularFourier ((Q).physicalPacket newSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(newSlope+(Q).rowSlope j l)*η| ≤ cStar/(Q).length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta := by
  intro j l u k ξ η hξ
  rw [P.referenceFamily_physicalPacket oldSlope newSlope R cone w F hw hcone hF hwide hfrequency j l u k] at hξ
  have h := hspectrum j (P.referenceOriginalLabel oldSlope newSlope R cone w j l) u k ξ η hξ
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)+
      (oldSlope-newSlope)) = oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope R cone w j l) := by ring
  change |ξ+(newSlope+(P.rowSlope j
    (P.referenceOriginalLabel oldSlope newSlope R cone w j l)+(oldSlope-newSlope)))*η| ≤
      cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta
  rw [hs]
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopLabel_first (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j) : l.val.1 = top :=
  Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1

theorem assignedTopLabel_injective (j : Fin N) :
    Function.Injective (P.assignedTopLabel packets assigned top j) := by
  intro l m h
  apply Subtype.ext
  exact Prod.ext ((P.assignedTopLabel_first packets assigned top j l).trans
    (P.assignedTopLabel_first packets assigned top j m).symm) h

theorem assignedTopItem_mem (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (⟨j,⟨l.val.2,u.val⟩⟩ : P.PacketIndex) ∈ packets := u.property.1

theorem assignedTopItem_assignment (j : Fin N)
    (l : (P.assignedTopFamily packets assigned top).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    assigned ⟨j,⟨l.val.2,u.val⟩⟩ = top :=
  u.property.2.trans (P.assignedTopLabel_first packets assigned top j l)

theorem assignedTopFamily_localMultiplicity (t d : ℝ) (M : ℕ) (j : Fin N)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (P.assignedTopFamily packets assigned top).labels j =>
        t+(P.assignedTopFamily packets assigned top).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (P.assignedTopLabel packets assigned top j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlo,hhi⟩
  · intro l _ m _ h
    exact P.assignedTopLabel_injective packets assigned top j h

theorem assignedTopFamily_spectrum (t w cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier (P.physicalPacket t q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier ((P.assignedTopFamily packets assigned top).physicalPacket
        t j l u k) (xi,eta) ≠ 0 →
      |xi+(t+(P.assignedTopFamily packets assigned top).rowSlope j l)*eta| ≤
        cStar/(P.assignedTopFamily packets assigned top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro j l u k xi eta hn
  exact hspectrum ⟨j,⟨l.val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j l u)
    (P.assignedTopItem_assignment packets assigned top j l u) k xi eta hn


section Reference
variable (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w

theorem assignedTopReference_condition (j : Fin N) (l : (Q).labels j) :
    P.referenceCondition oldSlope newSlope R cone w j (orig j l).val.2 :=
  ((P.assignedTopFamily packets assigned top).referenceLabelsEquiv oldSlope newSlope R cone w j l).property

theorem assignedTopReference_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l).val.2 :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physical_center oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l

theorem assignedTopReference_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M :=
  (P.assignedTopFamily packets assigned top).referenceFamily_localMultiplicity oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j d M
      (P.assignedTopFamily_localMultiplicity packets assigned top oldSlope d M j hlocal)

theorem assignedTopReference_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier ((Q).physicalPacket newSlope j l u k) (xi,eta) ≠ 0 →
      |xi+(newSlope+(Q).rowSlope j l)*eta| ≤ cStar/(Q).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta :=
  (P.assignedTopFamily packets assigned top).referenceFamily_spectrum oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    cStar cEta CEta
    (P.assignedTopFamily_spectrum packets assigned top oldSlope w cStar cEta CEta hspectrum)

theorem assignedTopReference_alt_spectrum
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (cStar cEta CEta : ℝ)
    (hspectrum : ∀ q ∈ packets, assigned q = top → ∀ k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
        oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
      |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j l u k xi eta,
      planarAngularFourier (((Q).withProfile
        (fun j l u k => alt j (orig j l).val.2 u.val k)
        (fun j l u k => hAlt j (orig j l).val.2 u.val k)).physicalPacket
          newSlope j l u k) (xi,eta) ≠ 0 →
      |xi+(newSlope+(Q).rowSlope j l)*eta| ≤ cStar/(Q).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro j l u k xi eta hn
  have hp := (P.assignedTopFamily packets assigned top).referenceFamily_alternate_physicalPacket
    oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top) j l u k
  have hn' : planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
      oldSlope j (orig j l).val.2 u.val k) (xi,eta) ≠ 0 := by
    intro hz
    apply hn
    exact (congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => planarAngularFourier f (xi,eta)) hp).trans hz
  have hs := hspectrum ⟨j,⟨(orig j l).val.2,u.val⟩⟩
    (P.assignedTopItem_mem packets assigned top j (orig j l) u)
    (P.assignedTopItem_assignment packets assigned top j (orig j l) u) k xi eta hn'
  have hc := P.assignedTopReference_physical_center packets assigned top oldSlope newSlope
    R cone w F hw hcone hF hwide hfrequency j l
  refine ⟨?_,hs.2⟩
  exact (congrArg (fun r : ℝ => |xi+r*eta|) hc).le.trans hs.1

theorem assignedTopReference_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : (Q).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l).val.2) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency (P.assignedTopSelector packets assigned top b) v f j l u

end Reference

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact original-selector interval splitting for top concentration.
All three raw covariant jets use the original analyzing coefficients.
Only the frozen-centered synthesis needs a variation estimate; the
remaining interval is controlled by the positive angular error. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem selector_rawBand_split
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (j : Fin N) (x y : ℝ) :
    (P.withProfile alt hAlt).rawBand (P.physicalMultiplierCoefficient t b v g) i j x y =
      (P.withProfile alt hAlt).rawBand (P.physicalFrozenCenteredCoefficient t a b v g) i j x y+
      (P.withProfile alt hAlt).rawBand (P.physicalAngularErrorCoefficient t a b v g) i j x y := by
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,WithLp.ofLp_toLp,PiLp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [P.physicalMultiplierCoefficient_split t a b hb hb1 v hv g hg hg1]
  simp only [PiLp.add_apply]
  ring

theorem selector_rawInterval_split
    (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hv : Measurable v) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    (P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v g)
        i lower upper x y =
      (P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
        i lower upper x y+
      (P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
        i lower upper x y := by
  rw [(P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,
    (P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,
    (P.withProfile alt hAlt).rawInterval_eq_band_sum _ _ _ _ hlu,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ =>
    P.selector_rawBand_split alt hAlt t a b v g hb hb1 hv hg hg1 i j x y

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledMainRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only nonzero frozen selectors enter the positive main scale.
Restricting to their fixed narrow reference cone is exact, and changes
the carrier bound without changing any retained physical packet or
positive envelope. The wide error family is not used in the main tail. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalFrozenCenteredCoefficient_eq_zero (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) (hz : ∀ k, b j l k t = 0) :
    P.physicalFrozenCenteredCoefficient t a b v g j l u = 0 := by
  ext k
  simp only [physicalFrozenCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp,
    hz k,zero_mul,ite_self,map_zero,mul_zero,integral_zero,PiLp.zero_apply]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveReference
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow main reference family retains only labels active at the
frozen direction. Inactive labels contribute exactly zero, so neither
the square nor the masked variation needs spectral assumptions there. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

theorem sum_frozenActive_of_zero {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, (∀ k, b j l k t = 0) → ∀ u, f l u = 0) :
    (∑ l : P.frozenActiveLabels t b j, ∑ u : Item j l,
      f (P.frozenActiveOriginalLabel t b j l) u) =
        ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have heq := Equiv.sum_comp (P.frozenActiveLabelsEquiv t b j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j // ¬∃ k, b j l k t ≠ 0},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro u _
    exact hzero l.val (fun k => by
      by_contra hn
      exact l.property ⟨k,hn⟩) u
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun l : P.labels j => ∃ k, b j l k t ≠ 0)
    (fun l => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact heq.trans hsum

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationActive
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only frozen-active labels enter the centered main term. Their actual
angular separation bounds the modulation parameter, independently of
the wide cone used for the positive angular error. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

variable (w F Cb : ℝ) (hw : 0 < w) (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
  (hfreq : ∀ k, |P.frequency k| ≤ F/w)
  (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j)
local notation "Q" => P.activeMainFamily t b w F Cb hw hF hCb hfreq hangle

theorem activeMainFamily_constant : (Q).constant = P.absoluteConstant*(F*Cb+2) := by
  unfold constant absoluteConstant activeMainFamily frozenActiveFamily
  ring

theorem activeMainFamily_rawInterval
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    ((Q).withProfile
        (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
        (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l))).rawInterval
      ((Q).physicalFrozenCenteredCoefficient t a (P.frozenActiveSelector t b) v g)
      i lower upper x y =
    (P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
      i lower upper x y := by
  rw [rawInterval_eq_band_sum _ _ _ _ _ hlu,rawInterval_eq_band_sum _ _ _ _ _ hlu]
  apply Finset.sum_congr rfl
  intro j _
  ext k
  simp only [rawBand,vectorPacketSynthesis,packetSynthesis_apply,WithLp.ofLp_toLp,
    Fintype.sum_sigma]
  exact P.sum_frozenActive_of_zero t b j
    (fun l u => P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      (P.withProfile alt hAlt).raw i j l u k y x)
    (fun l hz u => by
      have hzero := congrArg (fun c : EuclideanSpace ℂ κ => c k)
        (P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz)
      rw [hzero]
      simp)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedLabeledGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packetwise top geometry survives slotting and frozen-active label
restriction. These operations keep every retained center and length. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- The actual packet-center condition already controls retained lengths. -/
theorem supportedTopGeometry {T : SlopeBox} {K : ℝ} {D : ℕ}
    (hwidth : P.width ≤ K*T.width)
    (hx : ∀ j l u, |P.actualX j l u-T.x|+P.length j ≤ K*T.length)
    (hz : ∀ j l u, |P.actualZ j l u-(T.y-T.slope*T.x)|+P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width)) :
    SourceSupportedLabeledTopGeometry P T K D where
  length_le := fun j l u => by linarith [hx j l u,abs_nonneg (P.actualX j l u-T.x)]
  width_le := hwidth
  centerX_le := hx
  centerZ_le := hz
  order_le := horder
  scale_eq := hscale

theorem slotted_supportedTopGeometry
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D)
    (b : Fin B) : SourceSupportedLatticeTopGeometry (P.slotted hcard b) T K D where
  length_le := fun j p => G.length_le j p.1.1 p.1.2
  width_le := G.width_le
  centerX_le := by
    intro j p
    rw [P.slotted_actualX hcard, P.slotted_length hcard]
    exact G.centerX_le j p.1.1 p.1.2
  centerZ_le := by
    intro j p
    rw [P.slotted_actualZ hcard]
    exact G.centerZ_le j p.1.1 p.1.2
  order_le := G.order_le
  scale_eq := G.scale_eq

theorem activeMainFamily_supportedTopGeometry
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (w F Cb : ℝ) (hw : 0 < w) (hF : 0 ≤ F) (hCb : 0 ≤ Cb)
    (hfreq : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ j l, (∃ k, b j l k t ≠ 0) → |P.rowSlope j l| ≤ Cb*w/P.length j)
    {T : SlopeBox} {K : ℝ} {D : ℕ} (G : SourceSupportedLabeledTopGeometry P T K D) :
    SourceSupportedLabeledTopGeometry
      (P.activeMainFamily t b w F Cb hw hF hCb hfreq hangle) T K D where
  length_le := fun j l u => G.length_le j (P.frozenActiveOriginalLabel t b j l) u
  width_le := G.width_le
  centerX_le := fun j l u => G.centerX_le j (P.frozenActiveOriginalLabel t b j l) u
  centerZ_le := fun j l u => G.centerZ_le j (P.frozenActiveOriginalLabel t b j l) u
  order_le := G.order_le
  scale_eq := G.scale_eq

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedSupportedGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned reference geometry follows from the centers of the selected
packets. No global longest-scale hypothesis is required. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)

theorem assignedTopReference_supportedTopGeometry
    (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (T : SlopeBox) (K : ℝ) (D : ℕ)
    (hwidth : P.width ≤ K*T.width)
    (horder : 3+2*(8*D+1) ≤ P.order) (hscale : P.scale = 4*(K*T.width))
    (hX : ∀ q ∈ packets, assigned q = top →
      |P.actualX q.1 q.2.1 q.2.2-T.x|+P.length q.1 ≤ K*T.length)
    (hZ : ∀ q ∈ packets, assigned q = top →
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-T.slope)*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|+P.width ≤ K*T.width) :
    SourceSupportedLabeledTopGeometry
      ((P.assignedTopFamily packets assigned top).referenceFamily oldSlope T.slope R cone w F
        hw hcone hF hwide hfrequency) T K D := by
  let A := P.assignedTopFamily packets assigned top
  apply (A.referenceFamily oldSlope T.slope R cone w F
    hw hcone hF hwide hfrequency).supportedTopGeometry hwidth ?_ ?_ horder hscale
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    exact hX ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u)
  · intro j l u
    let l' := A.referenceOriginalLabel oldSlope T.slope R cone w j l
    have hz := A.referenceFamily_actualZ oldSlope T.slope R cone w F
      hw hcone hF hwide hfrequency j l u
    have he := congrArg (fun z : ℝ => |z-(T.y-T.slope*T.x)|+P.width) hz
    exact he.le.trans (hZ ⟨j,⟨l'.val.2,u.val⟩⟩
      (P.assignedTopItem_mem packets assigned top j l' u)
      (P.assignedTopItem_assignment packets assigned top j l' u))


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationJoint
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact linearity of the covariant signal and the joint triangle
bound for the original selector coefficient split. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

include hb hb1 hv hg hg1

theorem selector_covariantInterval_split (hscale : P.scale ≠ 0)
    (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient t b v g) 0 lower upper x yy k) y =
    covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalFrozenCenteredCoefficient t a b v g) 0 lower upper x yy k) y+
    covariantSignal P.frequency
      (fun k yy => (P.withProfile alt hAlt).rawInterval
        (P.physicalAngularErrorCoefficient t a b v g) 0 lower upper x yy k) y := by
  let Q := P.withProfile alt hAlt
  apply (smul_right_injective (M := EuclideanSpace ℂ κ) (by exact hscale : Q.scale ≠ 0))
  change Q.scale • _ = Q.scale • _
  rw [smul_add,Q.rawInterval_scaled_covariant,Q.rawInterval_scaled_covariant,
    Q.rawInterval_scaled_covariant]
  exact P.selector_rawInterval_split alt hAlt t a b v g hb hb1 hv hg hg1
    1 lower upper hlu x y

theorem selector_jointInterval_le (hscale : P.scale ≠ 0)
    (lower upper : ℕ) (hlu : lower ≤ upper) (W : ℝ) (hW : 0 ≤ W) (x y : ℝ) :
    ‖(P.withProfile alt hAlt).rawInterval (P.physicalMultiplierCoefficient t b v g)
      0 lower upper x y‖+W*‖covariantSignal P.frequency
        (fun k yy => (P.withProfile alt hAlt).rawInterval
          (P.physicalMultiplierCoefficient t b v g) 0 lower upper x yy k) y‖ ≤
    (‖(P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
      0 lower upper x y‖+W*‖covariantSignal P.frequency
        (fun k yy => (P.withProfile alt hAlt).rawInterval
          (P.physicalFrozenCenteredCoefficient t a b v g) 0 lower upper x yy k) y‖)+
    (‖(P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
      0 lower upper x y‖+W*‖covariantSignal P.frequency
        (fun k yy => (P.withProfile alt hAlt).rawInterval
          (P.physicalAngularErrorCoefficient t a b v g) 0 lower upper x yy k) y‖) := by
  rw [P.selector_rawInterval_split alt hAlt t a b v g hb hb1 hv hg hg1 0 lower upper hlu,
    P.selector_covariantInterval_split alt hAlt t a b hb hb1 v hv g hg hg1 hscale
      lower upper hlu x y]
  have hval := norm_add_le
    ((P.withProfile alt hAlt).rawInterval (P.physicalFrozenCenteredCoefficient t a b v g)
      0 lower upper x y)
    ((P.withProfile alt hAlt).rawInterval (P.physicalAngularErrorCoefficient t a b v g)
      0 lower upper x y)
  have hcov := mul_le_mul_of_nonneg_left (norm_add_le
    (covariantSignal P.frequency (fun k yy => (P.withProfile alt hAlt).rawInterval
      (P.physicalFrozenCenteredCoefficient t a b v g) 0 lower upper x yy k) y)
    (covariantSignal P.frequency (fun k yy => (P.withProfile alt hAlt).rawInterval
      (P.physicalAngularErrorCoefficient t a b v g) 0 lower upper x yy k) y)) hW
  linarith

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationCenteredFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered main part has one weighted physical exception for all
tops and both required jets. Three monotone cutoffs produce only a fixed
loss, absorbed in the polynomial threshold. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

/-- Exact centered interval identity, including cutoff boundaries. -/
theorem frozen_centered_rawInterval_eq
    (P : SourceLatticePacket N κ ι)
    (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (d : Fin N → ℝ) (hd : ∀ j, 0 ≤ d j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (P.withProfile alt hAlt).rawInterval
        ((P.frozenProfile c hc).physicalCenteredCoefficient t t d v g) i lower upper x y =
      (P.withProfile alt hAlt).rawInterval
        ((P.frozenProfile c hc).physicalCoefficient t (fun j => t+d j) v g) i lower upper x y+
      (P.withProfile alt hAlt).rawInterval
        ((P.frozenProfile c hc).physicalCoefficient t (fun j => d j-t) (fun z => -v z) g)
        i lower upper x y-
      (P.withProfile alt hAlt).rawInterval
        ((P.frozenProfile c hc).physicalCoefficient t (fun _ => 0) (fun _ => 0) g)
        i lower upper x y := by
  let C := (P.frozenProfile c hc).physicalCenteredCoefficient t t d v g
  let U := (P.frozenProfile c hc).physicalCoefficient t (fun j => t+d j) v g
  let V := (P.frozenProfile c hc).physicalCoefficient t (fun j => d j-t) (fun z => -v z) g
  let W := (P.frozenProfile c hc).physicalCoefficient t (fun _ => 0) (fun _ => 0) g
  let wave := fun j u k yy xx => (P.withProfile alt hAlt).raw i j u k yy xx
  have hC j u : C j u = U j u+V j u-W j u :=
    (P.frozenProfile c hc).physicalCenteredCoefficient_eq t t d hd v hv g hg hg1 j u
  have hband j k yy : planarPacketBand C wave j k x yy =
      planarPacketBand U wave j k x yy+planarPacketBand V wave j k x yy-
        planarPacketBand W wave j k x yy := by
    simp only [planarPacketBand,hC,PiLp.add_apply,PiLp.sub_apply]
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hpartial n k : scalarBandPartial (fun j => planarPacketBand C wave j k x) n y =
      scalarBandPartial (fun j => planarPacketBand U wave j k x) n y+
      scalarBandPartial (fun j => planarPacketBand V wave j k x) n y-
      scalarBandPartial (fun j => planarPacketBand W wave j k x) n y := by
    simp only [scalarBandPartial,hband]
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  change planarPacketInterval C wave lower upper x y =
    planarPacketInterval U wave lower upper x y+
    planarPacketInterval V wave lower upper x y-
    planarPacketInterval W wave lower upper x y
  ext k
  simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,
    PiLp.add_apply,PiLp.sub_apply,hpartial]
  ring

/-- Each one-sided physical coefficient is the same original reference
integral after the measure-preserving shear. -/
theorem frozen_physical_rawInterval_eq_reference
    (P : SourceLatticePacket N κ ι)
    (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    (P.withProfile alt hAlt).rawInterval
        ((P.frozenProfile c hc).physicalCoefficient t d v g) i lower upper x y =
      (P.withProfile alt hAlt).rawInterval
        ((P.frozenProfile c hc).family.mainCoefficient d
          (fun z => v (sourceReferenceToPhysical t z))
          (fun z => g (sourceReferenceToPhysical t z))) i lower upper x y := by
  have heq : (P.frozenProfile c hc).family.mainCoefficient d
      (fun z => v (sourceReferenceToPhysical t z))
      (fun z => g (sourceReferenceToPhysical t z)) =
      (P.frozenProfile c hc).physicalCoefficient t d v g := by
    funext j u
    exact (P.frozenProfile c hc).family_mainCoefficient_physical t d v g j u
  rw [heq]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSelectorConcentrationMainSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-slot recombination of the centered main concentration. The
slot index is confined to local concentration, and the result again has
the original top index and the original physical coefficients. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem frozenSlot_rawInterval (P : SourceLabeledLattice N κ Label Item)
    {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
    (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (s : Fin B) (i : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    ((P.slotted hcard s).withProfile (P.slottedAlt hcard alt s)
        (P.slottedAlt_bound hcard alt hAlt s)).rawInterval
      ((P.frozenSlot hcard t b hb s).physicalCenteredCoefficient t t
        (fun j => a*(2:ℝ)^j.val) v g) i lower upper x y =
    ((P.withProfile alt hAlt).slotted hcard s).rawInterval
      (fun j u => P.physicalFrozenCenteredCoefficient t a b v g j u.1.1 u.1.2)
      i lower upper x y := by
  have hc : (P.frozenSlot hcard t b hb s).physicalCenteredCoefficient t t
      (fun j => a*(2:ℝ)^j.val) v g =
      fun j u => P.physicalFrozenCenteredCoefficient t a b v g j u.1.1 u.1.2 := by
    funext j u
    exact P.frozenSlot_physicalCenteredCoefficient hcard t a b hb v g s j u
  rw [hc,← P.withProfile_slotted hcard alt hAlt s]
  rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledActiveCardTail
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only frozen-active labels need slots in the main reference tail.
Their cardinality follows from the original local slope multiplicity,
uniformly over the number of vector coordinates and inactive labels. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem frozenActiveLabels_card_local (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (j : Fin N) {d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => t+P.rowSlope j l) d M)
    (hK : radius ≤ K)
    (hsupport : ∀ l k, b j l k t ≠ 0 →
      |t-(t+P.rowSlope j l)| ≤ radius*d) :
    (P.frozenActiveLabels t b j).card ≤ (2*K+1)*M := by
  have h := SourceSlopeLabels.active_card_le Finset.univ
    (fun l : P.labels j => t+P.rowSlope j l) (b j) hd hlocal hK
    (fun l _ k hk => hsupport l k hk)
  have hc := Fintype.card_congr (P.frozenActiveLabelsEquiv t b j)
  rw [Fintype.card_coe,Fintype.card_subtype] at hc
  apply hc.trans_le
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext l
  simp only [SourceSlopeLabels.active,Finset.mem_filter,Finset.mem_univ,true_and]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedAnalyzedGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PlanarPacketFamily

theorem analyzed_global_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (_hderiv : ∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)),
      Monotone d →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (C r : ℝ), 0 < C → 0 < r →
      (∀ i y j u k x, ‖synth i j u k y x‖ ≤ C*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k x, ‖deriv (synth i j u k y) x‖ ≤ (C/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => synth 0 j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => synth 0 j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2)) →
      ∀ (raw : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (baseX baseZ rx : ℝ) (q : ℕ),
      0 < rx → 1 ≤ q → (∀ j (_u : ι j), P.length j ≤ rx) →
      (∀ j u k y x, synth 0 j u k y x =
        (polynomialWeight baseX rx q x*polynomialWeight baseZ r q y : ℝ)*raw j u k y x) →
      ∀ (branching : ℕ), 1 < branching → ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
          (2*ENNReal.ofReal rx*ENNReal.ofReal (2*r))*ENNReal.ofReal ((4*Real.pi)^2) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w, |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
            raw a b x (z+w)‖ ≤
              256^q*(24*K*(n:ℝ))*boxVariationWeight (packetBoxIndex baseX baseZ rx r x z)^(q-1) := by
  obtain ⟨Ab,Am,hAb,hAm,hlocal⟩ := analyzed_interval_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hderiv hd hlow hhigh synth frequency C r hC hr
    hbound hdbound hslow hshigh hcov hcont hdiff hD raw baseX baseZ rx q hrx hq hwidth
    hmult branching hbranch n hn
  dsimp only
  let coeff := fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u
  let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) branching
  let J := {ab : ℕ × ℕ // ab.1 ≤ ab.2 ∧ ab.2 ≤ N}
  let F : J → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval coeff raw ab.val.1 ab.val.2 x y
  have hK : 0 ≤ K := (lineMomentBase_pos _ _ _ hC.le (Nat.cast_nonneg _)).le
  have hall := global_top_neighborhood_of_local F baseX baseZ rx r (8*K) hrx hr
    (by positivity) (2*ENNReal.ofReal rx*ENNReal.ofReal (2*r)) n q hn hq (by
      intro p m hm
      let grid : FiniteLineGrid := {
        branching := branching
        branching_pos := lt_trans Nat.zero_lt_one hbranch
        origin := baseX+rx*p.1
        width := rx
        width_pos := hrx
        depth := N }
      have hroot : grid.root = Ico (baseX+rx*p.1) (baseX+rx*((p.1:ℝ)+1)) := by
        unfold FiniteLineGrid.root
        dsimp [grid]
        congr 1
        ring
      have hvolume : grid.lineMeasure univ = ENNReal.ofReal rx := by
        rw [FiniteLineGrid.lineMeasure, Measure.restrict_apply_univ]
        unfold FiniteLineGrid.root
        rw [Real.volume_Ico]
        congr 1
        dsimp [grid]
        ring
      obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := hlocal N κ ι P d v hv g hg hg1 hderiv hd hlow hhigh
        synth frequency C (baseZ+r*p.2) r hC hr hbound hdbound hslow hshigh hcov hcont hdiff hD
        grid hbranch hwidth m hm
      refine ⟨bad,hbad,?_,?_⟩
      · rw [hvolume] at harea
        convert harea using 1
        all_goals try with_reducible_and_instances rfl
        ring
      · intro ab x z w hx hz hw hout
        have hx' : x ∈ grid.root := by rw [hroot]; exact hx
        have hp := hpoint ab.val.1 ab.val.2 ab.property.1 ab.property.2 x z w hx' hz hw hout
        have heq := planarPacketInterval_multiplier_norm coeff raw
          (fun j u k y x => synth 0 j u k y x)
          (fun x y => polynomialWeight baseX rx q x*polynomialWeight baseZ r q y)
          (fun x y => mul_nonneg (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))
            (zero_le_one.trans (polynomialWeight_one_le _ _ _ _))) hmult ab.val.1 ab.val.2 x (z+w)
        rw [← heq]
        exact hp)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hall
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb x z w hw hout
  have hp := hpoint (⟨(a,b),hab,hb⟩ : J) x z w hw hout
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedSynthesisNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_synthesis_global_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone d →
      (∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (baseX baseZ rx r : ℝ) (q : ℕ),
      0 < rx → 0 < r → 1 ≤ q → (∀ j (_u : ι j), P.length j ≤ rx) → P.width ≤ r →
      (∀ j u, |P.centerX j u-baseX| ≤ rx) →
      (∀ j u, |P.centerZ j u-baseZ| ≤ r) →
      (∀ i y j u k x, ‖raw i j u k y x‖ ≤ P.constant*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*q) x *
          lineEnvelope (P.centerZ j u) P.width (2+2*q) y)) →
      (∀ i y j u k x, ‖deriv (raw i j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*q) x *
          lineEnvelope (P.centerZ j u) P.width (2+2*q) y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (raw i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (raw i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => raw 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*raw 0 j u k y x) = raw 1 j u k y x) →
      (∀ i j u k, Continuous (fun z : ℝ × ℝ => raw i j u k z.1 z.2)) →
      (∀ j u k x y, DifferentiableAt ℝ (fun t => raw 0 j u k t x) y) →
      ∀ n : ℕ, 1 ≤ n →
      let C := topPairConstant P.constant q
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) 2
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ (1/4:ℝ≥0∞)^n*
          (2*ENNReal.ofReal rx*ENNReal.ofReal (2*r))*ENNReal.ofReal ((4*Real.pi)^2) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w, |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (P.mainCoefficient d v g)
            (fun j u k y x => raw 0 j u k y x) a b x (z+w)‖ ≤
              P.coefficientScale*(256^q*(24*K*(n:ℝ))*
                boxVariationWeight (packetBoxIndex baseX baseZ rx r x z)^(q-1)) := by
  obtain ⟨Ab,Am,hAb,hAm,hglobal⟩ := analyzed_global_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hd hPderiv hPlow hPhigh raw frequency baseX baseZ rx r q
    hrx hr hq hwidth hW hx hz hbound hdbound hlow hhigh hcov hcont hdiff n hn
  let synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ :=
    fun i j u k y => topWeightedPair (fun e => raw e j u k y) baseX rx baseZ r y q i
  have hlen (j : Fin N) (u : ι j) : P.length j ≤ rx := hwidth j u
  have hslow i y j u k ξ hξ : 𝓕 (synth i j u k y) ξ = 0 :=
    topWeightedPair_low (fun e => raw e j u k y) baseX rx baseZ r y q
      (lo*2^j.val) (hi*2^j.val) (fun e => hlow e y j u k) (fun e => hhigh e y j u k) i ξ hξ
  have hshigh i y j u k ξ hξ : 𝓕 (synth i j u k y) ξ = 0 :=
    topWeightedPair_high (fun e => raw e j u k y) baseX rx baseZ r y q
      (lo*2^j.val) (hi*2^j.val) (fun e => hlow e y j u k) (fun e => hhigh e y j u k) i ξ hξ
  have hscov y j u k x : (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
      (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x := by
    simpa [synth, topWeightedPair] using
      topWeightedWave_covariant (raw 0 j u k) (raw 1 j u k)
        baseX rx baseZ r y (frequency k) x q (hdiff j u k x y) (hcov y j u k x)
  have hscont j u k : Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2) := by
    simpa only [synth, topWeightedPair, ↓reduceIte] using
      topWeightedWave_jointContinuous (raw 0 j u k) baseX rx baseZ r q (hcont 0 j u k)
  have hsdiff j u k x y : DifferentiableAt ℝ (fun t => synth 0 j u k t x) y := by
    simpa only [synth, topWeightedPair, ↓reduceIte] using
      topWeightedWave_vertical_differentiable (raw 0 j u k) baseX rx baseZ r x y q (hdiff j u k x y)
  have hsD j u k : Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => synth 0 j u k t z.2) z.1 -
        (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2) := by
    simpa only [synth, topWeightedPair, ↓reduceIte] using
      topWeightedWave_covariant_continuous (raw 0 j u k) (raw 1 j u k)
        baseX rx baseZ r (frequency k) q hr (hcont 0 j u k) (hcont 1 j u k)
          (hdiff j u k) (fun x y => hcov y j u k x)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hglobal N κ ι P d v hv g hg hg1 hPderiv hd hPlow hPhigh
    synth frequency (topPairConstant P.constant q) r (topPairConstant_pos _ _ P.constant_pos) hr
    (fun i y j u k x => topWeightedPair_bound (fun e => raw e j u k y)
      baseX rx baseZ r y (P.centerX j u) (P.length j) (P.centerZ j u) P.width P.constant q 3 2
      (P.length_pos j) hrx P.width_pos hr (hlen j u) hW (hx j u) (hz j u) P.constant_pos.le
      (fun e => hbound e y j u k) i x)
    (fun i y j u k x => topWeightedPair_derivative_bound (fun e => raw e j u k y)
      baseX rx baseZ r y (P.centerX j u) (P.length j) (P.centerZ j u) P.width P.constant q 3 2
      (P.length_pos j) hrx P.width_pos hr (hlen j u) hW (hx j u) (hz j u) P.constant_pos.le
      (fun e => hbound e y j u k) (fun e => hdbound e y j u k) i x)
    hslow hshigh hscov hscont hsdiff hsD
    (fun j u k y x => raw 0 j u k y x) baseX baseZ rx q hrx hq hwidth
    (by
      intro j u k y x
      simp only [synth, topWeightedPair, ↓reduceIte, topWeightedWave_apply])
    2 (by decide) n hn
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb x z w hw hout
  exact planarPacketInterval_denormalize_bound (P.mainCoefficient d v g)
    (fun j u k y x => raw 0 j u k y x) P.coefficientScale _
    P.coefficientScale_pos a b x (z+w) (hpoint a b hab hb x z w hw hout)

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PlanarPacketFamily

theorem constructed_analyzed_top_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (cutoff : Fin N → ℝ) (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone cutoff →
      (∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x*
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ j u k y xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) xi = 0) →
      (∀ j u k y xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.wave j u k y) xi = 0) →
      ∀ (raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (T : SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      (∀ j (_u : ι j), P.length j ≤ K*T.length) → P.width ≤ K*T.width →
      (∀ j u, |P.centerX j u-T.x| ≤ K*T.length) →
      (∀ j u, |P.centerZ j u-(T.y-T.slope*T.x)| ≤ K*T.width) →
      (∀ i y j u k x, ‖raw i j u k y x‖ ≤ P.constant*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x*
          lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)) →
      (∀ i y j u k x, ‖deriv (raw i j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) (3+2*(8*D+1)) x*
          lineEnvelope (P.centerZ j u) P.width (2+2*(8*D+1)) y)) →
      (∀ i y j u k xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (raw i j u k y) xi = 0) →
      (∀ i y j u k xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (raw i j u k y) xi = 0) →
      (∀ y j u k x, (4*(K*T.width):ℂ)*
        (deriv (fun yy => raw 0 j u k yy x) y-
          (frequency k:ℂ)*Complex.I*raw 0 j u k y x) = raw 1 j u k y x) →
      (∀ i j u k, Continuous (fun z : ℝ×ℝ => raw i j u k z.1 z.2)) →
      (∀ j u k x y, DifferentiableAt ℝ (fun yy => raw 0 j u k yy x) y) →
      ∀ J L : ℝ,
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z w, |w| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval (P.mainCoefficient cutoff v g)
            (fun j u k y x => raw 0 j u k y x) a b z.1 ((z.2-T.slope*z.1)+w)‖ ≤
              (P.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,hglobal⟩ := constructed_synthesis_global_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P cutoff v hv g hg hg1 hd hPderiv hPlow hPhigh raw frequency
    T K D hK hlength hwidth hcenterX hcenterZ hbound hderiv hlow hhigh hcov hcont hdiff J L
  let I := {ab : ℕ×ℕ // ab.1 ≤ ab.2 ∧ ab.2 ≤ N}
  let F : I → ℝ → ℝ → EuclideanSpace ℂ κ := fun ab x y =>
    planarPacketInterval (P.mainCoefficient cutoff v g)
      (fun j u k yy xx => raw 0 j u k yy xx) ab.val.1 ab.val.2 x y
  obtain ⟨bad,hbad,harea,hpoint⟩ := slope_top_neighborhood T K
    (P.topPacketAmplitude Ab Am D) J L D hK (P.topPacketAmplitude_pos Ab Am D).le F (by
      intro n hn
      obtain ⟨bad,hbad,harea,hpoint⟩ := hglobal N κ ι P cutoff v hv g hg hg1 hd
        hPderiv hPlow hPhigh raw frequency T.x (T.y-T.slope*T.x)
        (K*T.length) (K*T.width) (8*D+1)
        (mul_pos hK T.length_pos) (mul_pos hK T.width_pos) (by omega)
        hlength hwidth hcenterX hcenterZ hbound hderiv hlow hhigh
        (fun y j u k x => by simpa only [Complex.ofReal_mul] using hcov y j u k x)
        hcont hdiff n hn
      refine ⟨bad,hbad,harea,?_⟩
      intro ab x y w hw hout
      have hp := hpoint ab.val.1 ab.val.2 ab.property.1 ab.property.2 x y w hw hout
      simp only [Nat.add_sub_cancel] at hp
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [F,topPacketAmplitude]
      ring)
  refine ⟨bad,hbad,harea,?_⟩
  intro a b hab hb z w hw hout
  exact hpoint (⟨(a,b),hab,hb⟩ : I) z w hw hout

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem frozen_jet_top_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone d →
      (∀ j u k y xi, |xi| < (lo/P.topLength)*(2:ℝ)^j.val →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      (∀ j u k y xi, (hi/P.topLength)*(2:ℝ)^j.val < |xi| →
        𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0) →
      ∀ (T : SlopeBox) (K : ℝ) (D : ℕ), 0 < K →
      ∀ data : SupportedTopRawPacketData (P.withProfile alt hAlt).family
          (lo/P.topLength) (hi/P.topLength) T K D,
        SupportedTopCovariantData data → ∀ (i : Fin 2) (J L : ℝ),
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z w, |w| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval ((P.frozenProfile c hc).family.mainCoefficient d v g)
            (fun j u k y x => data.raw i j u k y x) a b z.1 ((z.2-T.slope*z.1)+w)‖ ≤
              (P.family.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  obtain ⟨Ab,Am,hAb,hAm,htop⟩ :=
    PlanarPacketFamily.constructed_analyzed_top_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd hAlow hAhigh T K D hK data second i J L
  let A := (P.frozenProfile c hc).referencePlanarFamily
  let U := T.horizontalRescale P.topLength P.topLength_pos
  let R := data.horizontalRescale P.topLength P.topLength_pos
  let R2 := second.horizontalRescale P.topLength P.topLength_pos
  let Q := (P.withProfile alt hAlt).family.horizontalRescale P.topLength P.topLength_pos
  have hconstant : Q.constant = A.constant := rfl
  have hlength (j : Fin N) : Q.length j = A.length j := rfl
  have hwidth : Q.width = A.width := rfl
  have hcenterX (j : Fin N) (u : ι j) : Q.centerX j u = A.centerX j u := rfl
  have hcenterZ (j : Fin N) (u : ι j) : Q.centerZ j u = A.centerZ j u := rfl
  have hfrequency : R.frequency = data.frequency := rfl
  have hboundR (e : Fin 2) (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖R.raw e j u k y x‖ ≤ A.constant*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R.bound e y j u k x
    change ‖R.raw e j u k y x‖ ≤ Q.constant*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  have hboundR2 (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖R2.second j u k y x‖ ≤ A.constant*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R2.bound y j u k x
    change ‖R2.second j u k y x‖ ≤ Q.constant*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  have hderivR (e : Fin 2) (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖deriv (R.raw e j u k y) x‖ ≤ (A.constant/A.length j)*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R.derivative_bound e y j u k x
    change ‖deriv (R.raw e j u k y) x‖ ≤ (Q.constant/Q.length j)*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  have hderivR2 (y : ℝ) (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
      ‖deriv (R2.second j u k y) x‖ ≤ (A.constant/A.length j)*
        (lineEnvelope (A.centerX j u) (A.length j) (3+2*(8*D+1)) x*
          lineEnvelope (A.centerZ j u) A.width (2+2*(8*D+1)) y) := by
    have h := R2.derivative_bound y j u k x
    change ‖deriv (R2.second j u k y) x‖ ≤ (Q.constant/Q.length j)*
      (lineEnvelope (Q.centerX j u) (Q.length j) (3+2*(8*D+1)) x*
        lineEnvelope (Q.centerZ j u) Q.width (2+2*(8*D+1)) y) at h
    simpa only [hconstant,hlength,hwidth,hcenterX,hcenterZ] using h
  let raw : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ := fun e =>
    if i=0 then R.raw e else if e=0 then R.raw 1 else R2.second
  let v' := fun z : ℝ×ℝ => v (z.1,P.topLength*z.2)
  let g' := fun z : ℝ×ℝ => g (z.1,P.topLength*z.2)
  have hv' : Measurable v' := hv.comp
    (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hg' : Measurable g' := hg.comp
    (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  obtain ⟨hAlow',hAhigh'⟩ := (P.frozenProfile c hc).referencePlanarFamily_cutoffs hAlow hAhigh
  obtain ⟨B,hB,harea,hpoint⟩ := htop N κ ι A d v' hv' g' hg' (fun _ => hg1 _) hd
    (fun y j u k x => (P.frozenProfile c hc).referencePlanarFamily_derivative j u k y x)
    hAlow' hAhigh' raw data.frequency U K D hK
    R.length_le R.width_le R.centerX_le R.centerZ_le
    (by
      intro e y j u k x
      fin_cases i <;> fin_cases e
      · simpa [raw] using hboundR 0 y j u k x
      · simpa [raw] using hboundR 1 y j u k x
      · simpa [raw] using hboundR 1 y j u k x
      · simpa [raw] using hboundR2 y j u k x)
    (by
      intro e y j u k x
      fin_cases i <;> fin_cases e
      · simpa [raw] using hderivR 0 y j u k x
      · simpa [raw] using hderivR 1 y j u k x
      · simpa [raw] using hderivR 1 y j u k x
      · simpa [raw] using hderivR2 y j u k x)
    (by
      intro e y j u k xi hxi
      fin_cases i <;> fin_cases e
      · simpa [raw] using R.low 0 y j u k xi hxi
      · simpa [raw] using R.low 1 y j u k xi hxi
      · simpa [raw] using R.low 1 y j u k xi hxi
      · simpa [raw] using R2.low y j u k xi hxi)
    (by
      intro e y j u k xi hxi
      fin_cases i <;> fin_cases e
      · simpa [raw] using R.high 0 y j u k xi hxi
      · simpa [raw] using R.high 1 y j u k xi hxi
      · simpa [raw] using R.high 1 y j u k xi hxi
      · simpa [raw] using R2.high y j u k xi hxi)
    (by
      intro y j u k x
      fin_cases i
      · simpa [raw,hfrequency] using R.covariant y j u k x
      · have h := R2.covariant y j u k x
        change (4*(K*U.width):ℂ)*(deriv (fun yy => R.raw 1 j u k yy x) y-
          (R.frequency k:ℂ)*Complex.I*R.raw 1 j u k y x) = R2.second j u k y x at h
        rw [hfrequency] at h
        simpa [raw] using h)
    (by
      intro e j u k
      fin_cases i <;> fin_cases e
      · simpa [raw] using R.continuous 0 j u k
      · simpa [raw] using R.continuous 1 j u k
      · simpa [raw] using R.continuous 1 j u k
      · simpa [raw] using R2.continuous j u k)
    (by
      intro j u k x y
      fin_cases i
      · simpa [raw] using R.differentiable j u k x y
      · simpa [raw] using R2.differentiable j u k x y) J L
  let bad := horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne') ⁻¹' B
  have hbad : MeasurableSet bad := hB.preimage
    (horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne')).measurable
  refine ⟨bad,hbad,?_,?_⟩
  · change (volume.prod volume)
      (horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne') ⁻¹' B) ≤ _
    rw [measure_horizontalDilation_preimage _ _ _ hB,inv_inv,abs_of_pos P.topLength_pos]
    apply (mul_le_mul_right harea (ENNReal.ofReal P.topLength)).trans
    rw [← ENNReal.ofReal_mul P.topLength_pos.le]
    apply ENNReal.ofReal_le_ofReal
    change P.topLength*(Real.exp (-J*L)*(T.length/P.topLength*T.width)) ≤ _
    apply le_of_eq
    field_simp [P.topLength_pos.ne']
    rfl
  · intro a b hab hb z w hw hout
    have hout' : (z.1/P.topLength,z.2) ∉ B := by
      intro hz
      apply hout
      change (horizontalDilation (P.topLength⁻¹) (inv_ne_zero P.topLength_pos.ne') z) ∈ B
      simpa only [horizontalDilation_apply,div_eq_mul_inv,mul_comm] using hz
    have hp := hpoint a b hab hb (z.1/P.topLength,z.2) w hw hout'
    have hraw (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
        raw 0 j u k y x = data.raw i j u k y (P.topLength*x) := by
      fin_cases i <;> rfl
    have hcoeff (j : Fin N) (u : ι j) :
        A.mainCoefficient d v' g' j u = (P.frozenProfile c hc).family.mainCoefficient d v g j u := by
      exact (P.frozenProfile c hc).family.horizontalRescale_mainCoefficient
        P.topLength P.topLength_pos d v g j u
    have hinterval (y : ℝ) : planarPacketInterval (A.mainCoefficient d v' g')
        (fun j u k yy xx => raw 0 j u k yy xx) a b (z.1/P.topLength) y =
        planarPacketInterval ((P.frozenProfile c hc).family.mainCoefficient d v g)
          (fun j u k yy xx => data.raw i j u k yy xx) a b z.1 y := by
      ext k
      simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,scalarBandPartial,
        planarPacketBand,hcoeff,hraw,mul_div_cancel₀ _ P.topLength_pos.ne']
    have hslope : U.slope*(z.1/P.topLength) = T.slope*z.1 := by
      change (P.topLength*T.slope)*(z.1/P.topLength) = _
      field_simp [P.topLength_pos.ne']
    have hweight : U.weight K (D:ℝ) (z.1/P.topLength,z.2) = T.weight K (D:ℝ) z := by
      rw [SlopeBox.horizontalRescale_weight]
      rw [mul_div_cancel₀ _ P.topLength_pos.ne']
    have hamp : A.topPacketAmplitude Ab Am D = P.family.topPacketAmplitude Ab Am D := rfl
    dsimp only at hp ⊢
    simpa only [hslope,hweight,hinterval,hamp] using hp

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

theorem source_frozen_spectral_jet_neighborhood_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : SourceLatticePacket N κ ι)
      (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)
      (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
      (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ), Measurable v →
      ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      Monotone d → ∀ (T : SlopeBox) (K w : ℝ) (D : ℕ), 0 < K → 0 < w →
      (∀ j u k xi eta, planarAngularFourier (P.physicalPacket T.slope j u k) (xi,eta) ≠ 0 →
        |xi+(T.slope+P.rowSlope j)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket T.slope j u k)
            (xi,eta) ≠ 0 →
        |xi+(T.slope+P.rowSlope j)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j (_u : ι j), cb*w/P.length j ≤ |P.rowSlope j| ∧
        |P.rowSlope j| ≤ Cb*w/P.length j) →
      SourceSupportedLatticeTopGeometry P T K D → ∀ (i : Fin 2) (J L : ℝ),
      let n := topExceptionMoment (topAreaPrefactor K) J L
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*T.area) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ z shift, |shift| ≤ K*T.width → z ∉ bad →
          ‖planarPacketInterval ((P.frozenProfile c hc).family.mainCoefficient d v g)
            (fun j u k y x => (P.withProfile alt hAlt).raw (i.castLE (by decide)) j u k y x)
            a b z.1 ((z.2-T.slope*z.1)+shift)‖ ≤
              (P.family.topPacketAmplitude Ab Am D*(n:ℝ)*5^(8*D))*(T.weight K (D:ℝ) z)^8 := by
  let lo := (cEta*cb-cStar)/(2*Real.pi)
  let hi := (CEta*Cb+cStar)/(2*Real.pi)
  have hlo : 0 < lo := div_pos (sub_pos.mpr hgap) (by positivity)
  have hhi : 0 ≤ hi := div_nonneg (add_nonneg (mul_nonneg hCEta hCb) hcStar) (by positivity)
  obtain ⟨Ab,Am,hAb,hAm,hgood⟩ := frozen_jet_top_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P c hc alt hAlt d v hv g hg hg1 hd T K w D hK hw hspectrum haltSpectrum hselector G i J L
  let S : SourceLatticeSpectralData (P.withProfile alt hAlt) := {
    referenceSlope := T.slope
    w := w
    cStar := cStar
    cEta := cEta
    CEta := CEta
    cb := cb
    Cb := Cb
    w_pos := hw
    cEta_pos := hcEta
    cb_nonneg := hcb
    Cb_nonneg := hCb
    spectrum := haltSpectrum
    selector := hselector }
  have hlow j u k y xi hxi : 𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0 :=
    (P.frozenProfile_fourier_cutoffs c hc T.slope w cStar cEta CEta cb Cb hw hcEta hcb hCb
      hspectrum (fun j u _ _ => hselector j u) 0 j u k y).1 xi hxi
  have hhigh j u k y xi hxi : 𝓕 ((P.frozenProfile c hc).raw 0 j u k y) xi = 0 :=
    (P.frozenProfile_fourier_cutoffs c hc T.slope w cStar cEta CEta cb Cb hw hcEta hcb hCb
      hspectrum (fun j u _ _ => hselector j u) 0 j u k y).2 xi hxi
  have Galt : SourceSupportedLatticeTopGeometry (P.withProfile alt hAlt) T K D := {
    length_le := G.length_le
    width_le := G.width_le
    centerX_le := G.centerX_le
    centerZ_le := G.centerZ_le
    order_le := G.order_le
    scale_eq := G.scale_eq }
  exact hgood N κ ι P c hc alt hAlt d v hv g hg hg1 hd hlow hhigh T K D hK
    ((P.withProfile alt hAlt).supportedTopRawData S T K D Galt)
    ((P.withProfile alt hAlt).supportedTopCovariantData S T K D Galt) i J L

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket

theorem source_frozen_jet_family_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb)
    (J a p : ℝ) (D : ℕ) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ top, Fin (N top) → Type) [∀ top j, Fintype (ι top j)]
        (P : ∀ top, SourceLatticePacket (N top) κ (ι top)),
      (∀ top, (P top).constant ≤ L^p) →
      ∀ (c : ∀ top j, ι top j → κ → ℂ) (hc : ∀ top j u k, ‖c top j u k‖ ≤ 1)
        (alt : ∀ top j, ι top j → κ → SchwartzMap (ℝ×ℝ) ℂ)
        (hAlt : ∀ top j u k,
          planarProfileConstant (alt top j u k) (2*(P top).order) ≤ (P top).profileBound)
        (d : ∀ top, Fin (N top) → ℝ) (v : τ → ℝ×ℝ → ℝ),
      (∀ top, Measurable (v top)) →
      ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) → (∀ top, Monotone (d top)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ top j u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j (_u : ι top j), cb*w/(P top).length j ≤ |(P top).rowSlope j| ∧
        |(P top).rowSlope j| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceSupportedLatticeTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top (i : Fin 2) lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ L^a*(T top).width → z ∉ bad →
          ‖planarPacketInterval (((P top).frozenProfile (c top) (hc top)).family.mainCoefficient
              (d top) (v top) (g top))
            (fun j u k y x => ((P top).withProfile (alt top) (hAlt top)).raw
              (i.castLE (by decide)) j u k y x)
            lower upper z.1 ((z.2-(T top).slope*z.1)+shift)‖ ≤
              L^(2*p+2)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Ab,Am,hAb,hAm,hgood⟩ := source_frozen_spectral_jet_neighborhood_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  obtain ⟨Lt,hLt,hthreshold⟩ := exists_top_threshold
    Ab Am (J+1) a p D hAb hAm (by linarith) ha hp
  refine ⟨max 2 Lt,le_max_left _ _,?_⟩
  intro L hLL τ κ _ _ N ι _ P hP c hc alt hAlt d v hv g hg hg1 hd
    T w hw hspectrum haltSpectrum hselector G
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLL
  have hLtL : Lt ≤ L := (le_max_right _ _).trans hLL
  have hLpos : 0 < L := by linarith
  have hK : 0 < L^a := Real.rpow_pos_of_pos hLpos _
  choose bad hbad harea hpoint using fun top (i : Fin 2) =>
    hgood (N top) κ (ι top) (P top) (c top) (hc top) (alt top) (hAlt top)
      (d top) (v top) (hv top) (g top) (hg top) (hg1 top) (hd top) (T top)
      (L^a) w D hK hw (hspectrum top) (haltSpectrum top) (hselector top) (G top)
      i (J+1) L
  have hsum : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
  have hexp : 2*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
    have htwo : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc
      _ ≤ Real.exp L*Real.exp (-(J+1)*L) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨⋃ top, ⋃ i, bad top i,MeasurableSet.iUnion (fun top => MeasurableSet.iUnion (hbad top)),?_,?_⟩
  · calc
      _ ≤ ∑ top, ∑ i, (volume.prod volume) (bad top i) := by
        apply (measure_iUnion_le _).trans
        simp only [tsum_fintype]
        exact Finset.sum_le_sum fun top _ => by simpa only [tsum_fintype] using measure_iUnion_le (bad top)
      _ ≤ ∑ top, ∑ _i : Fin 2, ENNReal.ofReal (Real.exp (-(J+1)*L)*(T top).area) :=
        Finset.sum_le_sum fun top _ => Finset.sum_le_sum fun i _ => harea top i
      _ = ENNReal.ofReal ((2*Real.exp (-(J+1)*L))*(∑ top, (T top).area)) := by
        simp only [Fin.sum_univ_two]
        have hnonneg (top : τ) : 0 ≤ Real.exp (-(J+1)*L)*(T top).area :=
          mul_nonneg (Real.exp_pos _).le (T top).area_pos.le
        simp_rw [← ENNReal.ofReal_add (hnonneg _) (hnonneg _)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun top _ => add_nonneg (hnonneg top) (hnonneg top))]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hexp hsum)
  · intro top i lower upper hlu hu z shift hshift hout
    have hout' : z ∉ bad top i := fun h => hout (mem_iUnion.mpr ⟨top,mem_iUnion.mpr ⟨i,h⟩⟩)
    exact (hpoint top i lower upper hlu hu z shift hshift hout').trans
      (mul_le_mul_of_nonneg_right
        (hthreshold L hLtL (N top) κ (ι top) (P top).family (hP top)) (by positivity))

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationCentered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem source_frozen_centered_family_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb)
    (J a p : ℝ) (D : ℕ) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 3 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ top, Fin (N top) → Type) [∀ top j, Fintype (ι top j)]
        (P : ∀ top, SourceLatticePacket (N top) κ (ι top)),
      (∀ top, (P top).constant ≤ L^p) →
      ∀ (c : ∀ top j, ι top j → κ → ℂ) (hc : ∀ top j u k, ‖c top j u k‖ ≤ 1)
        (alt : ∀ top j, ι top j → κ → SchwartzMap (ℝ×ℝ) ℂ)
        (hAlt : ∀ top j u k,
          planarProfileConstant (alt top j u k) (2*(P top).order) ≤ (P top).profileBound)
        (d : ∀ top, Fin (N top) → ℝ), (∀ top j, 0 ≤ d top j) →
      ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
      ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) → (∀ top, Monotone (d top)) →
      ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ top j u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j (_u : ι top j), cb*w/(P top).length j ≤ |(P top).rowSlope j| ∧
        |(P top).rowSlope j| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceSupportedLatticeTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
            (((P top).frozenProfile (c top) (hc top)).physicalCenteredCoefficient
              (T top).slope (T top).slope (d top) (v top) (g top)) 0 lower upper x y
          ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+
            (T top).width*‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Lt,_hLt,hgood⟩ := source_frozen_jet_family_concentration_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap (J+1) a p D (by linarith) ha hp
  refine ⟨max 3 Lt,le_max_left _ _,?_⟩
  intro L hLL τ κ _ _ N ι _ P hP c hc alt hAlt d hd v hv g hg hg1 hmono
    T w hw hspectrum haltSpectrum hselector G
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hLL
  have hLpos : 0 < L := by linarith
  have hK : 1 ≤ L^a := Real.one_le_rpow (by linarith) ha
  let cutoff := fun q : τ×Fin 3 => centeredPhaseCutoff_p1 (T q.1).slope (d q.1) q.2
  let field := fun q : τ×Fin 3 => centeredPhaseField_p1 (T q.1).slope (v q.1) q.2
  let test := fun q : τ×Fin 3 => fun z => g q.1 (sourceReferenceToPhysical (T q.1).slope z)
  have hfield q : Measurable (field q) := by
    rcases q with ⟨top,phase⟩
    fin_cases phase
    · exact (hv top).comp (sourceReferenceToPhysical (T top).slope).measurable
    · exact ((hv top).comp (sourceReferenceToPhysical (T top).slope).measurable).neg
    · exact measurable_const
  have htest q : Measurable (test q) :=
    (hg q.1).comp (sourceReferenceToPhysical (T q.1).slope).measurable
  have hcut q : Monotone (cutoff q) := by
    rcases q with ⟨top,phase⟩
    fin_cases phase
    · exact centered_upper_monotone (T top).slope (hmono top)
    · exact centered_lower_monotone (T top).slope (hmono top)
    · exact fun _ _ _ => le_rfl
  obtain ⟨bad,hbad,harea,hpoint⟩ := hgood L ((le_max_right _ _).trans hLL)
    (τ×Fin 3) κ (fun q => N q.1) (fun q => ι q.1) (fun q => P q.1) (fun q => hP q.1)
    (fun q => c q.1) (fun q => hc q.1) (fun q => alt q.1) (fun q => hAlt q.1)
    cutoff field hfield test htest (fun q z => hg1 q.1 _) hcut
    (fun q => T q.1) w hw (fun q => hspectrum q.1) (fun q => haltSpectrum q.1)
    (fun q => hselector q.1) (fun q => G q.1)
  refine ⟨bad,hbad,?_,?_⟩
  · have hexp : 3*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
      have hthree : 3 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
      calc
        _ ≤ Real.exp L*Real.exp (-(J+1)*L) :=
          mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hsum : (∑ q : τ×Fin 3, (T q.1).area) = 3*(∑ top, (T top).area) := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_three]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum] at harea
    exact harea.trans (ENNReal.ofReal_le_ofReal (by
      have hS : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
      nlinarith [mul_le_mul_of_nonneg_right hexp hS]))
  · intro top lower upper hlu hu z shift hshift hout
    let Q := (P top).withProfile (alt top) (hAlt top)
    let coeff := ((P top).frozenProfile (c top) (hc top)).physicalCenteredCoefficient
      (T top).slope (T top).slope (d top) (v top) (g top)
    let y := z.2-(T top).slope*z.1+shift
    let bound := L^(2*p+2)*((T top).weight (L^a) (D:ℝ) z)^8
    have hshift' : |shift| ≤ L^a*(T top).width :=
      hshift.trans (le_mul_of_one_le_left (T top).width_pos.le hK)
    have hphase (phase : Fin 3) (i : Fin 2) :
        ‖Q.rawInterval
          (((P top).frozenProfile (c top) (hc top)).physicalCoefficient (T top).slope
            (cutoff (top,phase))
            (if phase=0 then v top else if phase=1 then fun z => -v top z else fun _ => 0)
            (g top)) (i.castLE (by decide)) lower upper z.1 y‖ ≤ bound := by
      rw [(P top).frozen_physical_rawInterval_eq_reference (c top) (hc top) (alt top) (hAlt top)]
      have h := hpoint (top,phase) i lower upper hlu hu z shift hshift' hout
      fin_cases phase <;> simpa [Q,rawInterval,cutoff,field,test,centeredPhaseCutoff_p1,centeredPhaseField_p1,y,bound] using h
    have hjet (i : Fin 2) : ‖Q.rawInterval coeff (i.castLE (by decide)) lower upper z.1 y‖ ≤ 3*bound := by
      rw [(P top).frozen_centered_rawInterval_eq (c top) (hc top) (alt top) (hAlt top)
        (T top).slope (d top) (hd top) (v top) (hv top) (g top) (hg top) (hg1 top)]
      apply (norm_sub_le _ _).trans
      apply (add_le_add (norm_add_le _ _) le_rfl).trans
      have h0 := hphase 0 i
      have h1 := hphase 1 i
      have h2 := hphase 2 i
      simp [cutoff,centeredPhaseCutoff_p1] at h0 h1 h2
      linarith
    have hcov := Q.rawInterval_scaled_covariant coeff lower upper z.1 y
    have hcovnorm := congrArg norm hcov
    rw [norm_smul,Real.norm_eq_abs] at hcovnorm
    have hscale : (T top).width ≤ |Q.scale| := by
      change (T top).width ≤ |(P top).scale|
      rw [(G top).scale_eq,abs_of_pos (mul_pos (by norm_num : (0:ℝ) < 4)
        (mul_pos (Real.rpow_pos_of_pos hLpos a) (T top).width_pos))]
      nlinarith [(T top).width_pos]
    have hderiv : (T top).width*‖covariantSignal (P top).frequency
        (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ ≤ 3*bound := by
      calc
        _ ≤ |Q.scale| * ‖covariantSignal Q.frequency
          (fun k yy => Q.rawInterval coeff 0 lower upper z.1 yy k) y‖ :=
          mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
        _ = ‖Q.rawInterval coeff 1 lower upper z.1 y‖ := hcovnorm
        _ ≤ _ := hjet 1
    have hpoly : 6*bound ≤ L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 := by
      have hp2 : 6 ≤ L^2 := by nlinarith
      have hbnonneg : 0 ≤ bound := by dsimp [bound]; positivity
      calc
        _ ≤ L^2*bound := mul_le_mul_of_nonneg_right hp2 hbnonneg
        _ = _ := by
          dsimp [bound]
          rw [← mul_assoc,← Real.rpow_natCast L 2,← Real.rpow_add hLpos]
          congr 2
          ring
    exact (add_le_add (hjet 0) hderiv).trans (by linarith)

end LipschitzHilbert.SourceLatticePacket

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationMainSlots
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem source_labeled_centered_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hgap : cStar < cEta*cb)
    (J a p : ℝ) (D B : ℕ) (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 3 ≤ L0 ∧ (B:ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top))
      (_hcard : ∀ top j, ((P top).labels j).card ≤ B),
      (∀ top, (P top).constant ≤ L^p) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ)
      (_hb : ∀ top j l k, ‖b top j l k (0:ℝ)‖ ≤ 1),
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (angle : τ → ℝ), (∀ top, 0 ≤ angle top) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
    ∀ (T : τ → SlopeBox) (w : ℝ), 0 < w →
      (∀ top j l u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j (l : (P top).labels j) (_u : Item top j l),
        cb*w/(P top).length j ≤ |(P top).rowSlope j l| ∧
          |(P top).rowSlope j l| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let F := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
            ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
              (fun j l k _ => b top j l k 0) (v top) (g top)) 0 lower upper x y
          ‖F z.1 (z.2-(T top).slope*z.1+shift)‖+
            (T top).width*‖covariantSignal (P top).frequency (fun k y => F z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+5)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Lt,hLt,hconc⟩ := SourceLatticePacket.source_frozen_centered_family_concentration_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap (J+1) a p D (by linarith) ha hp
  refine ⟨max Lt B,hLt.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro L hLL τ κ _ _ N Label Item _ P hcard hP b hb alt hAlt angle hangle
    v hv g hg hg1 T w hw hspectrum haltSpectrum hselector G
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hLL)
  have hBL : (B:ℝ) ≤ L := (le_max_right _ _).trans hLL
  let Item' := fun q : τ×Fin B => (P q.1).SlotItem (hcard q.1) q.2
  let P' := fun q : τ×Fin B => (P q.1).slotted (hcard q.1) q.2
  let alt' := fun q : τ×Fin B => (P q.1).slottedAlt (hcard q.1) (alt q.1) q.2
  let hAlt' := fun q : τ×Fin B =>
    (P q.1).slottedAlt_bound (hcard q.1) (alt q.1) (hAlt q.1) q.2
  let c := fun (q : τ×Fin B) j (u : Item' q j) k => b q.1 j u.1.1 k 0
  have hspec (q : τ×Fin B) := (P q.1).slotted_spectrum (hcard q.1) (T q.1).slope w cStar cEta CEta
    (hspectrum q.1) q.2
  have haltSpec : ∀ q j u k xi eta,
      planarAngularFourier (((P' q).withProfile (alt' q) (hAlt' q)).physicalPacket
        (T q.1).slope j u k) (xi,eta) ≠ 0 →
      |xi+((T q.1).slope+(P' q).rowSlope j)*eta| ≤ cStar/(P' q).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro q j u k xi eta hn
    rw [(P q.1).slotted_alt_physicalPacket (hcard q.1) (alt q.1) (hAlt q.1)] at hn
    simpa only [P',slotted_length,(P q.1).slotted_rowSlope (hcard q.1) q.2 j u] using
      haltSpectrum q.1 j u.1.1 u.1.2 k xi eta hn
  obtain ⟨bad,hbad,harea,hpoint⟩ := hconc L ((le_max_left _ _).trans hLL)
    (τ×Fin B) κ (fun q => N q.1) Item' P'
    (fun q => by simpa only [P',slotted_constant] using hP q.1)
    c (fun q j u k => hb q.1 j u.1.1 k) alt' hAlt'
    (fun q j => angle q.1*(2:ℝ)^j.val)
    (fun q j => mul_nonneg (hangle q.1) (pow_nonneg (by norm_num) _))
    (fun q => v q.1) (fun q => hv q.1) (fun q => g q.1) (fun q => hg q.1)
    (fun q => hg1 q.1)
    (fun q i j hij => mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) (hangle q.1))
    (fun q => T q.1) w hw hspec haltSpec
    (fun q => (P q.1).slotted_selector (hcard q.1) w cb Cb (hselector q.1) q.2)
    (fun q => (P q.1).slotted_supportedTopGeometry (hcard q.1) (G q.1) q.2)
  refine ⟨bad,hbad,harea.trans (ENNReal.ofReal_le_ofReal ?_),?_⟩
  · have hsum : (∑ q : τ×Fin B, (T q.1).area) = (B:ℝ)*(∑ top, (T top).area) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← Finset.mul_sum]
    rw [hsum]
    have he : (B:ℝ) ≤ Real.exp L := hBL.trans (by linarith [Real.add_one_le_exp L])
    have hd : (B:ℝ)*Real.exp (-(J+1)*L) ≤ Real.exp (-J*L) := by
      calc
        _ ≤ Real.exp L*Real.exp (-(J+1)*L) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hs : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
    nlinarith [mul_le_mul_of_nonneg_right hd hs]
  · intro top lower upper hlu hu z shift hshift hout
    dsimp only
    let Q := (P top).withProfile (alt top) (hAlt top)
    let coeff := (P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
      (fun j l k _ => b top j l k 0) (v top) (g top)
    let y := z.2-(T top).slope*z.1+shift
    let F := fun s : Fin B => (Q.slotted (hcard top) s).rawInterval
      (fun j u => coeff j u.1.1 u.1.2) 0 lower upper z.1
    have hF (s : Fin B) (yy : ℝ) :
        ((P' (top,s)).withProfile (alt' (top,s)) (hAlt' (top,s))).rawInterval
          (((P' (top,s)).frozenProfile (c (top,s))
            (fun j u k => hb top j u.1.1 k)).physicalCenteredCoefficient
            (T top).slope (T top).slope (fun j => angle top*(2:ℝ)^j.val) (v top) (g top))
          0 lower upper z.1 yy = F s yy :=
      (P top).frozenSlot_rawInterval (hcard top) (T top).slope (angle top)
        (fun j l k _ => b top j l k 0) (fun j l k => hb top j l k)
        (alt top) (hAlt top) (v top) (g top) s 0 lower upper z.1 yy
    have hb' (s : Fin B) : ‖F s y‖+(T top).width*
        ‖covariantSignal (P top).frequency (fun k yy => F s yy k) y‖ ≤
        L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 := by
      have h := hpoint (top,s) lower upper hlu hu z shift hshift hout
      let A := fun yy => ((P' (top,s)).withProfile (alt' (top,s)) (hAlt' (top,s))).rawInterval
        (((P' (top,s)).frozenProfile (c (top,s))
          (fun j u k => hb top j u.1.1 k)).physicalCenteredCoefficient
          (T top).slope (T top).slope (fun j => angle top*(2:ℝ)^j.val) (v top) (g top))
        0 lower upper z.1 yy
      have hf : A = F s := funext (hF s)
      change ‖A y‖+(T top).width*‖covariantSignal (P top).frequency (fun k yy => A yy k) y‖ ≤ _ at h
      rw [hf] at h
      exact h
    have hscale : Q.scale ≠ 0 := by
      change (P top).scale ≠ 0
      rw [(G top).scale_eq]
      exact ne_of_gt (mul_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hLpos _) (T top).width_pos))
    have hs := Q.sum_slotted_rawInterval (hcard top) coeff 0 lower upper z.1 y
    have hd := Q.sum_slotted_covariant (hcard top) hscale coeff lower upper z.1 y
    have hn : ‖∑ s, F s y‖+(T top).width*
        ‖∑ s, covariantSignal (P top).frequency (fun k yy => F s yy k) y‖ ≤
        (B:ℝ)*(L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8) := by
      calc
        _ ≤ (∑ s, ‖F s y‖)+(T top).width*
            (∑ s, ‖covariantSignal (P top).frequency (fun k yy => F s yy k) y‖) :=
          add_le_add (norm_sum_le _ _) (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (T top).width_pos.le)
        _ = ∑ s, (‖F s y‖+(T top).width*
            ‖covariantSignal (P top).frequency (fun k yy => F s yy k) y‖) := by
          rw [Finset.sum_add_distrib,Finset.mul_sum]
        _ ≤ ∑ _s : Fin B, L^(2*p+4)*((T top).weight (L^a) (D:ℝ) z)^8 :=
          Finset.sum_le_sum fun s _ => hb' s
        _ = _ := by simp
    rw [hs,hd] at hn
    apply hn.trans
    have hpowers : L*L^(2*p+4) = L^(2*p+5) := by
      rw [show 2*p+5 = 1+(2*p+4) by ring,Real.rpow_add hLpos (1:ℝ) (2*p+4),Real.rpow_one]
    calc
      _ = ((B:ℝ)*L^(2*p+4))*((T top).weight (L^a) (D:ℝ) z)^8 := by ring
      _ ≤ (L*L^(2*p+4))*((T top).weight (L^a) (D:ℝ) z)^8 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBL (Real.rpow_nonneg hLpos.le _)) (by positivity)
      _ = _ := by rw [hpowers]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentrationMain
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem source_selector_main_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb) (J a p : ℝ) (D B : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 3 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ)
      (T : τ → SlopeBox),
      (∀ top j l k, ‖b top j l k (T top).slope‖ ≤ 1) →
      (∀ top j, ((P top).frozenActiveLabels (T top).slope (b top) j).card ≤ B) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (angle : τ → ℝ), (∀ top, 0 ≤ angle top) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
    ∀ (w : ℝ), 0 < w →
      (∀ top k, |(P top).frequency k| ≤ F/w) →
      (∀ top j l u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, (∃ k, b top j l k (T top).slope ≠ 0) →
        cb*w/(P top).length j ≤ |(P top).rowSlope j l| ∧
          |(P top).rowSlope j l| ≤ Cb*w/(P top).length j) →
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^a) D) →
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let V := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
            ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
              (b top) (v top) (g top)) 0 lower upper x y
          ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+
            (T top).width*‖covariantSignal (P top).frequency (fun k y => V z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+7)*((T top).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨Lt,hLt,_hBt,hconc⟩ := source_labeled_centered_concentration_of_supported hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap J a (p+1) D B
    hJ ha (by linarith)
  refine ⟨max Lt (F*Cb+2),hLt.trans (le_max_left _ _),?_⟩
  intro L hLL τ κ _ _ N Label Item _ P hP b T hb hcard alt hAlt angle hangle
    v hv g hg hg1 w hw hfreq hspectrum haltSpectrum hselector G
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hLL)
  have hCL : F*Cb+2 ≤ L := (le_max_right _ _).trans hLL
  let Q := fun top => (P top).activeMainFamily (T top).slope (b top) w F Cb hw hF hCb
    (hfreq top) (fun j l hl => (hselector top j l hl).2)
  let orig := fun top j => (P top).frozenActiveOriginalLabel (T top).slope (b top) j
  let altQ := fun top j l => alt top j (orig top j l)
  let hAltQ := fun top j l => hAlt top j (orig top j l)
  let bQ := fun top j l k (_s : ℝ) => b top j (orig top j l) k (T top).slope
  have hQ (top : τ) : (Q top).constant ≤ L^(p+1) := by
    rw [(P top).activeMainFamily_constant]
    calc
      _ ≤ L^p*L := mul_le_mul (hP top) hCL (by positivity) (Real.rpow_nonneg hLpos.le _)
      _ = _ := by rw [Real.rpow_add hLpos p 1,Real.rpow_one]
  have hs : ∀ top j l u k xi eta,
      planarAngularFourier ((Q top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
      |xi+((T top).slope+(Q top).rowSlope j l)*eta| ≤ cStar/(Q top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro top j l u k xi eta hx
    exact hspectrum top j (orig top j l) u k xi eta hx
  have hsAlt : ∀ top j l u k xi eta,
      planarAngularFourier (((Q top).withProfile (altQ top) (hAltQ top)).physicalPacket
        (T top).slope j l u k) (xi,eta) ≠ 0 →
      |xi+((T top).slope+(Q top).rowSlope j l)*eta| ≤ cStar/(Q top).length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
    intro top j l u k xi eta hx
    exact haltSpectrum top j (orig top j l) u k xi eta hx
  have hsel : ∀ top j (l : (Q top).labels j) (_u : Item top j l),
      cb*w/(Q top).length j ≤ |(Q top).rowSlope j l| ∧
        |(Q top).rowSlope j l| ≤ Cb*w/(Q top).length j := by
    intro top j l _u
    exact hselector top j (orig top j l)
      ((P top).frozenActiveLabel_nonzero (T top).slope (b top) j l)
  obtain ⟨bad,hbad,harea,hpoint⟩ := hconc L ((le_max_left _ _).trans hLL)
    τ κ N Label Item Q hcard hQ bQ (fun top j l k => hb top j (orig top j l) k)
    altQ hAltQ angle hangle v hv g hg hg1 T w hw hs hsAlt hsel
    (fun top => (P top).activeMainFamily_supportedTopGeometry (T top).slope (b top) w F Cb hw hF hCb
      (hfreq top) (fun j l hl => (hselector top j l hl).2) (G top))
  refine ⟨bad,hbad,harea,?_⟩
  intro top lower upper hlu hu z shift hshift hout
  have h := hpoint top lower upper hlu hu z shift hshift hout
  let V := fun x y => ((Q top).withProfile (altQ top) (hAltQ top)).rawInterval
    ((Q top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
      (fun j l k _ => bQ top j l k 0) (v top) (g top)) 0 lower upper x y
  have heq (x y : ℝ) : V x y = ((P top).withProfile (alt top) (hAlt top)).rawInterval
      ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
        (b top) (v top) (g top)) 0 lower upper x y := by
    exact (P top).activeMainFamily_rawInterval (T top).slope (b top) w F Cb hw hF hCb
      (hfreq top) (fun j l hl => (hselector top j l hl).2)
      (alt top) (hAlt top) (angle top) (v top) (g top) 0 lower upper hlu x y
  have heqfun (x : ℝ) : V x = fun y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
      ((P top).physicalFrozenCenteredCoefficient (T top).slope (angle top)
        (b top) (v top) (g top)) 0 lower upper x y := funext (heq x)
  change ‖V z.1 _‖+(T top).width*‖covariantSignal (P top).frequency
    (fun k y => V z.1 y k) _‖ ≤ _ at h
  rw [heqfun] at h
  simpa only [show 2*(p+1)+5 = 2*p+7 by ring] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedConcentration
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selector concentration with packetwise length control.
Empty initial scales impose no global top-length assumption; constants are unchanged. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.SourceLabeledLattice

theorem eventually_source_selector_concentration_of_supported (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (rate aWeight p Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : τ → ℕ) (Label : ∀ top, Fin (N top) → Type)
      (Item : ∀ top j, Label top j → Type) [∀ top j l, Fintype (Item top j l)]
      (P : ∀ top, SourceLabeledLattice (N top) κ (Label top) (Item top)),
      (∀ top, (P top).absoluteConstant ≤ L^p) →
      (∀ top, 6+2*(8*D+1) ≤ (P top).order) →
    ∀ (alt : ∀ top j (l : (P top).labels j), Item top j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ top j l u k,
        planarProfileConstant (alt top j l u k) (2*(P top).order) ≤ (P top).profileBound)
      (T : τ → SlopeBox),
      (∀ top, SourceSupportedLabeledTopGeometry (P top) (T top) (L^aWeight) D) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => (T top).slope+(P top).rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ top j, (P top).labels j → κ → ℝ → ℂ),
      (∀ top j l k, Measurable (b top j l k)) →
      (∀ top j l k s, ‖b top j l k s‖ ≤ 1) →
      (∀ top j l k s, b top j l k s ≠ 0 →
        |s-((T top).slope+(P top).rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b top j l k s-b top j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b top j l k s = 0) →
    ∀ (v : τ → ℝ×ℝ → ℝ), (∀ top, Measurable (v top)) →
    ∀ (g : τ → ℝ×ℝ → EuclideanSpace ℂ κ), (∀ top, Measurable (g top)) →
      (∀ top z, ‖g top z‖ ≤ 1) →
    ∀ (w : ℝ), 0 < w → (∀ top k, |(P top).frequency k| ≤ F/w) →
      (∀ top j l u k xi eta,
        planarAngularFourier ((P top).physicalPacket (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l u k xi eta,
        planarAngularFourier (((P top).withProfile (alt top) (hAlt top)).physicalPacket
          (T top).slope j l u k) (xi,eta) ≠ 0 →
        |xi+((T top).slope+(P top).rowSlope j l)*eta| ≤ cStar/(P top).length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, (∃ k, b top j l k (T top).slope ≠ 0) →
        cb*w/(P top).length j ≤ |(P top).rowSlope j l| ∧
          |(P top).rowSlope j l| ≤ Cb*w/(P top).length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
    ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
      (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
      ∀ top lower upper, lower ≤ upper → upper ≤ N top → ∀ z shift,
        |shift| ≤ (T top).width → z ∉ bad →
        let V := fun x y => ((P top).withProfile (alt top) (hAlt top)).rawInterval
          ((P top).physicalMultiplierCoefficient (T top).slope (b top) (v top) (g top))
          0 lower upper x y
        ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
          ‖covariantSignal (P top).frequency (fun k y => V z.1 y k)
            (z.2-(T top).slope*z.1+shift)‖ ≤
              L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  obtain ⟨Lt,_hLt,hmain⟩ := source_selector_main_concentration_of_supported hL
    cStar cEta CEta cb Cb F hcStar hcEta hCEta hcb hCb hF hgap
    (rate+1) aWeight p D ((2*K+1)*H) (by linarith) haWeight hp
  filter_upwards [eventually_selector_error_family_concentration_of_supported
      (rate+1) aWeight p 1 Lip D K H J₀ (by linarith) haWeight hp (by norm_num) hLip,
    eventually_ge_atTop (max 3 Lt)] with L herror hlarge
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hlarge
  have hLpos : 0 < L := by linarith
  intro τ κ _ _ N Label Item _ P hP horder alt hAlt T G angle small wide radius E J
    hangle hsmall hsmall1 hwide hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv g hg hg1 w hw hfreq hspectrum haltSpectrum hselector hJ hE
  classical
  have hcard top j : ((P top).frozenActiveLabels (T top).slope (b top) j).card ≤ (2*K+1)*H :=
    (P top).frozenActiveLabels_card_local (T top).slope (b top) j
      (mul_pos (hangle top) (pow_pos (by norm_num) _)) (hlocal top j) hradius
      (fun l k hk => hsupport top j l k (T top).slope hk)
  obtain ⟨Bmain,hBmain,hAmain,hMpoint⟩ := hmain L ((le_max_right _ _).trans hlarge)
    τ κ N Label Item P hP b T (fun top j l k => hb1 top j l k _) hcard
    alt hAlt angle (fun top => (hangle top).le) v hv g hg hg1 w hw hfreq
    hspectrum haltSpectrum hselector G
  obtain ⟨Berror,hBerror,hAerror,hEpoint⟩ := herror τ κ N Label Item P hP horder
    alt hAlt T G angle small wide radius E J hangle hsmall hsmall1 hwide hwide1 hradius
    hlocal b hb hb1 hsupport hnear hfar v hv g hg hg1 hJ hE
  refine ⟨Bmain∪Berror,hBmain.union hBerror,?_,?_⟩
  · apply (measure_union_le _ _).trans
    apply (add_le_add hAmain hAerror).trans
    rw [← ENNReal.ofReal_add
      (mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun top _ => (T top).area_pos.le))
      (mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun top _ => (T top).area_pos.le))]
    apply ENNReal.ofReal_le_ofReal
    have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have hexp : 2*Real.exp (-(rate+1)*L) ≤ Real.exp (-rate*L) := by
      calc
        _ ≤ Real.exp L*Real.exp (-(rate+1)*L) := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hs : 0 ≤ ∑ top, (T top).area := Finset.sum_nonneg fun top _ => (T top).area_pos.le
    nlinarith [mul_le_mul_of_nonneg_right hexp hs]
  · intro top lower upper hlu hu z shift hshift hout
    dsimp only
    have hm := hMpoint top lower upper hlu hu z shift hshift
      (fun h => hout (Or.inl h))
    have he := hEpoint top lower upper z shift hshift (fun h => hout (Or.inr h))
    have hscale : (P top).scale ≠ 0 := by
      rw [(G top).scale_eq]
      exact ne_of_gt (mul_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hLpos _) (T top).width_pos))
    have hj := (P top).selector_jointInterval_le (alt top) (hAlt top)
      (T top).slope (angle top) (b top) (hb top) (hb1 top) (v top) (hv top)
      (g top) (hg top) (hg1 top) hscale lower upper hlu (T top).width (T top).width_pos.le
      z.1 (z.2-(T top).slope*z.1+shift)
    apply hj.trans
    apply (add_le_add hm he).trans
    have hpowers : 2*L^(2*p+7) ≤ L^(2*p+8) := by
      calc
        _ ≤ L*L^(2*p+7) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hLpos.le _)
        _ = _ := by
          rw [show 2*p+8 = 1+(2*p+7) by ring,Real.rpow_add hLpos (1:ℝ) (2*p+7),Real.rpow_one]
    have hwpos := pow_nonneg ((T top).weight_pos
      (Real.rpow_pos_of_pos hLpos aWeight) (D:ℝ) z).le 8
    nlinarith [mul_le_mul_of_nonneg_right hpowers hwpos]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSupportedAssignedConcentration
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original-selector concentration for the assigned top families,
recentered at their own slopes. All source bounds concern the original
labels and selected packets. Neither restriction introduces multiplicity
or changes the analyzing coefficient. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_top_selector_concentration_of_supported_oai (hL : LepingleInput)
    (cStar cEta CEta cb Cb F : ℝ) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hF : 0 ≤ F)
    (hgap : cStar < cEta*cb)
    (rate aWeight p Lip : ℝ) (D K H J₀ : ℕ)
    (hrate : 0 ≤ rate) (haWeight : 0 ≤ aWeight) (hp : 0 ≤ p) (hLip : 0 ≤ Lip) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      P.referenceEnvelopeConstant ≤ L^p → 6+2*(8*D+1) ≤ P.order →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k,
        planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ top, P.width ≤ L^aWeight*(T top).width) →
      (∀ top, P.scale = 4*(L^aWeight*(T top).width)) →
      (∀ q ∈ packets,
        |P.actualX q.1 q.2.1 q.2.2-(T (assigned q)).x|+P.length q.1 ≤
          L^aWeight*(T (assigned q)).length) →
      (∀ q ∈ packets,
        |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(T (assigned q)).slope)*
          P.actualX q.1 q.2.1 q.2.2-
          ((T (assigned q)).y-(T (assigned q)).slope*(T (assigned q)).x)|+P.width ≤
            L^aWeight*(T (assigned q)).width) →
    ∀ (angle : τ → ℝ) (small wide radius : ℝ) (E J : ℕ),
      (∀ top, 0 < angle top) → 0 < small → small ≤ 1 →
      wide ≤ small*(2:ℝ)^J → 1 ≤ wide*((2:ℝ)^E)^4 → radius ≤ K →
      (∀ top j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l => oldSlope+P.rowSlope j l) (angle top*(2:ℝ)^j.val) H) →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) →
      (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ radius*(angle top*(2:ℝ)^j.val)) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        |s-(T top).slope| ≤ small*(angle top*(2:ℝ)^j.val) →
        ‖b j l k s-b j l k (T top).slope‖ ≤
          Lip*(|s-(T top).slope|/(angle top*(2:ℝ)^j.val))) →
      (∀ top j l k s, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (wide*((2:ℝ)^E)^4)*(angle top*(2:ℝ)^j.val) < |s-(T top).slope| →
        b j l k s = 0) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f →
      (∀ z, ‖f z‖ ≤ 1) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ q ∈ packets, ∀ k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket
          oldSlope q.1 q.2.1 q.2.2 k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope q.1 q.2.1)*eta| ≤ cStar/P.length q.1 ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ top j l, P.referenceCondition oldSlope (T top).slope (R top) cone w j l →
        (∃ k, b j l k (T top).slope ≠ 0) →
        cb*w/P.length j ≤ |oldSlope+P.rowSlope j l-(T top).slope| ∧
          |oldSlope+P.rowSlope j l-(T top).slope| ≤ Cb*w/P.length j) →
      J ≤ J₀ → E = SourceParameters.stepExponent L*SourceParameters.blockCount L →
      let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
        oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      let orig := fun top j (l : (Q top).labels j) =>
        ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
          oldSlope (T top).slope (R top) cone w j l).val.2
      let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        alt j (orig top j l) u.val k
      let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
        hAlt j (orig top j l) u.val k
      ∃ bad : Set (ℝ×ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-rate*L)*(∑ top, (T top).area)) ∧
        ∀ top lower upper, lower ≤ upper → upper ≤ N → ∀ z shift,
          |shift| ≤ (T top).width → z ∉ bad →
          let V := fun x y => ((Q top).withProfile (a top) (ha top)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
              j (orig top j l) u.val) 0 lower upper x y
          ‖V z.1 (z.2-(T top).slope*z.1+shift)‖+(T top).width*
            ‖covariantSignal P.frequency (fun k y => V z.1 y k)
              (z.2-(T top).slope*z.1+shift)‖ ≤
                L^(2*p+8)*((T top).weight (L^aWeight) (D:ℝ) z)^8 := by
  filter_upwards [SourceLabeledLattice.eventually_source_selector_concentration_of_supported hL cStar cEta CEta cb Cb F
    hcStar hcEta hCEta hcb hCb hF hgap rate aWeight p Lip D K H J₀
    hrate haWeight hp hLip] with L hconc
  intro τ κ _ _ N Label Item _ P packets assigned hP horder alt hAlt T oldSlope R cone w
    hw hcone hwide hfrequency hwidth hscale hX hZ angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius hlocal b hb hb1 hsupport hnear hfar
    v hv f hf hf1 hspectrum haltSpectrum hsep hJ hE
  classical
  let Q := fun top => (P.assignedTopFamily packets assigned top).referenceFamily
    oldSlope (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
  let orig := fun top j (l : (Q top).labels j) =>
    ((P.assignedTopFamily packets assigned top).referenceOriginalLabel
      oldSlope (T top).slope (R top) cone w j l).val.2
  let a := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
    alt j (orig top j l) u.val k
  let ha := fun top j (l : (Q top).labels j) (u : P.AssignedTopItem packets assigned j l) k =>
    hAlt j (orig top j l) u.val k
  change ∃ bad, _
  have hcond top j (l : (Q top).labels j) :
      P.referenceCondition oldSlope (T top).slope (R top) cone w j (orig top j l) :=
    P.assignedTopReference_condition packets assigned top oldSlope (T top).slope
      (R top) cone w F hw hcone hF hwide hfrequency j l
  have hgeometry top : SourceSupportedLabeledTopGeometry (Q top) (T top) (L^aWeight) D := by
    apply P.assignedTopReference_supportedTopGeometry packets assigned top oldSlope (R top) cone w F
      hw hcone hF hwide hfrequency (T top) (L^aWeight) D
      (hwidth top) (by omega) (hscale top)
    · intro q hq heq
      simpa only [heq] using hX q hq
    · intro q hq heq
      simpa only [heq] using hZ q hq
  have hcenter top j (l : (Q top).labels j) :
      (T top).slope+(Q top).rowSlope j l = oldSlope+P.rowSlope j (orig top j l) :=
    P.assignedTopReference_physical_center packets assigned top oldSlope (T top).slope
      (R top) cone w F hw hcone hF hwide hfrequency j l
  have hactive top j (l : (Q top).labels j)
      (hl : ∃ k, b j (orig top j l) k (T top).slope ≠ 0) :
      cb*w/(Q top).length j ≤ |(Q top).rowSlope j l| ∧
        |(Q top).rowSlope j l| ≤ Cb*w/(Q top).length j := by
    have hs := hsep top j (orig top j l) (hcond top j l) hl
    have he : (Q top).rowSlope j l = oldSlope+P.rowSlope j (orig top j l)-(T top).slope := by
      linarith [hcenter top j l]
    rw [he]
    exact hs
  obtain ⟨bad,hbad,harea,hpoint⟩ := hconc τ κ (fun _ => N)
    (fun _ j => τ×P.labels j) (fun _ => P.AssignedTopItem packets assigned) Q
    (fun _ => hP) (fun _ => horder) a ha T hgeometry angle small wide radius E J
    hangle hsmall hsmall1 hwideScale hwide1 hradius
    (fun top j => P.assignedTopReference_localMultiplicity packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency j
      (angle top*(2:ℝ)^j.val) H (hlocal top j))
    (fun top j l => b j (orig top j l))
    (fun _ j l k => hb j _ k) (fun _ j l k s => hb1 j _ k s)
    (by
      intro top j l k s hs
      rw [hcenter top j l]
      exact hsupport top j (orig top j l) k s (hcond top j l) hs)
    (fun top j l k s => hnear top j (orig top j l) k s (hcond top j l))
    (fun top j l k s => hfar top j (orig top j l) k s (hcond top j l))
    (fun _ => v) (fun _ => hv) (fun _ => f) (fun _ => hf) (fun _ => hf1) w hw
    (fun _ => hfrequency)
    (fun top => P.assignedTopReference_spectrum packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      cStar cEta CEta (fun q hq _ => hspectrum q hq))
    (fun top => P.assignedTopReference_alt_spectrum packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency
      alt hAlt cStar cEta CEta (fun q hq _ => haltSpectrum q hq))
    hactive hJ hE
  refine ⟨bad,hbad,harea,?_⟩
  intro top lower upper hlu hu z shift hshift hz
  have hcoeff : (Q top).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig top j l)) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  have h := hpoint top lower upper hlu hu z shift hshift hz
  rw [hcoeff] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported_oai := @OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_top_selector_concentration_of_supported_oai
