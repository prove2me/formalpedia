-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:41:26.213142+00:00
-- url     : https://prove2.me/submissions/ceeca1a0-4617-49a4-bf88-3d87c5a84900

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C016
import Definitions.Def_OAIQ091C018
import Theorems.Thm_OAI_PositiveEinsteinFour_quadratic_form_nonneg_of_det

section
-- module Solutions.OAIQ091_EF.Compat
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureContraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion contractions in the derivative-slot Green formula. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi Angular

noncomputable section

theorem mixed_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, quaternionMatrix s i k * oppositeMatrix r i k) = 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;>
    simp [TraceHessian.quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion] <;>
      (try split_ifs) <;> norm_num

end

end PositiveEinsteinFour.CurvatureContraction

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_OperatorGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted integration by parts retains the derivative of a varying
matrix-slot coefficient. The Weyl Hessian calculation applies the flow Green identity twice
to the nonparallel coefficient. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- A variable scalar tensor coefficient contributes its divergence term.
Summing this identity is the derivative-slot curvature integration step. -/
theorem weighted_scalar_coefficient_green
    (φ : ℝ → Ω ≃ᵐ Ω)
    (hφ : Continuous (fun p : ℝ × Ω => φ p.1 p.2))
    (hμ : ∀ t, MeasurePreserving (φ t) μ μ)
    (m dm a da : C(Ω, ℝ)) (f df g dg : C(Ω, E))
    (hm : ∀ t x, HasDerivAt (fun s => m (φ s x)) (dm (φ t x)) t)
    (ha : ∀ t x, HasDerivAt (fun s => a (φ s x)) (da (φ t x)) t)
    (hf : ∀ t x, HasDerivAt (fun s => f (φ s x)) (df (φ t x)) t)
    (hg : ∀ t x, HasDerivAt (fun s => g (φ s x)) (dg (φ t x)) t) :
    (∫ x, m x * a x * inner ℝ (f x) (dg x) +
      dm x * a x * inner ℝ (f x) (g x) ∂μ) =
      -(∫ x, m x * a x * inner ℝ (df x) (g x) ∂μ) -
        ∫ x, m x * da x * inner ℝ (f x) (g x) ∂μ := by
  let w : C(Ω, ℝ) := ⟨fun x => m x * a x, by fun_prop⟩
  let dw : C(Ω, ℝ) := ⟨fun x => dm x * a x + m x * da x, by fun_prop⟩
  have hw (t : ℝ) (x : Ω) :
      HasDerivAt (fun s => w (φ s x)) (dw (φ t x)) t := (hm t x).mul (ha t x)
  have h := weighted_flow_green μ φ hφ hμ w dw f df g dg hw hf hg
  have hA : Integrable (fun x => m x * a x * inner ℝ (f x) (dg x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun x => dm x * a x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x => m x * a x * inner ℝ (df x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (fun x => m x * da x * inner ℝ (f x) (g x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (fun x => w x * inner ℝ (df x) (g x) + dw x * inner ℝ (f x) (g x)) =
      (fun x => (m x * a x * inner ℝ (df x) (g x) +
        dm x * a x * inner ℝ (f x) (g x)) + m x * da x * inner ℝ (f x) (g x)) := by
    funext x
    dsimp [w, dw]
    ring
  have hJB : Integrable (fun x => m x * a x * inner ℝ (df x) (g x) +
      dm x * a x * inner ℝ (f x) (g x)) μ := hJ.add hB
  rw [he, integral_add hJB hK, integral_add hJ hB] at h
  change _ = -(∫ x, m x * a x * inner ℝ (f x) (dg x) ∂μ) at h
  rw [integral_add hA hB]
  linarith

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-slot curvature integration. Divergence freedom removes
the differentiated coefficient, and skew-symmetry leaves exactly one half
of the covariant commutator. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem divergence_sum_zero
    (A : CurvatureIndex → C(Ω, ℝ)) (X : Fin 4 → Fin 4 → C(Ω, E))
    (Z : Fin 4 → C(Ω, E))
    (hdiv : ∀ i j l x, (∑ k, A ((i, k), (j, l)) x) = 0) (x : Ω) :
    (∑ p : CurvatureIndex, A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) = 0 := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  calc
    _ = ∑ j, ∑ k, ∑ l, A ((i, k), (j, l)) x * inner ℝ (X i j x) (Z l x) :=
      Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, A ((i, k), (j, l)) x * inner ℝ (X i j x) (Z l x) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = 0 := by
      simp_rw [← Finset.sum_mul, hdiv, zero_mul]
      simp

private theorem skew_commutator_sum
    (A : CurvatureIndex → C(Ω, ℝ))
    (D : Fin 4 → Fin 4 → Fin 4 → C(Ω, E)) (Z : Fin 4 → C(Ω, E))
    (hskew : ∀ i k j l x, A ((k, i), (j, l)) x = -A ((i, k), (j, l)) x)
    (x : Ω) :
    -(∑ p : CurvatureIndex, A p x *
      inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) =
      (1 / 2 : ℝ) * (∑ p : CurvatureIndex, A p x *
        inner ℝ (D p.1.1 p.1.2 p.2.1 x - D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) := by
  have hs : (∑ p : CurvatureIndex, A p x *
      inner ℝ (D p.1.1 p.1.2 p.2.1 x) (Z p.2.2 x)) =
      -(∑ p : CurvatureIndex, A p x *
        inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) := by
    calc
      _ = ∑ p : CurvatureIndex, A (outerSwap p) x *
          inner ℝ (D (outerSwap p).1.1 (outerSwap p).1.2 (outerSwap p).2.1 x)
            (Z (outerSwap p).2.2 x) := (outerSwap.sum_comp _).symm
      _ = _ := by
        change (∑ p : CurvatureIndex, A ((p.1.2, p.1.1), p.2) x *
          inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) = _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [hskew]
        ring
  simp_rw [inner_sub_left, mul_sub, Finset.sum_sub_distrib]
  rw [hs]
  ring

variable [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Integrating a divergence-free curvature coefficient leaves the precise
half-commutator term. All first-derivative weight terms are retained. -/
theorem weighted_curvature_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ k, Continuous (fun p : ℝ × Ω => φ k p.1 p.2))
    (hμ : ∀ k t, MeasurePreserving (φ k t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (A dA : CurvatureIndex → C(Ω, ℝ))
    (Z : Fin 4 → C(Ω, E)) (X : Fin 4 → Fin 4 → C(Ω, E))
    (D : Fin 4 → Fin 4 → Fin 4 → C(Ω, E))
    (hdiv : ∀ i j l x, (∑ k, dA ((i, k), (j, l)) x) = 0)
    (hskew : ∀ i k j l x, A ((k, i), (j, l)) x = -A ((i, k), (j, l)) x)
    (hm : ∀ k t x, HasDerivAt (fun s => m (φ k s x)) (dm k (φ k t x)) t)
    (hA : ∀ p t x, HasDerivAt (fun s => A p (φ p.1.2 s x)) (dA p (φ p.1.2 t x)) t)
    (hZ : ∀ k j t x, HasDerivAt (fun s => Z j (φ k s x)) (X k j (φ k t x)) t)
    (hX : ∀ k i j t x, HasDerivAt (fun s => X i j (φ k s x)) (D k i j (φ k t x)) t) :
    (∫ x, ∑ p : CurvatureIndex,
      (m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) ∂μ) =
      (1 / 2 : ℝ) * (∫ x, ∑ p : CurvatureIndex, m x * A p x *
        inner ℝ (D p.1.1 p.1.2 p.2.1 x - D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) := by
  have hL (p : CurvatureIndex) : Integrable (fun x =>
      m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ (p : CurvatureIndex) : Integrable (fun x => m x * A p x *
      inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK (p : CurvatureIndex) : Integrable (fun x => m x * dA p x *
      inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : (∫ x, ∑ p : CurvatureIndex,
      (m x * A p x * inner ℝ (X p.1.1 p.2.1 x) (X p.1.2 p.2.2 x) +
        dm p.1.2 x * A p x * inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) ∂μ) =
      -(∫ x, ∑ p : CurvatureIndex, m x * A p x *
        inner ℝ (D p.1.2 p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) -
      (∫ x, ∑ p : CurvatureIndex, m x * dA p x *
        inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) := by
    rw [integral_finsetSum _ (fun p _ => hL p),
      integral_finsetSum _ (fun p _ => hJ p),
      integral_finsetSum _ (fun p _ => hK p)]
    simp_rw [weighted_scalar_coefficient_green μ _ (hφ _) (hμ _) m (dm _) (A _) (dA _)
      (X _ _) (D _ _ _) (Z _) (X _ _) (hm _) (hA _) (hX _ _ _) (hZ _ _)]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hz : (∫ x, ∑ p : CurvatureIndex, m x * dA p x *
      inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x) ∂μ) = 0 := by
    have he (x : Ω) : (∑ p : CurvatureIndex, m x * dA p x *
        inner ℝ (X p.1.1 p.2.1 x) (Z p.2.2 x)) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, divergence_sum_zero dA X Z hdiv x, mul_zero]
    simp_rw [he]
    simp
  rw [hs, hz, sub_zero, ← integral_neg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := skew_commutator_sum A D Z hskew x
  have hm' := congrArg (fun z : ℝ => m x * z) h
  rw [mul_left_comm (m x) (1 / 2 : ℝ)] at hm'
  simpa only [mul_neg, Finset.mul_sum, mul_assoc] using hm'

end

end PositiveEinsteinFour.Averages

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Matrix
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small positive semidefinite forms and Schur completion

The closed determinant criterion includes vanishing diagonal entries. The
Schur estimate below consequently includes the singular axial endpoint of the
quadratic comparison in Section 6 of the manuscript.
-/

namespace PositiveEinsteinFour

/-- Conversely, nonnegativity of the binary form implies the closed diagonal
and determinant conditions. The singular diagonal case is tested directly. -/
theorem quadratic_form_det_of_nonneg
    (r h s : ℝ)
    (hform : ∀ x y, 0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2) :
    0 ≤ r ∧ 0 ≤ h ∧ s ^ 2 ≤ r * h := by
  have hr : 0 ≤ r := by simpa using hform 1 0
  have hh : 0 ≤ h := by simpa using hform 0 1
  refine ⟨hr, hh, ?_⟩
  by_cases hrzero : r = 0
  · subst r
    have htest := hform (h + 1) (-s)
    have hhs : 0 ≤ h * s ^ 2 := mul_nonneg hh (sq_nonneg s)
    have hs : s = 0 := by nlinarith [sq_nonneg s]
    simp [hs]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    have htest := hform (-s) r
    have hproduct : 0 ≤ r * (r * h - s ^ 2) := by nlinarith
    have hdet := nonneg_of_mul_nonneg_right hproduct hrpos
    linarith

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Variance
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted Poisson argument and the scalar weight used to balance the
Weyl moments. The Bochner and Poisson identities imply the exact bound for the test
function, including zero norm values. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

noncomputable section

/-- An integral version of the closed two-by-two determinant criterion.
It needs no square-root integrability assumptions. -/
theorem integral_pairing_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g c : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hc : Integrable c μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hpoint : ∀ᵐ ω ∂μ, c ω ^ 2 ≤ f ω * g ω) :
    (∫ ω, c ω ∂μ) ^ 2 ≤ (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  apply (quadratic_form_det_of_nonneg _ _ _ ?_).2.2
  intro x y
  have hnonneg : 0 ≤ ∫ ω, f ω * x ^ 2 + 2 * c ω * x * y + g ω * y ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf0, hg0, hpoint] with ω hfω hgω hcω
    exact quadratic_form_nonneg_of_det _ _ _ hfω hgω hcω x y
  have h1 := integral_add ((hf.mul_const (x ^ 2)).add
    (((hc.const_mul 2).mul_const x).mul_const y)) (hg.mul_const (y ^ 2))
  have h2 := integral_add (hf.mul_const (x ^ 2))
    (((hc.const_mul 2).mul_const x).mul_const y)
  simp only [Pi.add_apply] at h1
  rw [h1, h2] at hnonneg
  simpa only [integral_mul_const, integral_const_mul] using hnonneg

/-- Abstract form of the weighted Poisson proof. For the geometric application,
`f = |grad a|²/K`, `g = K |grad phi|²`, and `c = -<grad a,grad phi>`;
integration by parts gives `E c = Var a`, while the improved Bochner identity
gives `E g ≤ Var a`. Neither geometric identity is assumed to be published. -/
theorem variance_le_of_poisson_pairing {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g c : Ω → ℝ} {V : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hc : Integrable c μ)
    (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hpoint : ∀ᵐ ω ∂μ, c ω ^ 2 ≤ f ω * g ω)
    (hV : 0 ≤ V) (hpair : (∫ ω, c ω ∂μ) = V)
    (hbochner : (∫ ω, g ω ∂μ) ≤ V) :
    V ≤ ∫ ω, f ω ∂μ := by
  have hF : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae hf0
  have hcs := integral_pairing_sq_le hf hg hc hf0 hg0 hpoint
  rw [hpair] at hcs
  have hmul := mul_le_mul_of_nonneg_left hbochner hF
  by_cases hz : V = 0
  · simpa [hz] using hF
  · have hp : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
    nlinarith

/-- Pointwise Cauchy--Schwarz with the reciprocal Poisson weight. -/
theorem weighted_inner_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a p : E) {K : ℝ} (hK : 0 < K) :
    (-inner ℝ a p) ^ 2 ≤ (‖a‖ ^ 2 / K) * (K * ‖p‖ ^ 2) := by
  have hcs := abs_real_inner_le_norm a p
  have habs : |inner ℝ a p| ^ 2 ≤ (‖a‖ * ‖p‖) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hcs
  have hid : (‖a‖ ^ 2 / K) * (K * ‖p‖ ^ 2) = ‖a‖ ^ 2 * ‖p‖ ^ 2 := by
    field_simp [ne_of_gt hK]
  rw [hid]
  simpa only [neg_sq, sq_abs, mul_pow] using habs

/-- The scalar consequence of the integrated Bochner identity and the
curvature contraction on trace-free Hessians. Here `p` and `s` are squared
gradient and trace-free Hessian norms, and `c` is the curvature contraction.
The two geometric identities are retained separately, rather than assuming
the improved weighted bound as a single premise. -/
theorem bochner_weighted_energy {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {v b p s c : Ω → ℝ} {L : ℝ}
    (hp : Integrable p μ) (hs : Integrable s μ) (hc : Integrable c μ)
    (hvp : Integrable (fun ω => (v ω ^ 2 + b ω ^ 2) * p ω) μ)
    (hbochner : L = 4 * (∫ ω, p ω ∂μ) + (4 / 3) * ∫ ω, s ω ∂μ)
    (hcurvature : (∫ ω, c ω ∂μ) = 3 * ∫ ω, (v ω ^ 2 + b ω ^ 2) * p ω ∂μ)
    (hoperator : ∀ᵐ ω ∂μ, c ω ≤ 4 * s ω) :
    (∫ ω, (4 + v ω ^ 2 + b ω ^ 2) * p ω ∂μ) ≤ L := by
  have hbound : (∫ ω, c ω ∂μ) ≤ 4 * ∫ ω, s ω ∂μ := by
    calc
      _ ≤ ∫ ω, 4 * s ω ∂μ := integral_mono_ae hc (hs.const_mul 4) hoperator
      _ = _ := integral_const_mul _ _
  have hid : (fun ω => (4 + v ω ^ 2 + b ω ^ 2) * p ω) =
      (fun ω => 4 * p ω + (v ω ^ 2 + b ω ^ 2) * p ω) := by
    funext ω
    ring
  rw [hid, integral_add (hp.const_mul 4) hvp, integral_const_mul]
  linarith

end

end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HVarianceApproximation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth approximation of the scalar test used in the weighted-variance
argument, with domination by the actual square-root energy. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

theorem hRegularizedArgument_pos (b ε : ℝ) (hε : 0 < ε) :
    0 < hRegularizedArgument b ε := by
  apply Real.sqrt_pos.2
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  nlinarith [sq_nonneg b]

theorem le_hRegularizedArgument (b ε : ℝ) (_hb : 0 ≤ b) :
    b ≤ hRegularizedArgument b ε := by
  unfold hRegularizedArgument
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ε]

theorem hRegularizedArgument_le_three (b ε : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) : hRegularizedArgument b ε ≤ 3 := by
  unfold hRegularizedArgument
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · have hb2 : b ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2), hb.2]
    have he2 : ε ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hε.1 (sub_nonneg.mpr hε.2), hε.2]
    nlinarith

theorem continuous_hRegularizedArgument : Continuous (fun x : ℝ × ℝ =>
    hRegularizedArgument x.1 x.2) := by
  unfold hRegularizedArgument
  fun_prop

theorem hRegularizedArgument_zero (b : ℝ) (hb : 0 ≤ b) :
    hRegularizedArgument b 0 = b := by
  simp only [hRegularizedArgument, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hb]

theorem tendsto_hRegularizedArgument (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (hRegularizedArgument b) (𝓝 0) (𝓝 b) := by
  have hc : Continuous (fun ε : ℝ => hRegularizedArgument b ε) :=
    continuous_hRegularizedArgument.comp (continuous_const.prodMk continuous_id)
  simpa only [hRegularizedArgument_zero b hb] using hc.tendsto 0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aemeasurable_hRegularizedArgument {b : Ω → ℝ} (hb : AEMeasurable b μ) (ε : ℝ) :
    AEMeasurable (fun x => hRegularizedArgument (b x) ε) μ := by
  exact ((hb.pow_const 2).add aemeasurable_const).sqrt

end
end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_NormVarianceApproximation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated smooth approximation of both Weyl norms and their difference.
The gradient limit uses the actual zero-set support property. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter
open scoped _root_.Topology ContDiff

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem regularizedRadialVector_norm_le {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (p : F) :
    ‖regularizedRadialVector b ε p‖ ≤ ‖p‖ := by
  have hr := hRegularizedArgument_pos b ε hε
  have hc0 : 0 ≤ b / hRegularizedArgument b ε := div_nonneg hb hr.le
  have hc1 : b / hRegularizedArgument b ε ≤ 1 :=
    (div_le_one hr).2 (le_hRegularizedArgument b ε hb)
  rw [regularizedRadialVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  exact mul_le_of_le_one_left (norm_nonneg p) hc1

theorem regularizedDifference_square_le {v b ε : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hε : 0 < ε) (p q : F) :
    ‖regularizedRadialVector v ε p - regularizedRadialVector b ε q‖ ^ 2 ≤
      2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have hn := (norm_sub_le (regularizedRadialVector v ε p)
    (regularizedRadialVector b ε q)).trans
    (add_le_add (regularizedRadialVector_norm_le hv hε p)
      (regularizedRadialVector_norm_le hb hε q))
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg p) (norm_nonneg q))).2 hn
  nlinarith [sq_nonneg (‖p‖ - ‖q‖)]

theorem regularizedDifferenceEnergy_nonneg {v b ε K : ℝ} (hK : 0 ≤ K) (p q : F) :
    0 ≤ regularizedDifferenceEnergy v b ε K p q := div_nonneg (sq_nonneg _) hK

theorem regularizedDifferenceEnergy_le {v b ε K : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hε : 0 < ε) (hK : 1 ≤ K) (p q : F) :
    regularizedDifferenceEnergy v b ε K p q ≤ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  unfold regularizedDifferenceEnergy
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hK)).2
  have hs := regularizedDifference_square_le hv hb hε p q
  have hm := mul_le_mul_of_nonneg_left hK
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖q‖)))
  nlinarith

theorem tendsto_regularizedRadialVector (b : ℝ) (p : F) (hb : 0 ≤ b)
    (hz : b = 0 → p = 0) :
    Tendsto (fun ε => regularizedRadialVector b ε p) (𝓝 0) (𝓝 p) := by
  by_cases hzero : b = 0
  · subst b
    rw [hz rfl]
    simp [regularizedRadialVector]
  have h : Tendsto (fun ε => (b / hRegularizedArgument b ε) • p) (𝓝 0)
      (𝓝 ((b / b) • p)) :=
    (tendsto_const_nhds.div (tendsto_hRegularizedArgument b hb) hzero).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => p) (𝓝 0) (𝓝 p))
  simpa only [regularizedRadialVector, div_self hzero, one_smul] using h

theorem tendsto_regularizedDifferenceEnergy (v b K : ℝ) (p q : F)
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : v = 0 → p = 0) (hq : b = 0 → q = 0) :
    Tendsto (fun ε => regularizedDifferenceEnergy v b ε K p q) (𝓝 0)
      (𝓝 (‖p - q‖ ^ 2 / K)) :=
  (((tendsto_regularizedRadialVector v p hv hp).sub
    (tendsto_regularizedRadialVector b q hb hq)).norm.pow 2).div_const K

theorem regularizedNormEnergy_eq_difference (b ε K : ℝ) (p : F) :
    regularizedNormEnergy b ε K p = regularizedDifferenceEnergy b 0 ε K p 0 := by
  simp [regularizedNormEnergy, regularizedDifferenceEnergy, regularizedRadialVector]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aestronglyMeasurable_regularizedRadialVector {b : Ω → ℝ} {p : Ω → F}
    (hb : AEMeasurable b μ) (hp : AEStronglyMeasurable p μ) (ε : ℝ) :
    AEStronglyMeasurable (fun x => regularizedRadialVector (b x) ε (p x)) μ :=
  (hb.div (aemeasurable_hRegularizedArgument hb ε)).aestronglyMeasurable.smul hp

theorem integral_regularizedDifferenceEnergy_tendsto {v b K : Ω → ℝ} {p q : Ω → F}
    (hv : AEMeasurable v μ) (hb : AEMeasurable b μ) (hK : AEMeasurable K μ)
    (hp : AEStronglyMeasurable p μ) (hq : AEStronglyMeasurable q μ)
    (hv0 : ∀ᵐ x ∂μ, 0 ≤ v x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hq0 : ∀ᵐ x ∂μ, b x = 0 → q x = 0)
    (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ) (hq2 : Integrable (fun x => ‖q x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedDifferenceEnergy (v x) (b x) (ε n) (K x) (p x) (q x) ∂μ)
      atTop (𝓝 (∫ x, ‖p x - q x‖ ^ 2 / K x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 2 * (‖p x‖ ^ 2 + ‖q x‖ ^ 2))
  · intro n
    exact ((((aestronglyMeasurable_regularizedRadialVector hv hp (ε n)).sub
      (aestronglyMeasurable_regularizedRadialVector hb hq (ε n))).norm.pow 2).aemeasurable.div
        hK).aestronglyMeasurable
  · exact (hp2.add hq2).const_mul 2
  · intro n
    filter_upwards [hv0, hb0, hK1] with x hvx hbx hKx
    rw [Real.norm_eq_abs, abs_of_nonneg (regularizedDifferenceEnergy_nonneg (by linarith) _ _)]
    exact regularizedDifferenceEnergy_le hvx hbx (hε n) hKx (p x) (q x)
  · filter_upwards [hv0, hb0, hp0, hq0] with x hvx hbx hpx hqx
    exact (tendsto_regularizedDifferenceEnergy (v x) (b x) (K x) (p x) (q x)
      hvx hbx hpx hqx).comp hlim

theorem integral_regularizedNormEnergy_tendsto {v K : Ω → ℝ} {p : Ω → F}
    (hv : AEMeasurable v μ) (hK : AEMeasurable K μ) (hp : AEStronglyMeasurable p μ)
    (hv0 : ∀ᵐ x ∂μ, 0 ≤ v x) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedNormEnergy (v x) (ε n) (K x) (p x) ∂μ)
      atTop (𝓝 (∫ x, ‖p x‖ ^ 2 / K x ∂μ)) := by
  have h := integral_regularizedDifferenceEnergy_tendsto
    (v := v) (b := fun _ => (0 : ℝ)) (K := K) (p := p) (q := fun _ => (0 : F))
    hv aemeasurable_const hK hp aestronglyMeasurable_const hv0
    (Filter.Eventually.of_forall (fun _ => le_rfl)) hK1 hp0
    (Filter.Eventually.of_forall (fun _ _ => rfl)) hp2
    (by simp) ε hε hlim
  simpa only [← regularizedNormEnergy_eq_difference, sub_zero] using h

theorem integral_regularizedNorm_pow_tendsto [IsFiniteMeasure μ] {v : Ω → ℝ}
    (hv : AEMeasurable v μ) (hv2 : ∀ᵐ x ∂μ, v x ∈ Set.Icc (0 : ℝ) 2)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => ∫ x, hRegularizedArgument (v x) (ε n) ^ k ∂μ) atTop
      (𝓝 (∫ x, v x ^ k ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (3 : ℝ) ^ k)
  · intro n
    exact ((aemeasurable_hRegularizedArgument hv (ε n)).pow_const k).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hv2] with x hx
    rw [Real.norm_eq_abs, abs_pow, abs_of_pos (hRegularizedArgument_pos _ _ (hε n).1)]
    exact pow_le_pow_left₀ (hRegularizedArgument_pos _ _ (hε n).1).le
      (hRegularizedArgument_le_three _ _ hx ⟨(hε n).1.le, (hε n).2⟩) k
  · filter_upwards [hv2] with x hx
    exact ((tendsto_hRegularizedArgument (v x) hx.1).comp hlim).pow k

/-- Difference-of-moments variance depends only on the almost-everywhere class. -/
theorem variance_congr_ae {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 =
      (∫ x, g x ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 := by
  have h1 := integral_congr_ae hfg
  have h2 := integral_congr_ae (hfg.mono (fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx))
  rw [h1, h2]

/-- For probability measure, the centered-square and difference-of-moments
forms agree under precisely the first and second moment integrability. -/
theorem integral_centered_square [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  have hpoly (x : Ω) : (f x - ∫ y, f y ∂μ) ^ 2 =
      f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x + (∫ y, f y ∂μ) ^ 2 := by ring
  have hadd := integral_add (hf2.sub (hf.const_mul (2 * ∫ y, f y ∂μ)))
    (integrable_const ((∫ y, f y ∂μ) ^ 2))
  have hsub := integral_sub hf2 (hf.const_mul (2 * ∫ y, f y ∂μ))
  simp only [Pi.sub_apply] at hadd hsub
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoly), hadd, hsub, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Either single norm is obtained by the same approximation, with its
own actual radial gradient and zero-set support. -/
theorem norm_variance_of_regularized [IsFiniteMeasure μ] {v K : Ω → ℝ} {p : Ω → F}
    (hv : AEMeasurable v μ) (hK : AEMeasurable K μ) (hp : AEStronglyMeasurable p μ)
    (hv2 : ∀ᵐ x ∂μ, v x ∈ Set.Icc (0 : ℝ) 2) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hvariance : ∀ n, (∫ x, hRegularizedArgument (v x) (ε n) ^ 2 ∂μ) -
      (∫ x, hRegularizedArgument (v x) (ε n) ∂μ) ^ 2 ≤
        ∫ x, regularizedNormEnergy (v x) (ε n) (K x) (p x) ∂μ) :
    (∫ x, v x ^ 2 ∂μ) - (∫ x, v x ∂μ) ^ 2 ≤ ∫ x, ‖p x‖ ^ 2 / K x ∂μ := by
  have h1 := integral_regularizedNorm_pow_tendsto hv hv2 ε hε hlim 1
  simp only [pow_one] at h1
  have h2 := integral_regularizedNorm_pow_tendsto hv hv2 ε hε hlim 2
  have he := integral_regularizedNormEnergy_tendsto hv hK hp
    (hv2.mono (fun _ hx => hx.1)) hK1 hp0 hp2 ε (fun n => (hε n).1) hlim
  exact le_of_tendsto_of_tendsto (h2.sub (h1.pow 2)) he (Filter.Eventually.of_forall hvariance)

end
end PositiveEinsteinFour.Variance

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Smooth norm regularization for the actual squared Weyl weight.
The positive regularization parameter allows the Green identities to be
used at Weyl zeros as well as on the positive-norm set. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian Filter
open scoped _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedRing
local instance smoothWeylNormedSpace_r8e6650_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.smoothWeylNormedAlgebra
theorem tendsto_regularizedBlockNorm (A : Mat) :
    Tendsto (fun ε => regularizedBlockNorm ε A) (𝓝 0) (𝓝 (normalizedBlockNorm A)) := by
  have hc : Continuous (fun ε => regularizedBlockNorm ε A) := by
    unfold regularizedBlockNorm
    fun_prop
  simpa only [regularizedBlockNorm_zero] using hc.tendsto 0

theorem tendsto_regularizedRadialDerivative (A Z : Mat) :
    Tendsto (fun ε => regularizedRadialDerivative ε A Z) (𝓝 0)
      (𝓝 (Matrix.trace (A * Z) / (6 * normalizedBlockNorm A))) := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA : A = 0 := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul (tendsto_regularizedBlockNorm A))
      (mul_ne_zero (by norm_num) ha)

theorem abs_trace_mul_le_norm (A Z : Mat) (hZ : symmetric Z) :
    |Matrix.trace (A * Z)| ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := by
  have hzt : Zᵀ = Z := by ext i j; exact hZ j i
  have hp : matrixPairing A Z = Matrix.trace (A * Z) := by
    rw [matrixPairing_eq_trace, hzt]
  have h := real_inner_mul_inner_self_le (matrixVector A) (matrixVector Z)
  simp only [inner_matrixVector, matrixPairing_self_norm, hp] at h
  apply abs_le_of_sq_le_sq _
    (mul_nonneg (mul_nonneg (by norm_num) (normalizedBlockNorm_nonneg A))
      (normalizedBlockNorm_nonneg Z))
  nlinarith only [h]

/-- The regularized derivative has a bound independent of the smoothing
parameter. This is the domination needed at Weyl zeros. -/
theorem abs_regularizedRadialDerivative_le (ε : ℝ) (hε : 0 < ε)
    (A Z : Mat) (hZ : symmetric Z) :
    |regularizedRadialDerivative ε A Z| ≤ normalizedBlockNorm Z := by
  have hn := regularizedBlockNorm_pos ε hε A
  rw [regularizedRadialDerivative, abs_div, abs_of_pos (mul_pos (by norm_num) hn),
    div_le_iff₀ (mul_pos (by norm_num) hn)]
  calc
    _ ≤ 6 * normalizedBlockNorm A * normalizedBlockNorm Z := abs_trace_mul_le_norm A Z hZ
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (norm_le_regularizedBlockNorm ε A)
        (normalizedBlockNorm_nonneg Z)
      nlinarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature contractions with the entire symmetric Weyl matrix.
No moving eigenframe enters these identities. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open Matrix TraceHessian Bianchi PositiveEinsteinFour.Geometry

noncomputable section

theorem generalCoefficient_eq_blockTensor (Q : Fin 3 → Mat4) (A : Mat)
    (i k j l : Fin 4) :
    generalCoefficient Q A i k j l = Angular.blockTensor A Q i k l j := by
  simp only [generalCoefficient, Angular.blockTensor, Angular.twoFormProduct,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

private theorem generalCoefficient_oneForm
    (Q P : Fin 3 → Mat4)
    (hQP : ∀ r t, (∑ i, ∑ k, Q r i k * P t i k) =
      if r = t then (4 : ℝ) else 0)
    (A : Mat) (t : Fin 3) (j l : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * P t i k) =
      2 * ∑ s, A t s * Q s j l := by
  simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_swap]
  have hterm (r s : Fin 3) :
      (∑ i, ∑ k, (1 / 2 : ℝ) * (A r s * Q r i k * Q s j l) * P t i k) =
        (1 / 2 : ℝ) * A r s * Q s j l * (∑ i, ∑ k, Q r i k * P t i k) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm, hQP]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, if_true]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem clifford_column_pairing
    (Q : Fin 3 → Mat4)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (r s : Fin 3) (l h : Fin 4) :
    (∑ j, Q r j l * Q s j h) + (∑ j, Q s j l * Q r j h) =
      (if r = s then (2 : ℝ) else 0) * (if l = h then 1 else 0) := by
  have hs (t : Fin 3) (j : Fin 4) : Q t l j = -Q t j l := by
    have hx := congrArg (fun M : Mat4 => M j l) (hskew t)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using hx
  have ha := congrArg (fun M : Mat4 => M l h) (hanti r s)
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, hs, neg_mul, Finset.sum_neg_distrib] at ha
  by_cases hrs : r = s <;> simp only [hrs, ite_true, if_true, ite_false, if_false] at * <;> linarith

/-- A symmetric coefficient contracts the Clifford product to its trace.
This includes all off-diagonal matrix entries. -/
theorem symmetric_clifford_column_contraction
    (Q : Fin 3 → Mat4)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (C : Mat) (hC : symmetric C) (l h : Fin 4) :
    (∑ r, ∑ s, C r s * (∑ j, Q r j l * Q s j h)) =
      Matrix.trace C * (if l = h then 1 else 0) := by
  have hswap : (∑ r, ∑ s, C r s * (∑ j, Q s j l * Q r j h)) =
      ∑ r, ∑ s, C r s * (∑ j, Q r j l * Q s j h) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [hC s r]
  have hd : (∑ r, ∑ s, C r s *
      ((∑ j, Q r j l * Q s j h) + (∑ j, Q s j l * Q r j h))) =
      2 * Matrix.trace C * (if l = h then 1 else 0) := by
    simp_rw [clifford_column_pairing Q hskew hanti]
    by_cases hlh : l = h
    · simp only [hlh, ite_true, if_true, mul_one, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, Matrix.trace, Matrix.diag]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    · simp only [hlh, ite_false, if_false, mul_zero, Finset.sum_const_zero]
  simp only [mul_add, Finset.sum_add_distrib, hswap] at hd
  linarith

private theorem pair_generalCoefficient (K : Mat4) (Q : Fin 3 → Mat4)
    (B : Mat) (h n : Fin 4) :
    (∑ i, ∑ k, K i k * generalCoefficient Q B i k h n) =
      (1 / 2 : ℝ) * ∑ r, ∑ s, B r s * Q s h n *
        (∑ i, ∑ k, K i k * Q r i k) := by
  simp only [generalCoefficient, Finset.mul_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem generalCoefficient_pairing
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, (∑ i, ∑ k, Q r i k * Q s i k) =
      if r = s then (4 : ℝ) else 0)
    (A B : Mat) (j l h n : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient Q B i k h n) =
      ∑ r, ∑ s, (Aᵀ * B) r s * Q r j l * Q s h n := by
  rw [pair_generalCoefficient (fun i k => generalCoefficient Q A i k j l) Q B h n]
  simp_rw [generalCoefficient_oneForm Q Q hQ]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

private theorem generalCoefficient_pairing_zero
    (Q P : Fin 3 → Mat4)
    (hQP : ∀ r s, (∑ i, ∑ k, Q r i k * P s i k) = 0)
    (A B : Mat) (j l h n : Fin 4) :
    (∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient P B i k h n) = 0 := by
  rw [pair_generalCoefficient (fun i k => generalCoefficient Q A i k j l) P B h n]
  have hz (r : Fin 3) :
      (∑ i, ∑ k, generalCoefficient Q A i k j l * P r i k) = 0 := by
    simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul]
    rw [sum_four_swap]
    have ht (s t : Fin 3) :
        (∑ i, ∑ k, (1 / 2 : ℝ) * (A s t * Q s i k * Q t j l) * P r i k) =
          (1 / 2 : ℝ) * A s t * Q t j l * (∑ i, ∑ k, Q s i k * P r i k) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [ht, hQP]
    simp
  simp only [hz, mul_zero, Finset.sum_const_zero]

private theorem generalCoefficient_ricci
    (Q : Fin 3 → Mat4)
    (hQ : ∀ r s, (∑ i, ∑ k, Q r i k * Q s i k) =
      if r = s then (4 : ℝ) else 0)
    (hskew : ∀ s, (Q s)ᵀ = -Q s)
    (hanti : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Mat4))
    (A B : Mat) (hAB : symmetric (Aᵀ * B)) (l h : Fin 4) :
    (∑ j, ∑ i, ∑ k, generalCoefficient Q A i k j l * generalCoefficient Q B i k j h) =
      Matrix.trace (Aᵀ * B) * (if l = h then 1 else 0) := by
  simp_rw [generalCoefficient_pairing Q hQ]
  calc
    _ = ∑ r, ∑ j, ∑ s, (Aᵀ * B) r s * Q r j l * Q s j h := Finset.sum_comm
    _ = ∑ r, ∑ s, (Aᵀ * B) r s * (∑ j, Q r j l * Q s j h) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := symmetric_clifford_column_contraction Q hskew hanti _ hAB l h

private theorem transpose_mul_one_add (A : Mat) (hs : symmetric A) :
    Aᵀ * (1 + A) = A + A * A := by
  have hAt : Aᵀ = A := by ext a b; exact hs b a
  rw [hAt, Matrix.mul_add, Matrix.mul_one]

private theorem symmetric_add_square (A : Mat) (hs : symmetric A) :
    symmetric (A + A * A) := by
  have hAt : Aᵀ = A := by ext a b; exact hs b a
  have h := show (A + A * A)ᵀ = A + A * A by
    simp only [Matrix.transpose_add, Matrix.transpose_mul, hAt]
  intro a b
  exact congrArg (fun M : Mat => M b a) h

/-- The covector contraction of the full plus block gives its squared
matrix norm, including all off-diagonal entries. -/
theorem plus_generalCoefficient_ricci (A U : Mat)
    (hs : symmetric A) (ht : traceFree A) (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k, generalCoefficient quaternionMatrix A i k j l *
      (generalCoefficient quaternionMatrix (1 + A) i k j h +
        generalCoefficient Angular.oppositeMatrix (1 + U) i k j h)) =
      (Matrix.trace (A * A) / 2) * (if l = h then 1 else 0) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hz (j : Fin 4) := generalCoefficient_pairing_zero _ _ mixed_twoForm_pairing
    A (1 + U) j l j h
  simp_rw [hz]
  simp only [Finset.sum_const_zero, mul_zero, add_zero]
  have hAB : symmetric (Aᵀ * (1 + A)) := by
    rw [transpose_mul_one_add A hs]
    exact symmetric_add_square A hs
  rw [generalCoefficient_ricci quaternionMatrix plus_twoForm_pairing
    Angular.quaternionMatrix_transpose Angular.quaternionMatrix_anticommutator _ _ hAB,
    transpose_mul_one_add A hs, Matrix.trace_add]
  have htrace : Matrix.trace A = 0 := ht
  rw [htrace]
  ring

private theorem oppositeMatrix_transpose (r : Fin 3) :
    (Angular.oppositeMatrix r)ᵀ = -Angular.oppositeMatrix r := by
  ext i j
  change Geometry.oppositeQuaternion r j i = -Geometry.oppositeQuaternion r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [Geometry.oppositeQuaternion, quaternionMatrix]

theorem minus_generalCoefficient_ricci (A U : Mat)
    (hs : symmetric U) (ht : traceFree U) (l h : Fin 4) :
    (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k, generalCoefficient Angular.oppositeMatrix U i k j l *
      (generalCoefficient quaternionMatrix (1 + A) i k j h +
        generalCoefficient Angular.oppositeMatrix (1 + U) i k j h)) =
      (Matrix.trace (U * U) / 2) * (if l = h then 1 else 0) := by
  simp only [mul_add, Finset.sum_add_distrib]
  have hQP (r s : Fin 3) :
      (∑ i, ∑ k, Angular.oppositeMatrix r i k * quaternionMatrix s i k) = 0 := by
    simpa only [mul_comm] using mixed_twoForm_pairing s r
  have hz (j : Fin 4) := generalCoefficient_pairing_zero _ _ hQP
    U (1 + A) j l j h
  simp_rw [hz]
  simp only [Finset.sum_const_zero, mul_zero, zero_add]
  have hAB : symmetric (Uᵀ * (1 + U)) := by
    rw [transpose_mul_one_add U hs]
    exact symmetric_add_square U hs
  rw [generalCoefficient_ricci Angular.oppositeMatrix opposite_twoForm_pairing
    oppositeMatrix_transpose Angular.oppositeMatrix_anticommutator _ _ hAB,
    transpose_mul_one_add U hs, Matrix.trace_add]
  have htrace : Matrix.trace U = 0 := ht
  rw [htrace]
  ring

theorem generalEinsteinCoefficient_eq_tensor (A U : Mat) (i k j l : Fin 4) :
    generalEinsteinCoefficient A U i k j l =
      Angular.einsteinCurvatureTensor A U i k l j := by
  simp only [generalEinsteinCoefficient, generalCoefficient_eq_blockTensor,
    Angular.einsteinCurvatureTensor, Pi.add_apply]

end
end PositiveEinsteinFour.CurvatureContraction
end


section

/-! Evaluate the derivative-slot Green integral on actual metric tensors,
using the published raw curvature decomposition and Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureIntegralNormedSpace
local instance curvatureIntegralNormedAlgebra_r8e6650_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem generalCoefficient_skew (Q : Fin 3 → Mat4)
    (hQ : ∀ s i j, Q s j i = -Q s i j) (A : Mat) (i k j l : Fin 4) :
    generalCoefficient Q A k i j l = -generalCoefficient Q A i k j l := by
  simp only [generalCoefficient, ← Finset.sum_neg_distrib, ← mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [hQ r i k]
  ring

theorem generalCoefficient_divergence (Q : Fin 3 → Mat4) (Z : Angular.Gradient)
    (hb : ∀ s i, (∑ r, ∑ k, Q r i k * Z k r s) = 0) (i j l : Fin 4) :
    (∑ k, generalCoefficient Q (Z k) i k j l) = 0 := by
  simp only [generalCoefficient, Finset.mul_sum]
  calc
    _ = ∑ s, (1 / 2 : ℝ) * Q s j l * (∑ r, ∑ k, Q r i k * Z k r s) := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ r, ∑ k, ∑ s, (1 / 2 : ℝ) * (Z k r s * Q r i k * Q s j l) :=
          Finset.sum_comm
        _ = ∑ r, ∑ s, ∑ k, (1 / 2 : ℝ) * (Z k r s * Q r i k * Q s j l) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = 0 := by simp only [hb, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual scalar derivatives in the same coordinate connection and frame
flow as the Weyl tensors. The data below contain only parallel differentiation,
Hessian symmetry and the ordinary covector Ricci commutator (Petersen,
Riemannian Geometry, §3.1.1 and Proposition 2.2.8). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace ScalarCovariantData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)} {d : MetricGreenData g μ}
  {a : M → ℝ} (s : ScalarCovariantData d a)

include s

theorem continuousGradientVector : Continuous (scalarGradientVector g a) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi s.continuousGradient)

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar Green formulas obtained by differentiating the invariant frame
integral. All fields are the actual covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace ScalarCovariantData

variable {a b : M → ℝ} (s : ScalarCovariantData d a)

include s

theorem laplacian_square_green :
    (∫ e, scalarLaplacian g a e ^ 2 ∂μ) =
      -(∫ e, ∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e j i i) ∂μ) := by
  have hi (i : Fin 4) := scalar_flow_green (d := d) i s.laplacianField
    (s.laplacianDerivativeField i) (s.gradientField i) (s.hessianField i i)
    (s.derivativeLaplacian i) (s.derivativeGradient i i)
  have hl (i : Fin 4) : Integrable (fun e =>
      (∑ j, scalarThird g a e i j j) * scalarGradient g a e i) μ :=
    ((s.laplacianDerivativeField i).continuous.mul (s.continuousGradient i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : Fin 4) : Integrable (fun e =>
      scalarLaplacian g a e * scalarHessian g a e i i) μ :=
    (s.continuousLaplacian.mul (s.continuousHessian i i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq := congrArg (fun z : Fin 4 → ℝ => ∑ i, z i) (funext hi)
  simp only [laplacianField, laplacianDerivativeField, gradientField, hessianField,
    ContinuousMap.coe_mk, Finset.sum_neg_distrib] at heq
  rw [← integral_finsetSum _ (fun i _ => hl i),
    ← integral_finsetSum _ (fun i _ => hr i)] at heq
  have hrw : (fun e : FrameBundle g => ∑ i, scalarLaplacian g a e * scalarHessian g a e i i) =
      (fun e => scalarLaplacian g a e ^ 2) := by
    funext e
    rw [← Finset.mul_sum]
    exact (pow_two _).symm
  rw [hrw] at heq
  have hlw : (fun e : FrameBundle g => ∑ i, (∑ j, scalarThird g a e i j j) * scalarGradient g a e i) =
      (fun e => ∑ i, scalarGradient g a e i * (∑ j, scalarThird g a e i j j)) := by
    funext e
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hlw] at heq
  linarith only [heq]

theorem hessian_square_green :
    (∫ e, ∑ j, ∑ i, scalarHessian g a e i j ^ 2 ∂μ) =
      -(∫ e, ∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e i i j) ∂μ) := by
  have hi (j : Fin 4) := Averages.weighted_four_direction_green μ
    (fun i => (d.flow i).map) (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    (ContinuousMap.const _ 1) (fun _ => ContinuousMap.const _ 0)
    (s.gradientField j) (fun i => s.hessianField i j) (fun i => s.thirdField i i j)
    (fun i t _ => hasDerivAt_const t 1) (fun i => s.derivativeGradient i j)
    (fun i => s.derivativeHessian i i j)
  simp only [ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul, Finset.sum_const_zero, add_zero,
    gradientField, hessianField, thirdField, ContinuousMap.coe_mk, Real.norm_eq_abs,
    sq_abs, RCLike.inner_apply, conj_trivial, mul_comm] at hi
  have hl (j : Fin 4) : Integrable (fun e => ∑ i, scalarHessian g a e i j ^ 2) μ :=
    (continuous_finsetSum _ (fun i _ => (s.continuousHessian i j).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (j : Fin 4) : Integrable (fun e =>
      scalarGradient g a e j * (∑ i, scalarThird g a e i i j)) μ :=
    ((s.continuousGradient j).mul (continuous_finsetSum _
      (fun i _ => s.continuousThird i i j))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun j _ => hl j)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hr j)]

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar Poisson solvability and covariant differentiation.

Petersen, Riemannian Geometry, third edition author text, §9.1,
Theorem 9.1.2 proof (p.287): the orthogonal image/kernel decomposition
of the Hodge Laplacian. In degree zero on a closed connected manifold,
the kernel is the constants, so every smooth mean-zero function is in
the image. Our Laplacian has the opposite sign, which does not change
its image. The scalar-calculus statement specializes the classical parallel-frame
covariant derivative identities of §3.1.1. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem centered_product_integral (a : C(Ω, ℝ)) :
    (∫ x, a x * (a x - ∫ y, a y ∂μ) ∂μ) =
      ∫ x, (a x - ∫ y, a y ∂μ) ^ 2 ∂μ := by
  let m := ∫ x, a x ∂μ
  have hi : Integrable a μ := a.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (fun x => a x - m) μ := hi.sub (integrable_const m)
  have hs : Integrable (fun x => (a x - m) ^ 2) μ :=
    ((a.continuous.sub continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : (∫ x, a x - m ∂μ) = 0 := by
    rw [integral_sub hi (integrable_const m)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact sub_self m
  have heq (x : Ω) : a x * (a x - m) = (a x - m) ^ 2 + m * (a x - m) := by ring
  change (∫ x, a x * (a x - m) ∂μ) = ∫ x, (a x - m) ^ 2 ∂μ
  simp_rw [heq]
  rw [integral_add hs (hd.const_mul m), integral_const_mul, hz, mul_zero, add_zero]

end PositiveEinsteinFour.Variance
end


section

/-! The small classical smooth-bundle input needed to use scalar Poisson
solutions on one oriented frame component. Smoothness of the squared norm
and invariance under oriented orthonormal frames are the ordinary metric
bundle calculus of Petersen §2.2 and §3.1.1. The scalar gradient identities
below are derived from parallel differentiation; no variance estimate is
included in the input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

omit [IsManifold I4 ∞ M] in
theorem orientedNormRegularization_smooth {b : M → ℝ}
    (hb : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => b c ^ 2)) {ε : ℝ} (hε : 0 < ε) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (orientedNormRegularization b ε) := by
  intro c
  have h : ContMDiffAt I4 𝓘(ℝ, ℝ) ∞ (fun c => b c ^ 2 + ε ^ 2) c :=
    (hb.add contMDiff_const).contMDiffAt
  have hp : 0 < b c ^ 2 + ε ^ 2 := by
    nlinarith [sq_nonneg (b c), sq_pos_of_pos hε]
  exact (Real.contDiffAt_sqrt (ne_of_gt hp)).comp_contMDiffAt
    (f := fun c : M => b c ^ 2 + ε ^ 2) h

theorem regularizedRadialDerivative_scale (ε : ℝ) (A Z : Mat) :
    regularizedRadialDerivative ε A Z =
      (normalizedBlockNorm A / regularizedBlockNorm ε A) *
        regularizedRadialDerivative 0 A Z := by
  by_cases ha : normalizedBlockNorm A = 0
  · have hA := (normalizedBlockNorm_eq_zero_iff A).mp ha
    subst A
    simp [regularizedRadialDerivative]
  · unfold regularizedRadialDerivative
    rw [regularizedBlockNorm_zero]
    field_simp

namespace PetersenOrientedNormInput

variable {orientation : FrameOrientation g} (h : PetersenOrientedNormInput orientation)
  {d : MetricGreenData g μ}

include h

theorem plus_regularized_gradient (hflow : OrientationPreservingFlow d orientation)
    {ε : ℝ} (hε : 0 < ε)
    (s : ScalarCovariantData d (orientedNormRegularization (plusNorm orientation) ε))
    (e : FrameBundle g) (he : e ∈ orientation.positive) (i : Fin 4) :
    scalarGradient g (orientedNormRegularization (plusNorm orientation) ε) e i =
      regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) := by
  apply scalarGradient_eq_of_frame_derivative s orientation hflow
    (fun e => regularizedBlockNorm ε (plusWeyl g e.base e.frame))
    (fun i e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i))
  · intro f hf
    unfold orientedNormRegularization regularizedBlockNorm
    rw [h.plusFrame f hf]
  · intro j t f
    exact hasDerivAt_regularizedBlockNorm (d.derivativeWeyl j t f)
      (fun r => d.weyl.symmetric ((d.flow j).map r f)) hε
  · exact he

end PetersenOrientedNormInput

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrated scalar Bochner identity derived from the actual Ricci
commutator and the frame-flow Green formulas. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem traceFree_four_square (H : Mat4) :
    (∑ i, ∑ j, (H i j - if i = j then Matrix.trace H / 4 else 0) ^ 2) =
      (∑ i, ∑ j, H i j ^ 2) - Matrix.trace H ^ 2 / 4 := by
  norm_num [Fin.sum_univ_four, Matrix.trace, Matrix.diag]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}
  {a : M → ℝ} (s : ScalarCovariantData d a)

include s

omit s in
theorem scalarTraceFreeHessian_square (e : FrameBundle g) :
    (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) =
      (∑ j, ∑ i, scalarHessian g a e i j ^ 2) - scalarLaplacian g a e ^ 2 / 4 := by
  calc
    _ = (∑ i, ∑ j, scalarHessian g a e i j ^ 2) - scalarLaplacian g a e ^ 2 / 4 := by
      simpa only [scalarTraceFreeHessian, scalarLaplacian, Matrix.trace, Matrix.diag]
        using traceFree_four_square (fun i j => scalarHessian g a e i j)
    _ = _ := by rw [Finset.sum_comm]

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem ScalarCovariantData.integrated_bochner :
    (∫ e, scalarLaplacian g a e ^ 2 ∂μ) =
      4 * (∫ e, ‖scalarGradientVector g a e‖ ^ 2 ∂μ) +
        (4 / 3 : ℝ) * ∫ e, ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 ∂μ := by
  have hH := s.hessian_square_green
  have hL := s.laplacian_square_green
  have hpoint (e : FrameBundle g) :
      (∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e i i j)) =
        (∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e j i i)) +
          3 * ‖scalarGradientVector g a e‖ ^ 2 := by
    simp_rw [s.laplacianGradient_commute, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j, scalarGradient g a e j * (3 * scalarGradient g a e j)) =
      3 * ∑ j, scalarGradient g a e j ^ 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hgrad : Integrable (fun e => ‖scalarGradientVector g a e‖ ^ 2) μ :=
    (s.continuousGradientVector.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm : Integrable (fun e =>
      ∑ j, scalarGradient g a e j * (∑ i, scalarThird g a e j i i)) μ :=
    (continuous_finsetSum _ (fun j _ => (s.continuousGradient j).mul
      (continuous_finsetSum _ (fun i _ => s.continuousThird j i i)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hhess : Integrable (fun e => ∑ j, ∑ i, scalarHessian g a e i j ^ 2) μ :=
    (continuous_finsetSum _ (fun j _ => continuous_finsetSum _
      (fun i _ => (s.continuousHessian i j).pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hlap : Integrable (fun e => scalarLaplacian g a e ^ 2) μ :=
    (s.continuousLaplacian.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [hpoint] at hH
  rw [integral_add hterm (hgrad.const_mul 3), integral_const_mul] at hH
  have htf : (∫ e, ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 ∂μ) =
      (∫ e, ∑ j, ∑ i, scalarHessian g a e i j ^ 2 ∂μ) -
        (∫ e, scalarLaplacian g a e ^ 2 ∂μ) / 4 := by
    simp_rw [scalarTraceFreeHessian_square]
    rw [integral_sub hhess (hlap.div_const 4), integral_div]
  linarith only [hH, hL, htf]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The nine commuting-quaternion products are an actual orthogonal
basis for symmetric trace-free scalar Hessians in four dimensions. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

private theorem coefficients_pairing_row_zero (S : Matrix4) (j : Fin 3) :
    coefficients S 0 j = scalarPairing (mixingCoefficient 0 j) S / 4 := by
  fin_cases j <;>
    norm_num [coefficients, rightQuaternionCoefficients, scalarPairing,
      mixingCoefficient_eq_table, coefficientTable, Fin.sum_univ_four] <;> ring

private theorem coefficients_pairing_row_one (S : Matrix4) (j : Fin 3) :
    coefficients S 1 j = scalarPairing (mixingCoefficient 1 j) S / 4 := by
  fin_cases j <;>
    norm_num [coefficients, rightQuaternionCoefficients, scalarPairing,
      mixingCoefficient_eq_table, coefficientTable, Fin.sum_univ_four] <;> ring

private theorem coefficients_pairing_row_two (S : Matrix4) (j : Fin 3) :
    coefficients S 2 j = scalarPairing (mixingCoefficient 2 j) S / 4 := by
  fin_cases j <;>
    norm_num [coefficients, rightQuaternionCoefficients, scalarPairing,
      mixingCoefficient_eq_table, coefficientTable, Fin.sum_univ_four] <;> ring

theorem coefficients_pairing (S : Matrix4) (i j : Fin 3) :
    coefficients S i j = scalarPairing (mixingCoefficient i j) S / 4 := by
  fin_cases i
  · exact coefficients_pairing_row_zero S j
  · exact coefficients_pairing_row_one S j
  · exact coefficients_pairing_row_two S j

theorem reconstruct_apply (C : Mat) (a b : Fin 4) :
    reconstruct C a b = ∑ i, ∑ j, C i j * mixingCoefficient i j a b := by
  simp only [reconstruct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

private theorem reconstruct_entry_zero (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 0 b =
      (S 0 b + S b 0) / 2 - (if (0 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

private theorem reconstruct_entry_one (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 1 b =
      (S 1 b + S b 1) / 2 - (if (1 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

private theorem reconstruct_entry_two (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 2 b =
      (S 2 b + S b 2) / 2 - (if (2 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

private theorem reconstruct_entry_three (S : Matrix4) (b : Fin 4) :
    reconstruct (coefficients S) 3 b =
      (S 3 b + S b 3) / 2 - (if (3 : Fin 4) = b then Matrix.trace S / 4 else 0) := by
  fin_cases b <;>
    norm_num [reconstruct_apply, coefficients, rightQuaternionCoefficients,
      mixingCoefficient_eq_table, coefficientTable, Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Fin.sum_univ_four] <;> ring

theorem reconstruct_entry (S : Matrix4) (a b : Fin 4) :
    reconstruct (coefficients S) a b =
      (S a b + S b a) / 2 - (if a = b then Matrix.trace S / 4 else 0) := by
  fin_cases a
  · exact reconstruct_entry_zero S b
  · exact reconstruct_entry_one S b
  · exact reconstruct_entry_two S b
  · exact reconstruct_entry_three S b

theorem reconstruct_coefficients (S : Matrix4) (hs : Sᵀ = S) (ht : Matrix.trace S = 0) :
    reconstruct (coefficients S) = S := by
  ext a b
  rw [reconstruct_entry, ht]
  have hab : S b a = S a b := congrArg (fun M : Matrix4 => M a b) hs
  rw [hab]
  split_ifs <;> ring

theorem scalarPairing_comm (S T : Matrix4) : scalarPairing S T = scalarPairing T S := by
  simp only [scalarPairing, mul_comm]

theorem scalarPairing_sum_left {ι : Type*} [Fintype ι] (f : ι → Matrix4) (T : Matrix4) :
    scalarPairing (∑ i, f i) T = ∑ i, scalarPairing (f i) T := by
  simp only [scalarPairing, Matrix.sum_apply, Finset.sum_mul]
  calc
    _ = ∑ a, ∑ i, ∑ b, f i a b * T a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem scalarPairing_smul_left (r : ℝ) (S T : Matrix4) :
    scalarPairing (r • S) T = r * scalarPairing S T := by
  simp only [scalarPairing, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem scalarPairing_reconstruct (C : Mat) (S : Matrix4) :
    scalarPairing (reconstruct C) S = 4 * ∑ i, ∑ j, C i j * coefficients S i j := by
  simp only [reconstruct, scalarPairing_sum_left, scalarPairing_smul_left, coefficients_pairing,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Parseval's identity in the nine actual quaternion product directions. -/
theorem scalarPairing_coefficients (S T : Matrix4)
    (hs : Sᵀ = S) (ht : Matrix.trace S = 0) :
    scalarPairing S T = 4 * ∑ i, ∑ j, coefficients S i j * coefficients T i j := by
  conv_lhs => rw [← reconstruct_coefficients S hs ht]
  exact scalarPairing_reconstruct _ _

theorem scalarNormSq_coefficients (S : Matrix4) (hs : Sᵀ = S) (ht : Matrix.trace S = 0) :
    scalarNormSq S = 4 * ∑ i, ∑ j, coefficients S i j ^ 2 := by
  simpa only [scalarNormSq, pow_two] using scalarPairing_coefficients S S hs ht

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! Actual scalar-Hessian Weyl operators, on the nine quaternion-product
coordinates. Only the algebra needed by the weighted variance is used. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian CurvatureContraction

noncomputable section

theorem clifford_triple (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4)) (r i s : Fin 3) :
    Q r * Q i * Q s + Q s * Q i * Q r =
      (2 : ℝ) • ((if r = s then Q i else 0) -
        (if r = i then Q s else 0) - (if i = s then Q r else 0)) := by
  calc
    _ = (Q r * Q i + Q i * Q r) * Q s -
        Q i * (Q r * Q s + Q s * Q r) +
        (Q i * Q s + Q s * Q i) * Q r := by noncomm_ring
    _ = _ := by
      rw [hQ, hQ, hQ]
      split_ifs <;>
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          zero_smul, zero_mul, mul_zero]
      all_goals module

private theorem folded_clifford_triple (Q : Fin 3 → Matrix4) (A : Mat) (i : Fin 3) :
    (∑ r, ∑ s, A r s • ((if r = s then Q i else 0) -
      (if r = i then Q s else 0) - (if i = s then Q r else 0))) =
      Matrix.trace A • Q i - (∑ s, A i s • Q s) - ∑ r, A r i • Q r := by
  fin_cases i <;> ext a b <;>
    simp [Fin.sum_univ_three, Matrix.trace, Matrix.diag, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] <;> ring

theorem weighted_clifford_sandwich (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (i : Fin 3) :
    (∑ r, ∑ s, A r s • (Q r * Q i * Q s)) =
      (-2 : ℝ) • ∑ r, A r i • Q r := by
  let G : Matrix4 := ∑ r, ∑ s, A r s • (Q r * Q i * Q s)
  have hrev : G = ∑ r, ∑ s, A r s • (Q s * Q i * Q r) := by
    dsimp only [G]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    rw [hs s r]
  have hadd : G + G =
      (2 : ℝ) • (Matrix.trace A • Q i - (∑ s, A i s • Q s) - ∑ r, A r i • Q r) := by
    conv_lhs => rhs; rw [hrev]
    dsimp only [G]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, ← smul_add, clifford_triple Q hQ]
    simp only [smul_comm _ (2 : ℝ), ← Finset.smul_sum]
    rw [folded_clifford_triple]
  have hrow : (∑ s, A i s • Q s) = ∑ r, A r i • Q r := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hs i r]
  have htrace : Matrix.trace A = 0 := ht
  rw [hrow, htrace, zero_smul] at hadd
  change G = _
  apply (smul_right_injective (R := ℝ) (M := Matrix4) (by norm_num : (2 : ℝ) ≠ 0))
  calc
    (2 : ℝ) • G = G + G := by module
    _ = (2 : ℝ) • (0 - (∑ r, A r i • Q r) - ∑ r, A r i • Q r) := hadd
    _ = _ := by module

private theorem blockAction_product (Q P : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (hcomm : ∀ r s, P r * Q s = Q s * P r)
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (i j : Fin 3) :
    blockAction Q A (-(Q i * P j)) = ∑ r, A r i • (-(Q r * P j)) := by
  have hterm (r s : Fin 3) : Q r * (-(Q i * P j)) * Q s = -(Q r * Q i * Q s) * P j := by
    calc
      _ = -(Q r * Q i * (P j * Q s)) := by noncomm_ring
      _ = _ := by rw [hcomm]; noncomm_ring
  unfold blockAction blockActionLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, hterm]
  have hid : (∑ r, ∑ s, A r s • (-(Q r * Q i * Q s) * P j)) =
      -(∑ r, ∑ s, A r s • (Q r * Q i * Q s)) * P j := by
    simp only [Matrix.sum_mul, Matrix.smul_mul, neg_mul, smul_neg,
      Finset.sum_neg_distrib]
  rw [hid, weighted_clifford_sandwich Q hQ A hs ht i]
  have hscalar : -((-2 : ℝ) • (∑ r, A r i • Q r)) =
      (2 : ℝ) • (∑ r, A r i • Q r) := by module
  rw [hscalar, Matrix.smul_mul, smul_smul]
  norm_num
  simp only [Matrix.sum_mul, Matrix.smul_mul]

theorem plusAction_basis (A : Mat) (hs : symmetric A) (ht : traceFree A) (i j : Fin 3) :
    blockAction quaternionMatrix A (mixingCoefficient i j) =
      ∑ r, A r i • mixingCoefficient r j := by
  simpa only [mixingCoefficient, quaternionMatrix_transpose, Matrix.neg_mul] using
    blockAction_product quaternionMatrix oppositeMatrix quaternionMatrix_anticommutator
      oppositeMatrix_commute A hs ht i j

theorem minusAction_basis (U : Mat) (hs : symmetric U) (ht : traceFree U) (i j : Fin 3) :
    blockAction oppositeMatrix U (mixingCoefficient i j) =
      ∑ s, U s j • mixingCoefficient i s := by
  have hc (r s : Fin 3) : quaternionMatrix r * oppositeMatrix s =
      oppositeMatrix s * quaternionMatrix r := (oppositeMatrix_commute s r).symm
  have h := blockAction_product oppositeMatrix quaternionMatrix oppositeMatrix_anticommutator
    hc U hs ht j i
  simpa only [mixingCoefficient, quaternionMatrix_transpose, Matrix.neg_mul,
    oppositeMatrix_commute] using h

theorem blockAction_reconstruct (Q : Fin 3 → Matrix4) (A C : Mat) :
    blockAction Q A (reconstruct C) =
      ∑ i, ∑ j, C i j • blockAction Q A (mixingCoefficient i j) := by
  simp only [reconstruct, blockAction, map_sum, map_smul]

theorem basis_pairing (S : Matrix4) (i j : Fin 3) :
    scalarPairing (mixingCoefficient i j) S = 4 * coefficients S i j := by
  rw [coefficients_pairing]
  ring

/-- The plus operator is the ordinary coefficient-matrix quadratic form
on the columns of the nine-product expansion. -/
theorem plusAction_pairing (A : Mat) (hA : symmetric A) (htA : traceFree A)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    scalarPairing (blockAction quaternionMatrix A S) S =
      4 * ∑ j, ∑ r, ∑ s, A r s * coefficients S r j * coefficients S s j := by
  have haction : blockAction quaternionMatrix A S =
      ∑ i, ∑ j, coefficients S i j • (∑ r, A r i • mixingCoefficient r j) := by
    calc
      _ = blockAction quaternionMatrix A (reconstruct (coefficients S)) := by
        rw [reconstruct_coefficients S hS htS]
      _ = _ := by rw [blockAction_reconstruct]; simp_rw [plusAction_basis A hA htA]
  rw [haction]
  simp only [scalarPairing_sum_left, scalarPairing_smul_left, basis_pairing]
  simp only [Fin.sum_univ_three]
  ring

/-- The minus operator acts on the rows of the same expansion. -/
theorem minusAction_pairing (U : Mat) (hU : symmetric U) (htU : traceFree U)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    scalarPairing (blockAction oppositeMatrix U S) S =
      4 * ∑ i, ∑ r, ∑ s, U r s * coefficients S i r * coefficients S i s := by
  have haction : blockAction oppositeMatrix U S =
      ∑ i, ∑ j, coefficients S i j • (∑ s, U s j • mixingCoefficient i s) := by
    calc
      _ = blockAction oppositeMatrix U (reconstruct (coefficients S)) := by
        rw [reconstruct_coefficients S hS htS]
      _ = _ := by rw [blockAction_reconstruct]; simp_rw [minusAction_basis U hU htU]
  rw [haction]
  simp only [scalarPairing_sum_left, scalarPairing_smul_left, basis_pairing]
  simp only [Fin.sum_univ_three]
  ring

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The scalar-Hessian curvature contraction in the weighted-variance
argument, with the actual Einstein curvature tensor and arbitrary
symmetric trace-free Weyl matrices. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Bianchi Angular CurvatureContraction
open PositiveEinsteinFour.Geometry

noncomputable section

private theorem sum_five_permute (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ k, ∑ j, ∑ l, ∑ h, f i k j l h) =
      ∑ l, ∑ h, ∑ j, ∑ i, ∑ k, f i k j l h := by
  let e : (((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) × Fin 4) ≃
      ((Fin 4 × Fin 4) × (Fin 4 × (Fin 4 × Fin 4))) :=
    { toFun := fun x => ((x.1.2.2, x.2), (x.1.2.1, (x.1.1.1, x.1.1.2)))
      invFun := fun y => (((y.2.2.1, y.2.2.2), (y.2.1, y.1.1)), y.1.2)
      left_inv := by rintro ⟨⟨⟨i, k⟩, ⟨j, l⟩⟩, h⟩; rfl
      right_inv := by rintro ⟨⟨l, h⟩, ⟨j, ⟨i, k⟩⟩⟩; rfl }
  have he := e.sum_comp (fun y => f y.2.2.1 y.2.2.2 y.2.1 y.1.1 y.1.2)
  change (∑ x : ((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) × Fin 4,
      f x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2) =
    ∑ y : (Fin 4 × Fin 4) × (Fin 4 × (Fin 4 × Fin 4)),
      f y.2.2.1 y.2.2.2 y.2.1 y.1.1 y.1.2 at he
  simpa only [Fintype.sum_prod_type] using he

/-- The curvature term in the tuple-indexed Green identity is exactly the
contraction above; this is only reindexing, with no tensor hypothesis. -/
theorem scalarCurvatureContraction_tuple (A U : Mat) (p : Vec) :
    (1 / 2 : ℝ) * ∑ q : (Fin 4 × Fin 4) × (Fin 4 × Fin 4),
      (generalCoefficient quaternionMatrix A q.1.1 q.1.2 q.2.1 q.2.2 +
        generalCoefficient oppositeMatrix U q.1.1 q.1.2 q.2.1 q.2.2) *
        (∑ h, generalEinsteinCoefficient A U q.1.1 q.1.2 q.2.1 h * p h) * p q.2.2 =
      scalarCurvatureContraction A U p := by
  unfold scalarCurvatureContraction
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact sum_five_permute _

theorem scalarCurvatureContraction_eq (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (p : Vec) :
    scalarCurvatureContraction A U p =
      3 * (normalizedBlockNorm A ^ 2 + normalizedBlockNorm U ^ 2) * ‖p‖ ^ 2 := by
  have hpoint (l h : Fin 4) :
      (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
        (generalCoefficient quaternionMatrix A i k j l +
          generalCoefficient oppositeMatrix U i k j l) *
          generalEinsteinCoefficient A U i k j h) =
      ((Matrix.trace (A * A) + Matrix.trace (U * U)) / 2) *
        (if l = h then 1 else 0) := by
    have hp : (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
        generalCoefficient quaternionMatrix A i k j l * generalEinsteinCoefficient A U i k j h) =
      (Matrix.trace (A * A) / 2) * (if l = h then 1 else 0) :=
      plus_generalCoefficient_ricci A U hA htA l h
    have hm : (1 / 2 : ℝ) * (∑ j, ∑ i, ∑ k,
        generalCoefficient oppositeMatrix U i k j l * generalEinsteinCoefficient A U i k j h) =
      (Matrix.trace (U * U) / 2) * (if l = h then 1 else 0) :=
      minus_generalCoefficient_ricci A U hU htU l h
    simp only [add_mul, Finset.sum_add_distrib, mul_add]
    rw [hp, hm]
    ring
  unfold scalarCurvatureContraction
  simp_rw [hpoint]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
  have hAn := trace_square_eq_six_norm_sq A hA
  have hUn := trace_square_eq_six_norm_sq U hU
  rw [← pow_two] at hAn hUn
  rw [hAn, hUn]
  ring

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! Shifted positive Weyl coefficients give an upper bound on the scalar trace-free Hessian, using its actual nine real coefficients. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

theorem coefficientQuadratic_nonneg (A : Mat) (hA : A.PosSemidef) (c : Fin 3 → ℝ) :
    0 ≤ coefficientQuadratic A c := by
  have h := hA.dotProduct_mulVec_nonneg c
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold coefficientQuadratic
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem coefficientQuadratic_cross_identity (A : Mat) (hA : symmetric A)
    (ht : traceFree A) (x : ℝ) (c : Fin 3 → ℝ) :
    (∑ t, coefficientQuadratic (A + x • (1 : Mat)) (crossVector t c)) =
      2 * x * (∑ r, c r ^ 2) - coefficientQuadratic A c := by
  have htrace : A 0 0 + A 1 1 + A 2 2 = 0 := by
    simpa only [traceFree, Matrix.trace, Matrix.diag, Fin.sum_univ_three] using ht
  norm_num [coefficientQuadratic, crossVector, Fin.sum_univ_three,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    hA 1 0, hA 2 0, hA 2 1]
  linear_combination (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * htrace

/-- The upper eigenvalue bound follows directly from shifted positivity,
with no spectral frame. -/
theorem coefficientQuadratic_le_two_shift (A : Mat) (hA : symmetric A)
    (ht : traceFree A) (x : ℝ) (hx : (A + x • (1 : Mat)).PosSemidef)
    (c : Fin 3 → ℝ) :
    coefficientQuadratic A c ≤ 2 * x * ∑ r, c r ^ 2 := by
  have hn : 0 ≤ ∑ t, coefficientQuadratic (A + x • (1 : Mat)) (crossVector t c) :=
    Finset.sum_nonneg fun t _ => coefficientQuadratic_nonneg _ hx _
  rw [coefficientQuadratic_cross_identity A hA ht x c] at hn
  linarith only [hn]

theorem columnGram_le_two_shift (A C : Mat) (hA : symmetric A) (ht : traceFree A)
    (x : ℝ) (hx : (A + x • (1 : Mat)).PosSemidef) :
    columnGram A C ≤ 2 * x * ∑ i, ∑ j, C i j ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    coefficientQuadratic_le_two_shift A hA ht x hx (fun i => C i j)
  change columnGram A C ≤ _ at h
  rw [← Finset.mul_sum, Finset.sum_comm] at h
  exact h

theorem rowGram_le_two_shift (A C : Mat) (hA : symmetric A) (ht : traceFree A)
    (x : ℝ) (hx : (A + x • (1 : Mat)).PosSemidef) :
    rowGram A C ≤ 2 * x * ∑ i, ∑ j, C i j ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    coefficientQuadratic_le_two_shift A hA ht x hx (fun j => C i j)
  change rowGram A C ≤ _ at h
  rwa [← Finset.mul_sum] at h

/-- The sharp scalar-Hessian operator bound for arbitrary
symmetric Weyl matrices and their actual shifted positive forms. -/
theorem scalarHessian_operator_bound (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    scalarPairing (blockAction quaternionMatrix A S) S +
      scalarPairing (blockAction oppositeMatrix U S) S ≤ 4 * scalarNormSq S := by
  have hp := columnGram_le_two_shift A (coefficients S) hA htA x hAx
  have hm := rowGram_le_two_shift U (coefficients S) hU htU y hUy
  have hN : 0 ≤ ∑ i, ∑ j, coefficients S i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [plusAction_pairing A hA htA S hS htS, minusAction_pairing U hU htU S hS htS,
    scalarNormSq_coefficients S hS htS]
  change 4 * columnGram A (coefficients S) + 4 * rowGram U (coefficients S) ≤ _
  have hsum : 2 * (x + y) * (∑ i, ∑ j, coefficients S i j ^ 2) ≤
      4 * (∑ i, ∑ j, coefficients S i j ^ 2) := by
    exact mul_le_mul_of_nonneg_right (by linarith only [hxy]) hN
  nlinarith only [hp, hm, hsum]

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! Identify the scalar-Hessian matrix operator with the actual
four-index curvature coefficient used in integration by parts. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular CurvatureContraction

noncomputable section

private theorem sum_four_swap {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  have h := (Equiv.prodComm (α × β) (γ × δ)).sum_comp
    (fun p : (γ × δ) × (α × β) => f p.2.1 p.2.2 p.1.1 p.1.2)
  simpa only [Fintype.sum_prod_type, Equiv.prodComm_apply, Prod.swap_prod_mk] using h

theorem blockAction_entry (Q : Fin 3 → Matrix4)
    (hQ : ∀ r, (Q r)ᵀ = -Q r) (A : Mat) (S : Matrix4) (i j : Fin 4) :
    blockAction Q A S i j =
      ∑ k, ∑ l, generalCoefficient Q A i k j l * S k l := by
  have hskew (r : Fin 3) (a b : Fin 4) : Q r a b = -Q r b a := by
    have h := congrArg (fun M : Matrix4 => M b a) (hQ r)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  have hmul (r s : Fin 3) : (Q r * S * Q s) i j =
      -(∑ k, ∑ l, Q r i k * Q s j l * S k l) := by
    calc
      _ = ∑ k, ∑ l, Q r i k * S k l * Q s l j := by
        simp only [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_comm
      _ = ∑ k, ∑ l, -(Q r i k * Q s j l * S k l) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        rw [hskew s l j]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  change (-(1 / 2 : ℝ) • ∑ r, ∑ s, A r s • (Q r * S * Q s)) i j = _
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hmul,
    mul_neg, Finset.sum_neg_distrib, neg_mul, neg_neg]
  calc
    _ = (1 / 2 : ℝ) * ∑ r, ∑ s, ∑ k, ∑ l, A r s * Q r i k * Q s j l * S k l := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = (1 / 2 : ℝ) * ∑ k, ∑ l, ∑ r, ∑ s, A r s * Q r i k * Q s j l * S k l := by
      rw [sum_four_swap]
    _ = _ := by
      simp only [generalCoefficient, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem blockQuadratic_eq_pairing (Q : Fin 3 → Matrix4)
    (hQ : ∀ r, (Q r)ᵀ = -Q r) (A : Mat) (S : Matrix4) :
    blockQuadratic Q A S = scalarPairing (blockAction Q A S) S := by
  symm
  unfold scalarPairing
  simp_rw [blockAction_entry Q hQ, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, (generalCoefficient Q A i k j l * S k l) * S i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      unfold blockQuadratic
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem scalarHessian_coefficient_bound (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (S : Matrix4) (hS : Sᵀ = S) (htS : Matrix.trace S = 0) :
    blockQuadratic quaternionMatrix A S + blockQuadratic oppositeMatrix U S ≤
      4 * scalarNormSq S := by
  rw [blockQuadratic_eq_pairing quaternionMatrix quaternionMatrix_transpose,
    blockQuadratic_eq_pairing oppositeMatrix QuaternionFrame.oppositeMatrix_transpose]
  exact scalarHessian_operator_bound A U hA hU htA htU x y hAx hUy hxy S hS htS

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! The integrated scalar-Hessian curvature identity. The only
differential inputs are the raw scalar and Weyl parallel-frame derivatives
and Ricci commutator. Coefficient divergence and the exact contraction are
proved from the Bianchi equation and the finite-dimensional calculations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Bianchi CurvatureContraction ScalarHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarIdentityRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarIdentitySpace
local instance scalarIdentityAlgebra_r8e6650_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem scalar_block_quadratic_tuple (A U : Mat) (H : Mat4) :
    (∑ p : Averages.CurvatureIndex,
      (generalCoefficient quaternionMatrix A p.1.1 p.1.2 p.2.1 p.2.2 +
        generalCoefficient Angular.oppositeMatrix U p.1.1 p.1.2 p.2.1 p.2.2) *
          (H p.1.2 p.2.2 * H p.1.1 p.2.1)) =
      blockQuadratic quaternionMatrix A H + blockQuadratic Angular.oppositeMatrix U H := by
  simp only [blockQuadratic, Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib,
    mul_assoc, mul_comm, mul_left_comm]

theorem scalar_curvature_contraction_commuted (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (p : Bianchi.Vec) :
    (1 / 2 : ℝ) * (∑ q : Averages.CurvatureIndex,
      (generalCoefficient quaternionMatrix A q.1.1 q.1.2 q.2.1 q.2.2 +
        generalCoefficient Angular.oppositeMatrix U q.1.1 q.1.2 q.2.1 q.2.2) *
          (p q.2.2 * ∑ l, generalEinsteinCoefficient A U q.1.1 q.1.2 q.2.1 l * p l)) =
      3 * (normalizedBlockNorm A ^ 2 + normalizedBlockNorm U ^ 2) * ‖p‖ ^ 2 := by
  have h := scalarCurvatureContraction_tuple A U p
  rw [scalarCurvatureContraction_eq A U hA hU htA htU p] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
  {a : M → ℝ}

omit [CompactSpace (FrameBundle g)] in
theorem scalarGradientVector_apply (e : FrameBundle g) (i : Fin 4) :
    scalarGradientVector g a e i = scalarGradient g a e i := rfl

theorem ScalarCovariantData.curvature_identity (s : ScalarCovariantData d a)
    (o : OppositeWeylData d)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)) :
    (∫ e, scalarWeylHessianForm g a e ∂μ) =
      3 * ∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
        normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) *
          ‖scalarGradientVector g a e‖ ^ 2 ∂μ := by
  let C (p : Averages.CurvatureIndex) : C(FrameBundle g, ℝ) :=
    ⟨fun e => generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2,
      ((generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        d.continuousWeyl).add
        ((generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
          o.continuousWeyl)⟩
  let D (p : Averages.CurvatureIndex) : C(FrameBundle g, ℝ) :=
    ⟨fun e => generalCoefficient quaternionMatrix (plusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2,
      ((generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
        (d.continuousGradient p.1.2)).add
        ((generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).continuous.comp
          (o.continuousGradient p.1.2))⟩
  have hC (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      C p e = generalCoefficient quaternionMatrix (plusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeyl g e.base e.frame)
        p.1.1 p.1.2 p.2.1 p.2.2 := rfl
  have hD (p : Averages.CurvatureIndex) (e : FrameBundle g) :
      D p e = generalCoefficient quaternionMatrix (plusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2 +
      generalCoefficient Angular.oppositeMatrix (minusWeylGradient g e.base e.frame p.1.2)
        p.1.1 p.1.2 p.2.1 p.2.2 := rfl
  have hc : ∀ i j l e, (∑ k, D ((i,k),(j,l)) e) = 0 := by
    intro i j l e
    simp only [hD, Finset.sum_add_distrib]
    rw [generalCoefficient_divergence quaternionMatrix _ (d.gradientBianchi e),
      generalCoefficient_divergence Angular.oppositeMatrix _ (o.gradientBianchi e)]
    exact add_zero 0
  have hminus (r : Fin 3) (i j : Fin 4) :
      Angular.oppositeMatrix r j i = -Angular.oppositeMatrix r i j := by
    exact congrArg (fun A : Mat4 => A i j) (QuaternionFrame.oppositeMatrix_transpose r)
  have hs : ∀ i k j l e, C ((k,i),(j,l)) e = -C ((i,k),(j,l)) e := by
    intro i k j l e
    simp only [hC]
    rw [generalCoefficient_skew quaternionMatrix (fun r i j => quaternionMatrix_skew r j i),
      generalCoefficient_skew Angular.oppositeMatrix hminus]
    ring
  have hd (p : Averages.CurvatureIndex) (t : ℝ) (e : FrameBundle g) :
      HasDerivAt (fun r => C p ((d.flow p.1.2).map r e))
        (D p ((d.flow p.1.2).map t e)) t :=
    ((generalCoefficientMap quaternionMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
      (d.derivativeWeyl p.1.2 t e)).add
      ((generalCoefficientMap Angular.oppositeMatrix p.1.1 p.1.2 p.2.1 p.2.2).hasFDerivAt.comp_hasDerivAt t
        (o.derivativeWeyl p.1.2 t e))
  have hg := Averages.weighted_curvature_green μ (fun i => (d.flow i).map)
    (fun i => (d.flow i).continuous) (fun i => (d.flow i).preserves)
    (ContinuousMap.const _ 1) (fun _ => ContinuousMap.const _ 0) C D
    s.gradientField s.hessianField s.thirdField hc hs
    (fun _ t _ => hasDerivAt_const t 1) hd s.derivativeGradient s.derivativeHessian
  have hR (e : FrameBundle g) (i k j l : Fin 4) :
      frameCurvature g e.base e.frame i k l j =
        generalEinsteinCoefficient (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) i k j l := by
    rw [generalEinsteinCoefficient_eq_tensor, hdecomp e]
  simp only [ScalarCovariantData.gradientField, ScalarCovariantData.hessianField,
    ScalarCovariantData.thirdField, ContinuousMap.coe_mk, ContinuousMap.coe_const,
    Function.const_apply, one_mul, zero_mul, add_zero, RCLike.inner_apply,
    conj_trivial, s.commutator, hR] at hg
  rw [← integral_const_mul] at hg
  have hleft (e : FrameBundle g) :
      (∑ p : Averages.CurvatureIndex,
        C p e * (scalarHessian g a e p.1.2 p.2.2 * scalarHessian g a e p.1.1 p.2.1)) =
      scalarWeylHessianForm g a e := by
    simpa only [scalarWeylHessianForm, hC] using
      scalar_block_quadratic_tuple (plusWeyl g e.base e.frame)
        (minusWeyl g e.base e.frame) (scalarHessian g a e)
  simp_rw [hleft] at hg
  rw [hg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  have hpoint := scalar_curvature_contraction_commuted
    (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
    (d.weyl.symmetric e) (o.symmetric e) (d.weyl.traceFree e) (o.traceFree e)
    (scalarGradientVector g a e)
  simpa only [hC, scalarGradientVector_apply, mul_assoc] using hpoint

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Weyl operators annihilate the metric trace.  This identifies
actual Hessian contractions with their trace-free parts. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular CurvatureContraction

noncomputable section

theorem weighted_clifford_product_zero (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) :
    (∑ r, ∑ s, A r s • (Q r * Q s)) = 0 := by
  let W : Matrix4 := ∑ r, ∑ s, A r s • (Q r * Q s)
  have hrev : W = ∑ r, ∑ s, A r s • (Q s * Q r) := by
    dsimp only [W]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    rw [hs s r]
  have hadd : W + W = (-2 * Matrix.trace A) • (1 : Matrix4) := by
    conv_lhs => rhs; rw [hrev]
    dsimp only [W]
    rw [← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, ← smul_add, hQ]
    norm_num [Fin.sum_univ_three, Matrix.trace, Matrix.diag, smul_smul]
    module
  rw [show Matrix.trace A = 0 from ht, mul_zero, zero_smul] at hadd
  have htwo : (2 : ℝ) • W = 0 := by simpa only [two_smul] using hadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem blockAction_one (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) :
    blockAction Q A (1 : Matrix4) = 0 := by
  change -(1 / 2 : ℝ) • (∑ r, ∑ s, A r s • (Q r * 1 * Q s)) = 0
  simp only [Matrix.mul_one, weighted_clifford_product_zero Q hQ A hs ht, smul_zero]

theorem blockAction_trace (Q : Fin 3 → Matrix4)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (S : Matrix4) :
    Matrix.trace (blockAction Q A S) = 0 := by
  have hrev : (∑ r, ∑ s, A r s • (Q s * Q r)) = 0 := by
    calc
      _ = ∑ s, ∑ r, A r s • (Q s * Q r) := Finset.sum_comm
      _ = ∑ s, ∑ r, A s r • (Q s * Q r) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro r _
        rw [hs r s]
      _ = 0 := weighted_clifford_product_zero Q hQ A hs ht
  have hid : Matrix.trace (blockAction Q A S) =
      -(1 / 2 : ℝ) * Matrix.trace ((∑ r, ∑ s, A r s • (Q s * Q r)) * S) := by
    change Matrix.trace (-(1 / 2 : ℝ) • (∑ r, ∑ s, A r s • (Q r * S * Q s))) = _
    simp only [Matrix.trace_smul, Matrix.trace_sum, Matrix.sum_mul,
      Matrix.smul_mul, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.trace_mul_cycle]
  rw [hid, hrev, zero_mul, Matrix.trace_zero, mul_zero]

theorem traceFreePart_symmetric (S : Matrix4) (hS : Sᵀ = S) :
    (traceFreePart S)ᵀ = traceFreePart S := by
  simp only [traceFreePart, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, hS]

theorem traceFreePart_trace (S : Matrix4) : Matrix.trace (traceFreePart S) = 0 := by
  simp only [traceFreePart, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  ring

theorem scalarPairing_one_right (S : Matrix4) : scalarPairing S 1 = Matrix.trace S := by
  simp [scalarPairing, Matrix.one_apply, Matrix.trace, Matrix.diag]

theorem scalarPairing_sub_right (R S T : Matrix4) :
    scalarPairing R (S - T) = scalarPairing R S - scalarPairing R T := by
  simp only [scalarPairing, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem scalarPairing_smul_right (r : ℝ) (R S : Matrix4) :
    scalarPairing R (r • S) = r * scalarPairing R S := by
  rw [scalarPairing_comm, scalarPairing_smul_left, scalarPairing_comm S R]

theorem blockQuadratic_traceFreePart (Q : Fin 3 → Matrix4)
    (hskew : ∀ r, (Q r)ᵀ = -Q r)
    (hQ : ∀ r s, Q r * Q s + Q s * Q r =
      (if r = s then (-2 : ℝ) else 0) • (1 : Matrix4))
    (A : Mat) (hs : symmetric A) (ht : traceFree A) (S : Matrix4) :
    blockQuadratic Q A (traceFreePart S) = blockQuadratic Q A S := by
  rw [blockQuadratic_eq_pairing Q hskew, blockQuadratic_eq_pairing Q hskew]
  have hact : blockAction Q A (traceFreePart S) = blockAction Q A S := by
    change blockActionLinear Q A (S - (Matrix.trace S / 4) • (1 : Matrix4)) = _
    rw [map_sub, map_smul]
    change blockAction Q A S - (Matrix.trace S / 4) • blockAction Q A 1 = _
    rw [blockAction_one Q hQ A hs ht, smul_zero, sub_zero]
  rw [hact, traceFreePart, scalarPairing_sub_right, scalarPairing_smul_right,
    scalarPairing_one_right, blockAction_trace Q hQ A hs ht, mul_zero, sub_zero]

/-- The actual scalar Hessian may retain its trace; the Weyl contraction
only sees the trace-free part. -/
theorem scalarHessian_coefficient_bound_full (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (htA : traceFree A) (htU : traceFree U)
    (x y : ℝ) (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (S : Matrix4) (hS : Sᵀ = S) :
    blockQuadratic quaternionMatrix A S + blockQuadratic oppositeMatrix U S ≤
      4 * scalarNormSq (traceFreePart S) := by
  rw [← blockQuadratic_traceFreePart quaternionMatrix quaternionMatrix_transpose
      quaternionMatrix_anticommutator A hA htA S,
    ← blockQuadratic_traceFreePart oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
      oppositeMatrix_anticommutator U hU htU S]
  exact scalarHessian_coefficient_bound A U hA hU htA htU x y hAx hUy hxy
    (traceFreePart S) (traceFreePart_symmetric S hS) (traceFreePart_trace S)

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! Integrability at a zero Weyl norm is obtained from uniformly bounded
regularized energies and Fatou's lemma. No integrability of the singular
quotient is assumed in the limiting argument. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter TraceHessian
open scoped BigOperators _root_.Topology

noncomputable section

theorem integrable_of_ae_limit_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hF : ∀ n, Integrable (F n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖F n x‖ ∂μ) ≤ C) : Integrable f μ := by
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hF n).aestronglyMeasurable) hlim, ?_⟩
  have hf : (∫⁻ x, ‖f x‖ₑ ∂μ) ≤
      liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ‖F n x‖ₑ) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono (fun x hx => hx.enorm.liminf_eq.symm))
      _ ≤ _ := lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm)
  have hb : liminf (fun n => ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro n
    refine (iInf₂_le n le_rfl).trans ?_
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact lt_of_le_of_lt (hf.trans hb) ENNReal.ofReal_lt_top

end
end PositiveEinsteinFour.Geometry
end


section

/-! The strengthened scalar Bochner inequality is derived from the actual
metric Green identities and the proved finite-dimensional Hessian estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian ScalarHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}
  {a : M → ℝ}

theorem scalarTraceFreeHessian_eq_part (e : FrameBundle g) :
    scalarTraceFreeHessian g a e = traceFreePart (scalarHessian g a e) := by
  ext i j
  change scalarHessian g a e i j - (if i = j then scalarLaplacian g a e / 4 else 0) =
    scalarHessian g a e i j - (Matrix.trace (scalarHessian g a e) / 4) *
      (if i = j then 1 else 0)
  change _ = scalarHessian g a e i j - (scalarLaplacian g a e / 4) *
    (if i = j then 1 else 0)
  split_ifs <;> ring

theorem ScalarCovariantData.continuousTraceFreeSquare (s : ScalarCovariantData d a) :
    Continuous (fun e => ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) := by
  unfold scalarTraceFreeHessian
  have hL := s.continuousLaplacian
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hHij := s.continuousHessian i j
  split_ifs <;> fun_prop

theorem ScalarCovariantData.continuousWeylHessianForm (s : ScalarCovariantData d a)
    (o : OppositeWeylData d) : Continuous (scalarWeylHessianForm g a) := by
  have hp := continuous_generalCoefficient quaternionMatrix d.continuousWeyl
  have hm := continuous_generalCoefficient Angular.oppositeMatrix o.continuousWeyl
  have hH := s.continuousHessian
  unfold scalarWeylHessianForm blockQuadratic
  fun_prop

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

local instance scalarWeightedBochnerRing_r8e6650_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance scalarWeightedBochnerSpace_r8e6650_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance scalarWeightedBochnerAlgebra_r8e6650_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem ScalarCovariantData.weighted_bochner (s : ScalarCovariantData d a)
    (o : OppositeWeylData d) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)) :
    (∫ e, (4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
      normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) *
        ‖scalarGradientVector g a e‖ ^ 2 ∂μ) ≤ ∫ e, scalarLaplacian g a e ^ 2 ∂μ := by
  have hpcont := s.continuousGradientVector.norm.pow 2
  have hvcont := continuous_normalizedBlockNorm.comp d.continuousWeyl
  have hbcont := continuous_normalizedBlockNorm.comp o.continuousWeyl
  have intg {f : FrameBundle g → ℝ} (h : Continuous f) : Integrable f μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hoperator (e : FrameBundle g) :
      scalarWeylHessianForm g a e ≤ 4 * ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hp e
    have hS : (scalarHessian g a e)ᵀ = scalarHessian g a e := by
      ext i j
      exact s.hessianSymmetric e j i
    have h := scalarHessian_coefficient_bound_full
      (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (d.weyl.symmetric e) (o.symmetric e) (d.weyl.traceFree e) (o.traceFree e)
      x y hx hy hxy (scalarHessian g a e) hS
    rw [← scalarTraceFreeHessian_eq_part] at h
    simpa only [scalarWeylHessianForm, scalarNormSq, scalarPairing, pow_two] using h
  exact Variance.bochner_weighted_energy
    (intg hpcont) (intg s.continuousTraceFreeSquare)
    (intg (s.continuousWeylHessianForm o))
    (intg (((hvcont.pow 2).add (hbcont.pow 2)).mul hpcont))
    s.integrated_bochner (s.curvature_identity o hdecomp)
    (Filter.Eventually.of_forall hoperator)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The weighted scalar variance inequality for smooth functions, derived
from the weighted Bochner estimate and degree-zero Poisson solvability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem smooth_weighted_variance
    (o : OppositeWeylData d) (hcalc : PetersenScalarCalculusInput d)
    (hpoisson : PetersenPoissonInput g μ) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (a : M → ℝ) (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) :
    (∫ e, (a e.base - ∫ f, a f.base ∂μ) ^ 2 ∂μ) ≤
      ∫ e, ‖scalarGradientVector g a e‖ ^ 2 /
        (4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
          normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) ∂μ := by
  obtain ⟨s⟩ := hcalc a ha
  obtain ⟨φ, hφ, hΔ⟩ := hpoisson a ha
  obtain ⟨t⟩ := hcalc φ hφ
  let K : FrameBundle g → ℝ := fun e =>
    4 + normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
      normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2
  have hK (e : FrameBundle g) : 0 < K e := by dsimp [K]; positivity
  have hKc : Continuous K := by
    exact (continuous_const.add ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2)).add
      ((continuous_normalizedBlockNorm.comp o.continuousWeyl).pow 2)
  have intg {f : FrameBundle g → ℝ} (h : Continuous f) : Integrable f μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf := intg ((s.continuousGradientVector.norm.pow 2).div hKc (fun e => (hK e).ne'))
  have hg := intg (hKc.mul (t.continuousGradientVector.norm.pow 2))
  have hc := intg ((s.continuousGradientVector.inner t.continuousGradientVector).neg)
  have hcpoint (e : FrameBundle g) :
      -inner ℝ (scalarGradientVector g a e) (scalarGradientVector g φ e) =
        -(∑ i, scalarGradient g a e i * scalarGradient g φ e i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      scalarGradientVector, mul_comm]
  have hpair : (∫ e, -inner ℝ (scalarGradientVector g a e) (scalarGradientVector g φ e) ∂μ) =
      ∫ e, (a e.base - ∫ f, a f.base ∂μ) ^ 2 ∂μ := by
    calc
      _ = -(∫ e, ∑ i, scalarGradient g a e i * scalarGradient g φ e i ∂μ) := by
        simp_rw [hcpoint]
        exact integral_neg _
      _ = ∫ e, a e.base * scalarLaplacian g φ e ∂μ := by
        rw [s.scalar_pairing_green t, neg_neg]
      _ = ∫ e, a e.base * (a e.base - ∫ f, a f.base ∂μ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun e => congrArg (fun z => a e.base * z) (hΔ e))
      _ = _ := Variance.centered_product_integral s.valueField
  have hbound : (∫ e, K e * ‖scalarGradientVector g φ e‖ ^ 2 ∂μ) ≤
      ∫ e, (a e.base - ∫ f, a f.base ∂μ) ^ 2 ∂μ := by
    have h := t.weighted_bochner o hp hdecomp
    simpa only [hΔ] using h
  exact Variance.variance_le_of_poisson_pairing hf hg hc
    (Filter.Eventually.of_forall (fun e => div_nonneg (sq_nonneg _) (hK e).le))
    (Filter.Eventually.of_forall (fun e => mul_nonneg (hK e).le (sq_nonneg _)))
    (Filter.Eventually.of_forall (fun e => Variance.weighted_inner_sq_le
      (scalarGradientVector g a e) (scalarGradientVector g φ e) (hK e)))
    (integral_nonneg (fun e => sq_nonneg _)) hpair hbound

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the proved scalar variance theorem to smooth regularizations of
actual oriented Weyl norms. All equalities with frame derivatives are
proved from the raw parallel calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}

theorem PetersenOrientedNormInput.plus_regularized_vector
    {orientation : FrameOrientation g} (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation) {ε : ℝ} (hε : 0 < ε)
    (s : ScalarCovariantData d (orientedNormRegularization (plusNorm orientation) ε))
    (e : FrameBundle g) (he : e ∈ orientation.positive) :
    scalarGradientVector g (orientedNormRegularization (plusNorm orientation) ε) e =
      Variance.regularizedRadialVector (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε
        (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) := by
  ext i
  change scalarGradient g _ e i =
    (normalizedBlockNorm (plusWeyl g e.base e.frame) /
      regularizedBlockNorm ε (plusWeyl g e.base e.frame)) *
        regularizedRadialDerivative 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
  rw [h.plus_regularized_gradient hflow hε s e he i, regularizedRadialDerivative_scale]

variable [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem smooth_weighted_variance_ae
    (o : OppositeWeylData d) (hcalc : PetersenScalarCalculusInput d)
    (hpoisson : PetersenPoissonInput g μ) (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (a : M → ℝ) (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (f : FrameBundle g → ℝ) (p : FrameBundle g → Bianchi.Vec)
    (hf : (fun e => a e.base) =ᵐ[μ] f)
    (hpgrad : scalarGradientVector g a =ᵐ[μ] p) :
    (∫ e, f e ^ 2 ∂μ) - (∫ e, f e ∂μ) ^ 2 ≤
      ∫ e, ‖p e‖ ^ 2 / scalarVarianceWeight g e ∂μ := by
  obtain ⟨s⟩ := hcalc a ha
  have hi : Integrable (fun e => a e.base) μ := s.continuousValue.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun e => a e.base ^ 2) μ := (s.continuousValue.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hv := smooth_weighted_variance o hcalc hpoisson hp hdecomp a ha
  rw [Variance.integral_centered_square hi hi2, Variance.variance_congr_ae hf] at hv
  apply hv.trans_eq
  apply integral_congr_ae
  filter_upwards [hpgrad] with e he
  rw [he]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The single-norm and square-root-polynomial smooth tests used in the
final variance and balanced-moment arguments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem regularized_plus_variance
    (o : OppositeWeylData d) (orientation : FrameOrientation g)
    (h : PetersenOrientedNormInput orientation)
    (hflow : OrientationPreservingFlow d orientation)
    (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hcalc : PetersenScalarCalculusInput d) (hpoisson : PetersenPoissonInput g μ)
    (hp : ShiftedCurvaturePositive g)
    (hdecomp : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ e, Variance.hRegularizedArgument (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε ^ 2 ∂μ) -
      (∫ e, Variance.hRegularizedArgument (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε ∂μ) ^ 2 ≤
      ∫ e, Variance.regularizedNormEnergy (normalizedBlockNorm (plusWeyl g e.base e.frame)) ε (scalarVarianceWeight g e)
        (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)) ∂μ := by
  let a := orientedNormRegularization (plusNorm orientation) ε
  have ha := orientedNormRegularization_smooth h.plusSquareSmooth hε
  obtain ⟨s⟩ := hcalc a ha
  apply smooth_weighted_variance_ae o hcalc hpoisson hp hdecomp a ha
  · filter_upwards [hae] with e he
    change Real.sqrt (plusNorm orientation e.base ^ 2 + ε ^ 2) = _
    rw [h.plusFrame e he]
    rfl
  · filter_upwards [hae] with e he
    exact h.plus_regularized_vector hflow hε s e he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The invariant Bianchi refined Kato inequality for the metric. The weak
norm equations and singular quotient integrability follow from parallel-frame
covariant calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem refinedKato (d : MetricGreenData g μ) (e : FrameBundle g) :
    (5 / 3 : ℝ) * ‖blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤
        weylGradientEnergy (plusWeylGradient g e.base e.frame) :=
  QuaternionFrame.blockRadialGradient_refined_kato _ _ (d.weyl.symmetric e)
    (d.weyl.traceFree e) (d.gradientConstraints e).1 (d.gradientConstraints e).2
    (d.gradientBianchi e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability of the scalar weak equation and of its radial terms.
The estimates use the actual metric Kato bound, including the zero set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

theorem radial_integrable (d : MetricGreenData g μ) (i : Fin 4) :
    Integrable (fun e => regularizedRadialDerivative 0 (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i)) μ := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  let H : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm
    (plusWeylGradient g e.base e.frame i),
    continuous_normalizedBlockNorm.comp (d.continuousGradient i)⟩
  have hF (n) : Integrable (fun e => d.regularizedRadialField (ε n) (hε n) i e) μ :=
    (d.regularizedRadialField (ε n) (hε n) i).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply integrable_of_ae_limit_norm_bound μ
    (fun n e => d.regularizedRadialField (ε n) (hε n) i e) _ (∫ e, H e ∂μ) hF
  · filter_upwards [] with e
    simpa only [ε, regularizedRadialField, ContinuousMap.coe_mk, Function.comp_def,
      regularizedRadialDerivative, regularizedBlockNorm_zero] using
      (tendsto_regularizedRadialDerivative (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i)).comp tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    apply integral_mono_ae (hF n).norm
      (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    filter_upwards [] with e
    rw [Real.norm_eq_abs]
    exact abs_regularizedRadialDerivative_le (ε n) (hε n) _ _ ((d.gradientConstraints e).1 i)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Measurability and square integrability of both actual radial gradients
on the original oriented measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem blockRadialGradient_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (A : Ω → Mat) (Z : Ω → Fin 4 → Mat)
    (h : ∀ i, AEStronglyMeasurable (fun x => regularizedRadialDerivative 0 (A x) (Z x i)) μ) :
    AEStronglyMeasurable (fun x => blockRadialGradient (A x) (Z x)) μ := by
  have hm : AEMeasurable (fun x i => regularizedRadialDerivative 0 (A x) (Z x i)) μ :=
    AEMeasurable.of_eval (fun i => (h i).aemeasurable)
  exact ((PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable hm).aestronglyMeasurable

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

variable (d : MetricGreenData g μ)

include d

theorem radialVector_measurable :
    AEStronglyMeasurable (fun e => blockRadialGradient (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame)) μ :=
  blockRadialGradient_aestronglyMeasurable _ _ (fun i => (d.radial_integrable i).aestronglyMeasurable)

theorem radialEnergy_integrable : Integrable (fun e : FrameBundle g => plusRadialEnergy e) μ := by
  have hE : Integrable (fun e => weylGradientEnergy (plusWeylGradient g e.base e.frame)) μ :=
    d.gradientEnergyField.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hE.mono' (d.radialVector_measurable.norm.pow 2)
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ≤ _
  have hk := d.refinedKato e
  nlinarith [sq_nonneg ‖blockRadialGradient (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame)‖]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weyl-norm difference variance follows by passing the smooth scalar
theorem to the limit using parallel-frame calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}

theorem blockRadialGradient_zero_of_norm_zero (A : Mat) (Z : Fin 4 → Mat)
    (h : normalizedBlockNorm A = 0) : blockRadialGradient A Z = 0 := by
  have hA := (normalizedBlockNorm_eq_zero_iff A).mp h
  subst A
  ext i
  simp [blockRadialGradient, regularizedRadialDerivative]

theorem normRegularizationParameter_mem (n : ℕ) :
    normRegularizationParameter n ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · unfold normRegularizationParameter
    positivity
  · unfold normRegularizationParameter
    exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem normRegularizationParameter_tendsto :
    Tendsto normRegularizationParameter atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem scalarVarianceWeight_continuous (o : OppositeWeylData d) :
    Continuous (scalarVarianceWeight g) :=
  (continuous_const.add ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2)).add
    ((continuous_normalizedBlockNorm.comp o.continuousWeyl).pow 2)

theorem scalarVarianceWeight_ge_one (e : FrameBundle g) : 1 ≤ scalarVarianceWeight g e := by
  unfold scalarVarianceWeight
  nlinarith [sq_nonneg (normalizedBlockNorm (plusWeyl g e.base e.frame)),
    sq_nonneg (normalizedBlockNorm (minusWeyl g e.base e.frame))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weighted variance of each actual Weyl norm and of the square-root
polynomial H. The final H bound combines the proved scalar variance and
weak Weyl norm equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.plusWeightedNormVariance
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (_hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame)) ^ 2 ∂μ) - (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ∂μ) ^ 2 ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 / scalarVarianceWeight g e ∂μ := by
  apply Variance.norm_variance_of_regularized
    (continuous_normalizedBlockNorm.comp d.continuousWeyl).aemeasurable
    (scalarVarianceWeight_continuous o).aemeasurable d.radialVector_measurable
    (Filter.Eventually.of_forall (fun e => ⟨normalizedBlockNorm_nonneg _, by
      change normalizedBlockNorm (plusWeyl g e.base e.frame) ≤ 2
      linarith [hpinch e, normalizedBlockNorm_nonneg (minusWeyl g e.base e.frame)]⟩))
    (Filter.Eventually.of_forall scalarVarianceWeight_ge_one)
    (Filter.Eventually.of_forall (fun e => blockRadialGradient_zero_of_norm_zero _ _))
    d.radialEnergy_integrable
    normRegularizationParameter normRegularizationParameter_mem normRegularizationParameter_tendsto
  intro n
  exact regularized_plus_variance o orientation s.norms s.orientationFlow s.supported
    s.calculus s.poisson s.positive s.decomposition (normRegularizationParameter_mem n).1

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Scalar variance bounds for one-block vanishing, and the H-variance bounds
used to balance the two Weyl moments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem integral_div_le_of_one_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E K : Ω → ℝ} (hi : Integrable E μ) (hm : AEMeasurable K μ)
    (hE : ∀ᵐ x ∂μ, 0 ≤ E x) (hK : ∀ᵐ x ∂μ, 1 ≤ K x) :
    (∫ x, E x / K x ∂μ) ≤ ∫ x, E x ∂μ := by
  have hb : ∀ᵐ x ∂μ, ‖E x / K x‖ ≤ E x := by
    filter_upwards [hE, hK] with x hEx hKx
    have hp : 0 < K x := lt_of_lt_of_le (by norm_num) hKx
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hEx hp.le)]
    exact (div_le_iff₀ hp).2 (le_mul_of_one_le_right hEx hKx)
  have hdi := hi.mono' (hi.aemeasurable.div hm).aestronglyMeasurable hb
  apply integral_mono_ae hdi hi
  filter_upwards [hb] with x hx
  exact (le_abs_self _).trans hx

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

theorem MetricGreenData.plusNormVariance_oai
    (d : MetricGreenData g μ) (o : OppositeWeylData d) {orientation : FrameOrientation g}
    (s : ScalarVarianceInputs d orientation) (hparallel : ParallelReflection d)
    (hpinch : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2) :
    (∫ e, (normalizedBlockNorm (plusWeyl g e.base e.frame) - ∫ f, normalizedBlockNorm (plusWeyl g f.base f.frame) ∂μ) ^ 2 ∂μ) ≤
      ∫ e, ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2 ∂μ := by
  have hi : Integrable (fun e : FrameBundle g => normalizedBlockNorm (plusWeyl g e.base e.frame)) μ :=
    (continuous_normalizedBlockNorm.comp d.continuousWeyl).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun e : FrameBundle g => (normalizedBlockNorm (plusWeyl g e.base e.frame)) ^ 2) μ :=
    ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [Variance.integral_centered_square hi hi2]
  exact (d.plusWeightedNormVariance o s hparallel hpinch).trans
    (integral_div_le_of_one_le d.radialEnergy_integrable
      (scalarVarianceWeight_continuous o).aemeasurable
      (Filter.Eventually.of_forall (fun e => sq_nonneg _))
      (Filter.Eventually.of_forall scalarVarianceWeight_ge_one))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

theorem solution.{u_1} : type_of% @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance_oai.{u_1} := @OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance_oai.{u_1}
