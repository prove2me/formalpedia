-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_residue_source_with_scales
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T04:32:53.718995+00:00
-- url     : https://prove2.me/submissions/14f07bdd-c2f3-4aec-9819-1ef10e70cfcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1375
import Definitions.Def_OAIErdos3B1383
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLongJetProxy_residue_error
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLongJetProxy_zero_off_ball
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNormalizedLongJetDensity_zero_off_ball
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_proxy_l1_with_scales

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomialMonomial_eval {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) (x : I → ℝ) :
    MvPolynomial.eval x (polynomialMonomial a m) =
      ∏ k ∈ m.support, MvPolynomial.eval x (a k) ^ m k := by
  simp only [polynomialMonomial, map_prod, map_pow]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial


end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffineInput_eval {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) (x : I → ℝ) :
    MvPolynomial.eval x (booleanAffineInput a t) =
      ∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (a r) := by
  simp only [booleanAffineInput, map_sum, map_mul, MvPolynomial.eval_C]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanJetColumnPolynomial_eval {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α) (x : P → ℝ) :
    MvPolynomial.eval x (booleanJetColumnPolynomial e input s) =
      booleanCoefficient (fun t => ∏ k ∈ e.support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e k) s := by
  simp only [booleanJetColumnPolynomial, booleanCoefficient_map, polynomialMonomial_eval, booleanAffineInput_eval]

theorem booleanJetColumns_apply_coefficients {K P α O J : Type*} [Fintype α] [DecidableEq α]
    [Fintype O] [Fintype J] (e : J → K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ)
    (rows : O → Finset α) (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => booleanJetColumnPolynomial (e j) input (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (∑ r, (booleanFeature r t : ℝ) * MvPolynomial.eval x (input k r)) ^ e j k) (rows o) := by
  simp only [booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, MvPolynomial.eval x (booleanJetColumnPolynomial (e j) input (rows o)) * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [booleanJetColumnPolynomial_eval, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

variable [Fintype ι]

theorem linearDensityPullback_integrable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (linearDensityPullback A f) := by
  have hm : Integrable f (Measure.map A.symm volume) := by
    rw [inverse_map_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (A.symm.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hm).const_mul _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

theorem diagonalDensityTransport_det :
    LinearMap.det (coordinateScaleEquiv a ha).toLinearMap = ∏ i, a i := by
  classical
  have hm : LinearMap.toMatrix' (coordinateScaleEquiv a ha).toLinearMap = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply]
    · simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply, hij]
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_diagonal]

theorem diagonalDensityTransport_eq (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    diagonalDensityTransport a ha f x = |∏ i, a i|⁻¹ * f (fun i => x i / a i) := by
  unfold diagonalDensityTransport linearDensityPullback
  rw [inverseJacobian_eq]
  change |LinearMap.det (coordinateScaleEquiv a ha).toLinearMap|⁻¹ *
    f (fun i => x i / a i) = _
  rw [diagonalDensityTransport_det]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical


end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal



end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem diagonalImageDensity_eq_pullback (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (f : (ι → ℝ) → ℝ) :
    diagonalImageDensity d f =
      linearDensityPullback (coordinateScaleEquiv d hd).toContinuousLinearEquiv f := by
  funext x
  simpa only [diagonalImageDensity, diagonalDensityTransport, Finset.abs_prod] using
    (diagonalDensityTransport_eq d hd f x).symm

theorem diagonalImageDensity_integrable (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (diagonalImageDensity d f) := by
  rw [diagonalImageDensity_eq_pullback d hd]
  exact linearDensityPullback_integrable _ hf

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

theorem sigmaAxisCoordinates_symm_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I).symm volume volume := by
  refine ⟨(sigmaAxisCoordinates I).symm.continuous.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (sigmaAxisCoordinates I).symm.continuous.measurable (MeasurableSet.univ_pi hs)]
  have he : (sigmaAxisCoordinates I).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i : I d => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, volume_pi_pi]
  simp only [volume_pi_pi, Fintype.prod_sigma]

theorem sigmaAxisCoordinates_measurePreserving :
    MeasurePreserving (sigmaAxisCoordinates I) volume volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).symm
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem frozenTupleCoordinate_eval {Z P : Type*} (z : Z → ℝ) (x : P → ℝ) (i : Z ⊕ P) :
    MvPolynomial.eval x (frozenTupleCoordinate z i) = Sum.elim z x i := by
  cases i <;> simp [frozenTupleCoordinate]

theorem normalizedJetColumns_apply_coefficients {Z P K α O J : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [Fintype J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : O → Finset α)
    (x : P → ℝ) (c : J → ℝ) (o : O) :
    polynomialColumns (fun o j => normalizedJetColumn (e j) input z (rows o)) x c o =
      booleanCoefficient (fun t => ∑ j, c j * ∏ k ∈ (e j).support,
        (normalizedCubeTuple input z x t k)^e j k) (rows o) := by
  simpa only [normalizedJetColumn, frozenTupleCoordinate_eval, normalizedCubeTuple] using
    booleanJetColumns_apply_coefficients e (fun k r => frozenTupleCoordinate z (input k r)) rows x c o

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PivotCoordinateChange
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotDensityPullback_measurable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (pivotDensityPullback A B f) :=
  measurable_const.mul (hf.comp (pivotCoordinateChange A B).symm.continuous.measurable)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

theorem pivotOutputDensity_measurable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (pivotOutputDensity A B f) :=
  (pivotDensityPullback_measurable A B hf).stronglyMeasurable.integral_prod_left'.measurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory


end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators


end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

omit [∀ d, Fintype (I d)] in
theorem sigmaAxisWeight_nonneg (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d y, 0 ≤ w d y) (x : (Σ d, I d) → ℝ) : 0 ≤ sigmaAxisWeight w x :=
  tensorCutoffWeight_nonneg w hw _

theorem sigmaAxisWeight_integral (w : ∀ d, (I d → ℝ) → ℝ) :
    (∫ x, sigmaAxisWeight w x) = ∏ d, ∫ y, w d y := by
  calc
    _ = ∫ x, tensorCutoffWeight w x :=
      (sigmaAxisCoordinates_measurePreserving I).integral_comp
        (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding _
    _ = _ := tensorCutoffWeight_integral w

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_slice_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    Integrable (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by
  have hc : Continuous (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J → ℝ) × (N → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  apply hp
  have heq : ‖Sum.elim p.1 p.2‖ = ‖p‖ := (splitCoordinates_norm (Sum.elim p.1 p.2)).symm
  have hz := splitFreeProfile_zero_outside hfs hgs
    (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))
    (h.trans_le (heq ▸ norm_fst_le
      (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))))
  exact hz

end Erdos3

end

section

namespace Erdos3

open scoped Matrix


end Erdos3

end

section

namespace Erdos3

open scoped NNReal


end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3


end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitPivotDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v =
      ∫ n, g n * pivotOutputDensity A B f (v - C n) := by
  let F : (J → ℝ) × (N → ℝ) → ℝ := fun p =>
    f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2
  have hi : Integrable F := splitFreeProfile_slice_integrable A B C hf hg hfs hgs v
  rw [pivotOutputDensity_formula]
  change inverseJacobian A * (∫ y, splitInputProfile F y) = _
  rw [splitInputProfile_integral, Measure.volume_eq_prod, integral_prod_symm _ hi,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  have heq (y : J → ℝ) : v - (B y + C n) = (v - C n) - B y := by abel
  simp only [F, heq, integral_mul_const, pivotOutputDensity_formula]
  ring

end Erdos3

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

namespace Erdos3

open MeasureTheory

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetMeasurability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem normalizedCubeTuple_measurable_comp {Ω Z P K α : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] (input : K → Option α → Z ⊕ P)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j)) (t : Finset α) (k : K) :
    Measurable (fun ω => normalizedCubeTuple input (z ω) (x ω) t k) := by
  have hs (i : Z ⊕ P) : Measurable (fun ω => Sum.elim (z ω) (x ω) i) := by
    cases i with
    | inl j => exact hz j
    | inr j => exact hx j
  unfold normalizedCubeTuple
  fun_prop

theorem normalizedJetColumns_measurable_comp {Ω Z P K α I N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype N]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (rows : I → Finset α)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j))
    (c : Ω → N → ℝ) (hc : ∀ j, Measurable (fun ω => c ω j)) :
    Measurable (fun ω => polynomialColumns (fun o n => normalizedJetColumn (e n) input (z ω) (rows o)) (x ω) (c ω)) := by
  apply measurable_pi_iff.mpr
  intro o
  simp_rw [normalizedJetColumns_apply_coefficients, booleanCoefficient]
  have ht (t : Finset α) (k : K) := normalizedCubeTuple_measurable_comp input z hz x hx t k
  fun_prop

theorem normalizedJetDensity_measurable_comp {Ω Z P K α I J N : Type*} [MeasurableSpace Ω]
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (rows : I → Finset α)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {R S : ℝ} (hfs : ∀ u, R < ‖u‖ → f u = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun ω => z ω j))
    (x : Ω → P → ℝ) (hx : ∀ j, Measurable (fun ω => x ω j))
    (v : Ω → I → ℝ) (hv : ∀ i, Measurable (fun ω => v ω i)) :
    Measurable (fun ω => normalizedJetDensity A F e input (z ω) rows f g (x ω) (v ω)) := by
  have he : (fun ω => normalizedJetDensity A F e input (z ω) rows f g (x ω) (v ω)) =
      (fun ω => ∫ n, g n * pivotOutputDensity A F f (v ω -
        polynomialColumns (fun o n => normalizedJetColumn (e n) input (z ω) (rows o)) (x ω) n)) :=
    funext (fun ω => splitPivotDensity_formula A F _ hf hg hfs hgs (v ω))
  rw [he]
  have hcols := normalizedJetColumns_measurable_comp (Ω := Ω × (N → ℝ)) e input rows
    (fun q => z q.1) (fun j => (hz j).comp measurable_fst)
    (fun q => x q.1) (fun j => (hx j).comp measurable_fst)
    (fun q => q.2) (fun j => (measurable_pi_apply j).comp measurable_snd)
  have hv' : Measurable v := measurable_pi_iff.mpr hv
  have htest := (hg.measurable.comp measurable_snd).mul
    ((pivotOutputDensity_measurable A F hf.measurable).comp ((hv'.comp measurable_fst).sub hcols))
  exact htest.stronglyMeasurable.integral_prod_right'.measurable

theorem normalizedJetDensity_measurable {Z P K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (rows : I → Finset α)
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    {R S : ℝ} (hfs : ∀ u, R < ‖u‖ → f u = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0) :
    Measurable (Function.uncurry (normalizedJetDensity A F e input z rows f g)) := by
  change Measurable (fun q : (P → ℝ) × (I → ℝ) => normalizedJetDensity A F e input z rows f g q.1 q.2)
  exact normalizedJetDensity_measurable_comp (Ω := (P → ℝ) × (I → ℝ))
    A F e input rows hf hg hfs hgs
    (fun _ => z) (fun _ => measurable_const) (fun q => q.1)
    (fun i => (measurable_pi_apply i).comp measurable_fst) (fun q => q.2)
    (fun i => (measurable_pi_apply i).comp measurable_snd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem principalTupleFlatten_norm_apply_le {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (α : Type*) [Fintype α]
    (x : PrincipalTupleIndex B h → Option α → ℝ) : ‖principalTupleFlatten B h α x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro z
  exact (norm_le_pi_norm (x ⟨z.1, z.2.1, z.2.2.1⟩) z.2.2.2).trans
    (norm_le_pi_norm x ⟨z.1, z.2.1, z.2.2.1⟩)

end Erdos3

namespace Erdos3

open MeasureTheory

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

theorem integerScalarCube_endpoint_normalized_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    {H : ℕ} (hH : 2 ≤ H) (z : Option I → ℤ) (hz : IntegerScalarCube H z) :
    ‖fun i => (z i : ℝ) / ((H : ℝ) - 1)‖ ≤ 1 := by
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hi := integerScalarCube_coordinates hz i
  have hzi : -(H : ℤ) + 1 ≤ z i ∧ z i ≤ (H : ℤ) - 1 := by omega
  have hr : |(z i : ℝ)| ≤ (H : ℝ) - 1 := by
    apply abs_le.mpr
    have hl : -(H : ℝ) + 1 ≤ (z i : ℝ) := by exact_mod_cast hzi.1
    have hu : (z i : ℝ) ≤ (H : ℝ) - 1 := by exact_mod_cast hzi.2
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < (H : ℝ) - 1)]
  exact (div_le_one (by linarith)).mpr hr

theorem affineCubeTuple_norm_le {J I : Type*} [Fintype J] [Fintype I]
    (lower width : J → ℝ) (hw : ∀ j, |lower j| + |width j| ≤ 1)
    (x : J → Option I → ℝ) (hx : ‖x‖ ≤ 1) : ‖affineCubeTuple lower width x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hxi : |x j i| ≤ 1 :=
    (norm_le_pi_norm (x j) i).trans ((norm_le_pi_norm x j).trans hx)
  have hc : |if i = none then lower j else 0| ≤ |lower j| := by
    split_ifs <;> simp
  exact (abs_add_le _ _).trans ((add_le_add hc
    ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left hxi (abs_nonneg _)))).trans
      (by simpa using hw j))

theorem progressionTuple_norm_le {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (L step H : J → ℕ) (c : J → ℤ) (hH : ∀ j, 2 ≤ H j)
    (hw : ∀ j, |(c j : ℝ) / L j| + |(step j : ℝ) * ((H j : ℝ) - 1) / L j| ≤ 1)
    (z : ∀ j, IntegerScalarCubeBox I (H j))
    (hz : ∀ j, IntegerScalarCube (H j) (fun i => (z j i : ℤ))) :
    ‖fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j‖ ≤ 1 := by
  have hn : ‖fun j i => (z j i : ℝ) / ((H j : ℝ) - 1)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact integerScalarCube_endpoint_normalized_norm_le (hH j) _ (hz j)
  have he := affineCubeTuple_norm_le (fun j => (c j : ℝ) / L j)
    (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) hw _ hn
  convert he using 2
  funext j i
  have hd : (H j : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ H j := by exact_mod_cast hH j
    linarith
  dsimp only [affineCubeTuple]
  split_ifs <;> field_simp
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i

include hR hσ hσ1 in
theorem allocatedKernelProfile_bound (d) : |centers d|+widths d ≤ R j :=
  (allocatedProfile_term_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerIntegerPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical








end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial


end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)


local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))

include hR hσ in
theorem allocatedContinuousKernelDensity_measurable (hσ1 : σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedContinuousKernelDensity B U basis S j i x u rows s hA)) := by
  have hw (d) := allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)
  have hb (d) := allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)
  exact normalizedJetDensity_measurable pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun d => hw (.inl d)) (hR j).le (fun d => hb (.inl d))))
    (affineProductProfile_zero_outside _ _ (fun d => hw (.inr d)) (hR j).le (fun d => hb (.inr d)))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial



end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix





end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))


local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => height))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))

include hR hσ in
theorem allocatedIntegerKernelDensity_measurable (hσ1 : σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedIntegerKernelDensity B U basis S j i x u rows s hA)) := by
  have hw (d) := allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)
  have hb (d) := allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)
  exact normalizedJetDensity_measurable pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun d => hw (.inl d)) (hR j).le (fun d => hb (.inl d))))
    (affineProductProfile_zero_outside _ _ (fun d => hw (.inr d)) (hR j).le (fun d => hb (.inr d)))

include hR hσ in
theorem allocatedIntegerKernelDensity_probability_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (∀ z, 0 ≤ allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z) ∧
      Integrable (allocatedIntegerKernelDensity B U basis S j i x u rows s hA y) ∧
      (∫ z, allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z) = 1 :=
  affineSelectedJetDensity_probability_data s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)) y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix






end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ in
theorem allocatedNormalizedLongJetFactor_probability (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) (a : {a // ¬grid a}) :
    (∀ v, 0 ≤ allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a v) ∧
    Integrable (allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a) ∧
    (∫ v, allocatedNormalizedLongJetFactor B U basis S x u rows s hA y a v) = 1 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact allocatedContinuousKernelDensity_probability_data B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) y
  | inr i => exact allocatedIntegerKernelDensity_probability_data B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j) y

include hR hσ in
theorem allocatedNormalizedLongJetFactor_measurable (hσ1 : ∀ j, σ j ≤ 1)
    (a : {a // ¬grid a}) :
    Measurable (fun p : (activeInput → ℝ) × (O a.val.1 → ℝ) =>
      allocatedNormalizedLongJetFactor B U basis S x u rows s hA p.1 a p.2) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact allocatedContinuousKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)
  | inr i => exact allocatedIntegerKernelDensity_measurable B U basis hR hσ S j i x u (rows j) (s j) (hA j) (hσ1 j)

include hR hσ in
theorem allocatedNormalizedLongJetDensity_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedNormalizedLongJetDensity B U basis S x u rows s hA)) := by
  change Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
    ∏ a, allocatedNormalizedLongJetFactor B U basis S x u rows s hA p.1 a (fun o => p.2 ⟨a, o⟩))
  apply Finset.measurable_prod
  intro a _
  have hc : Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
      (p.1, fun o : O a.val.1 => p.2 ⟨a, o⟩)) :=
    measurable_fst.prodMk (measurable_pi_iff.mpr (fun o =>
      (measurable_pi_apply (⟨a, o⟩ : realOutput)).comp measurable_snd))
  exact (allocatedNormalizedLongJetFactor_measurable B U basis hR hσ S x u rows s hA hσ1 a).comp
    (f := fun p : (activeInput → ℝ) × (realOutput → ℝ) => (p.1, fun o => p.2 ⟨a, o⟩)) hc

include hR hσ in
theorem allocatedNormalizedLongJetDensity_probability (hσ1 : ∀ j, σ j ≤ 1)
    (y : activeInput → ℝ) :
    (∀ v, 0 ≤ allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) ∧
    Integrable (allocatedNormalizedLongJetDensity B U basis S x u rows s hA y) ∧
    (∫ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) = 1 := by
  have hp := allocatedNormalizedLongJetFactor_probability B U basis hR hσ S x u rows s hA hσ1 y
  have hm : (∫ v, allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v) = 1 := by
    unfold allocatedNormalizedLongJetDensity
    rw [sigmaAxisWeight_integral]
    exact Finset.prod_eq_one (fun a _ => (hp a).2.2)
  exact ⟨sigmaAxisWeight_nonneg _ (fun a => (hp a).1),
    Integrable.of_integral_ne_zero (hm.trans_ne one_ne_zero), hm⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical





end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical




end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineRadiusLog
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

include hR hσ in
theorem allocatedAffineLongJetDensity_measurable (hσ1 : ∀ j, σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedAffineLongJetDensity B U basis S x u rows s hA center width)) := by
  have hin : Measurable (fun p : (activeInput → ℝ) × (realOutput → ℝ) =>
      ((fun i => center i + width i * p.1 i), p.2)) := by
    apply Measurable.prodMk
    · apply measurable_pi_iff.mpr
      intro i
      exact measurable_const.add (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
    · exact measurable_snd
  exact (allocatedNormalizedLongJetDensity_measurable B U basis hR hσ S x u rows s hA hσ1).comp
    (f := fun p : (activeInput → ℝ) × (realOutput → ℝ) => ((fun i => center i + width i * p.1 i), p.2)) hin

include hR hσ in
theorem allocatedAffineLongJetDensity_probability (hσ1 : ∀ j, σ j ≤ 1) (y : activeInput → ℝ) :
    (∀ v, 0 ≤ allocatedAffineLongJetDensity B U basis S x u rows s hA center width y v) ∧
    Integrable (allocatedAffineLongJetDensity B U basis S x u rows s hA center width y) ∧
    (∫ v, allocatedAffineLongJetDensity B U basis S x u rows s hA center width y v) = 1 :=
  allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u rows s hA hσ1 _

include hR hσ in
theorem allocatedAffineLongJetProxy_probability (hσ1 : ∀ j, σ j ≤ 1) :
    (∀ v, 0 ≤ allocatedAffineLongJetProxy B U basis S x u rows s hA center width v) ∧
    Integrable (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) ∧
    (∫ v, allocatedAffineLongJetProxy B U basis S x u rows s hA center width v) = 1 :=
  densityMixture_probability_density _ _ _
    (allocatedAffineLongJetDensity_measurable B U basis hR hσ S x u rows s hA center width hσ1)
    (Filter.Eventually.of_forall
      (allocatedAffineLongJetDensity_probability B U basis hR hσ S x u rows s hA center width hσ1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal BigOperators Classical


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EarlyAllocatedAffineResidueSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped ContDiff NNReal Classical


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical




end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "Jet" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "bound" => NNReal.mk
  (Real.exp (allocatedDensityLog (G := G) B α O P)) (Real.exp_nonneg _)
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
theorem allocatedAffineLongJetProxy_residue_l1 (hσ1 : ∀ j, σ j ≤ 1)
    (L step H M : Tuple → ℕ) (c : Tuple → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Tuple → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε) :
    let Δ := fun z : Jet → ℝ => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
          (principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
            (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z) -
      allocatedAffineLongJetProxy B U basis S x u rows s hA
        (principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L c)
        (principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
          (fun a => degree a.val) L H step) z
    Integrable Δ ∧ (∫ z, |Δ z|) ≤
      ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
        (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Jet := by
  intro Δ
  let weights := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let tupleLower := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) => (c ⟨a,p⟩ : ℝ) / L ⟨a,p⟩
  let tupleWidth := fun (a : {a // ¬grid a}) (p : B a.val × Fin (degree a.val)) =>
    (step ⟨a,p⟩ : ℝ) * ((H ⟨a,p⟩ : ℝ) - 1) / L ⟨a,p⟩
  let F := fun (v : ∀ j, IntegerScalarCubeBox α (H j)) =>
    principalTupleFlatten (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val) α
      (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)
  let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬grid a} => B a.val)
    (fun a => degree a.val) L c
  let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬grid a} => B a.val)
    (fun a => degree a.val) L H step
  let proxy := allocatedAffineLongJetProxy B U basis S x u rows s hA center width
  let density := allocatedNormalizedLongJetDensity B U basis S x u rows s hA
  let radius := Real.exp (allocatedJetSupportLog (G := G) B α O P)
  have hw (a) (p) : |tupleLower a p| + |tupleWidth a p| ≤ 1 :=
    (progression_slice_endpoint_geometry (c ⟨a,p⟩) (hL _) (hstep _) (hH _) hδ
      (hsubset _) (hdense _)).2.2.1
  have hF (v) (hv : 0 < weights.weight v) : ‖F v‖ ≤ 1 := by
    apply (principalTupleFlatten_norm_apply_le _ _ _ _).trans
    apply progressionTuple_norm_le L step H c hH (fun j => hw j.1 j.2) v
    intro j
    exact scalarCubeResidueWeights_cube_support α (H j) (M j) (by have := hH j; omega)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j) (v j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ v hv j)
  have hs (z : Jet → ℝ) (hz : radius < ‖z‖) : Δ z = 0 := by
    have hp : proxy z = 0 := allocatedAffineLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hMk hi hP hMkP hRP hRi hσi hcount u hσ1 center width
      (fun i => (principalProgressionSlice_parameters (α := α)
        (fun a : {a // ¬grid a} => B a.val) (fun a => degree a.val)
        L H step c hL hstep hH hδ hsubset hdense i).2.2) z hz
    have hd : weights.mean (fun v => density (F v) z) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      by_cases hv : weights.weight v = 0
      · simp only [hv, zero_mul]
      · have hf := allocatedNormalizedLongJetDensity_zero_off_ball B U basis hR hσ S x
          rows s hA hMk hi hP hMkP hRP hRi hσi hcount u hσ1 (F v)
          (hF v (lt_of_le_of_ne (weights.nonneg v) (Ne.symm hv))) z hz
        exact mul_eq_zero_of_right _ hf
    exact sub_eq_zero.mpr (hd.trans hp.symm)
  have hint : Integrable (fun z => weights.mean (fun v => density (F v) z)) := by
    apply integrable_finsetSum
    intro v _
    exact ((allocatedNormalizedLongJetDensity_probability B U basis hR hσ S x u
      rows s hA hσ1 (F v)).2.1).const_mul (weights.weight v)
  have hip := (allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA
    center width hσ1).2.1
  refine ⟨hint.sub hip, ?_⟩
  apply integral_norm_le_box Δ (Real.exp_nonneg _) hs
  intro z _
  exact allocatedAffineLongJetProxy_residue_error B U basis hR hσ S x u rows s hA hMk hi hP hMkP
    hRP hRi hσi hcount hσ1 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_residue_source_with_scales_oai
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_ : 0 < Mk)
        (_ : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_ : 0 ≤ P) (_ : (Mk : ℝ) ≤ Real.exp P)
        (_ : ∀ j, R j ≤ Real.exp P) (_ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_ : ∀ j, 0 < L j) (_ : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (_ : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_ : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (_ : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_ : 0 ≤ ε) (_ : ∀ j, (step j : ℝ) / L j ≤ ε),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      (∫ z, |ideal z - discrete z|) ≤ η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) := by
  have hδhalf1 : δ / 2 ≤ 1 := by linarith
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_proxy_l1_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock (half_pos hδ) hδhalf1 hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L step H M c hL hstep hH hsubset hdense modulus residue hm hmM hsize hsmall ε hε hmesh
    center width ideal discrete bound cap lip
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hg := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hcont := hs U basis hR hσ S hσsmall x u center width
    (fun i => (hg i).2.1) (fun i => (hg i).2.2) s hA
  have hdisc := allocatedAffineLongJetProxy_residue_l1 B U basis hR hσ S x u rows s hA
    hMk hi hP hMkP hRP hRi hσi hcount hσ1 L step H M c hL hstep hH hδ hsubset hdense
    modulus residue hm hmM hsize hsmall hε hmesh
  let proxy := allocatedAffineLongJetProxy B U basis S x u rows s hA center width
  have hρpos : 0 < ρ (allocatedGridAxis (I := I) U basis S.value) := hρmin.trans_le (hρ (allocatedGridAxis (I := I) U basis S.value)).1
  have hideal := activeAveragedSlicedProfileIdeal_spec (G := G) (B := B)
    (G × Option α) (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) hρpos center width
  have hIi : Integrable ideal := diagonalImageDensity_integrable
    (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1) (fun o => (hR o.1.val.1).ne') hideal.2.2.1
  have hp := (allocatedAffineLongJetProxy_probability B U basis hR hσ S x u rows s hA center width hσ1).2.1
  have hdiff : Integrable (fun z => ideal z - proxy z) := hIi.sub hp
  calc
    _ ≤ ∫ z, (|ideal z - proxy z| + |discrete z - proxy z|) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (hdiff.abs.add hdisc.1.abs)
      apply Filter.Eventually.of_forall
      intro z
      change |ideal z - discrete z| ≤ |ideal z - proxy z| + |discrete z - proxy z|
      simpa only [abs_sub_comm (proxy z) (discrete z)] using abs_sub_le (ideal z) (proxy z) (discrete z)
    _ = (∫ z, |ideal z - proxy z|) + ∫ z, |discrete z - proxy z| := integral_add hdiff.abs hdisc.1.abs
    _ ≤ _ := add_le_add hcont hdisc.2

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_residue_source_with_scales_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_residue_source_with_scales_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
