-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:45:17.887207+00:00
-- url     : https://prove2.me/submissions/cd4fd562-0ff5-4ab2-8c5c-b1129a2d92c9

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Semiconj.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A010
import Definitions.Def_OAIQ075A011
import Definitions.Def_OAIQ075A016
import Theorems.Thm_OAI_KadisonSimilarity_ScalarFree_trace_pair
import Theorems.Thm_OAI_KadisonSimilarity_arcWidth_pos
import Theorems.Thm_OAI_KadisonSimilarity_trace_centered_mul_of_free

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The centered arc, its exact second moment, and its nonzero Fourier
coefficients, computed using normalized angular Lebesgue integration. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Set

private theorem intervalIntegrable_indicator_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} {s : Set ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

private theorem integral_indicator_subinterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) :
    (∫ x in a..b, (Ioc c d).indicator f x) = ∫ x in c..d, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset, ← intervalIntegral.integral_of_le hcd]
  exact Ioc_subset_Ioc hac hdb

theorem centeredArc_integral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    (∫ x in -Real.pi..Real.pi, centeredArc θ x) = 0 := by
  simp only [centeredArc]
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of intervalIntegrable_const measurableSet_Ioc)
    intervalIntegrable_const,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- Nonzero frequency integration over a symmetric arc. -/
theorem integral_arc_exponential (θ r : ℝ) (hr : r ≠ 0) :
    (∫ x in -θ..θ, Complex.exp ((r * x : ℝ) * Complex.I)) =
      (2 * Real.sin (r * θ) / r : ℝ) := by
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp (x * Complex.I)) (a := -θ) (b := θ) hr
  rw [mul_neg, integral_exp_mul_I_eq_sin] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv, Complex.real_smul, div_eq_mul_inv, mul_comm] using h

@[simp] theorem arcFourierIntegral_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    arcFourierIntegral θ 0 = 0 := by
  simp only [arcFourierIntegral, Int.cast_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, centeredArc_integral_zero hθ hπ]
  simp

theorem arcFourierIntegral_ne_zero {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (l : ℤ) (hl : l ≠ 0) :
    arcFourierIntegral θ l = (Real.sin (l * θ) / (Real.pi * l) : ℝ) := by
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  let g : ℝ → ℂ := fun x => Complex.exp (((l : ℝ) * x : ℝ) * Complex.I)
  have hg : IntervalIntegrable g volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hid : (fun x => (centeredArc θ x : ℂ) * g x) =
      fun x => (Ioc (-θ) θ).indicator g x - (θ / Real.pi : ℝ) • g x := by
    funext x
    by_cases hx : x ∈ Ioc (-θ) θ <;>
      simp [centeredArc, hx, Complex.real_smul, sub_mul]
  unfold arcFourierIntegral
  change ((2 * Real.pi)⁻¹ : ℝ) • (∫ x in -Real.pi..Real.pi,
    (centeredArc θ x : ℂ) * g x) = _
  have hsg : IntervalIntegrable (fun x => (θ / Real.pi) • g x)
      volume (-Real.pi) Real.pi := hg.smul (θ / Real.pi)
  rw [hid, intervalIntegral.integral_sub
    (intervalIntegrable_indicator_of hg measurableSet_Ioc) hsg,
    intervalIntegral.integral_smul,
    integral_indicator_subinterval _ (by linarith [Real.pi_pos]) (by linarith)
      (by linarith) hπ]
  dsimp [g]
  rw [integral_arc_exponential _ _ hlr, integral_arc_exponential _ _ hlr,
    Real.sin_int_mul_pi]
  simp only [mul_zero, zero_div, Complex.ofReal_zero, sub_zero, ← Complex.ofReal_mul]
  congr 1
  field_simp

theorem arcFourierIntegral_eq_real {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi)
    (l : ℤ) : arcFourierIntegral θ l = (realArcFourierCoefficient θ l : ℂ) := by
  by_cases hl : l = 0
  · subst l
    simp [hθ, hπ, realArcFourierCoefficient]
  · rw [arcFourierIntegral_ne_zero hθ hπ l hl, realArcFourierCoefficient, ite_eq_right hl]

theorem realArcFourierCoefficient_pos_index {N : ℕ} {l : ℕ} (hl : 0 < l) :
    realArcFourierCoefficient (arcWidth N) l = arcCoefficient N l := by
  have h : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  simp only [realArcFourierCoefficient, ite_eq_right h, arcCoefficient, Int.cast_natCast]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact dihedral word identity and the finite Fourier matrix entries. -/

noncomputable section
namespace KadisonSimilarity

section Group
variable {G : Type*} [Group G]

/-- The reflection relation fixes the sum-index in the Hankel term. -/
theorem dihedral_word_identity (w d : G) (hd : d * w = w⁻¹ * d) (j k : ℤ) :
    w ^ j * d * w ^ (-k) = w ^ (j + k + 1) * (w⁻¹ * d) := by
  have hmove : d * w ^ (-k) = w ^ k * d := by
    have h := (show SemiconjBy d w w⁻¹ from hd).zpow_right (-k)
    simpa only [inv_zpow, zpow_neg, inv_inv] using h.eq
  calc
    _ = w ^ j * (d * w ^ (-k)) := mul_assoc _ _ _
    _ = w ^ j * (w ^ k * d) := by rw [hmove]
    _ = w ^ (j + k) * d := by rw [← mul_assoc, ← zpow_add]
    _ = w ^ (j + k + 1) * (w⁻¹ * d) := by
      rw [← mul_assoc, ← zpow_neg_one, ← zpow_add]
      congr 2
      omega

end Group

section Algebra
variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- Exact rotation-plus-reflection decomposition of the corner word. -/
theorem dihedral_corner_word (w d : Rˣ) (hd : d * w = w⁻¹ * d) (j k : ℤ) :
    (↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R) =
      (1 / 2 : ℂ) • ((↑(w ^ (j - k)) : R) +
        (↑(w ^ (j + k + 1)) : R) * (↑(w⁻¹ * d) : R)) := by
  have hrot : (↑(w ^ j) : R) * (↑(w ^ (-k)) : R) = (↑(w ^ (j - k)) : R) := by
    rw [← Units.val_mul, ← zpow_add]
    congr 1
  have href := congrArg (fun a : Rˣ => (a : R)) (dihedral_word_identity w d hd j k)
  simp only [Units.val_mul] at href
  simp only [dihedralHalfProjection, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_one, smul_add, Units.val_mul]
  rw [hrot, href]

/-- Once the two Fourier coefficient identities hold, the corner entry has
both its Toeplitz difference index and its Hankel sum-plus-one index. -/
theorem dihedral_fourier_entry
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f : R) (E : R →ₗ[ℂ] R)
    (γ : ℤ → ℂ)
    (hrot : ∀ l : ℤ, E (f * (↑(w ^ l) : R)) = γ l • (1 : R))
    (href : ∀ l : ℤ, E (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      γ l • (↑(w⁻¹ * d) : R)) (j k : ℤ) :
    E (f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R))) =
      (1 / 2 : ℂ) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  rw [dihedral_corner_word w d hd, mul_smul_comm, mul_add, ← mul_assoc,
    map_smul, map_add, hrot, href]

/-- The two coefficients of `x` and `xs` exchange when `s²=1`. -/
theorem symmetryExpectation_mul_symmetry
    (τ : R →ₗ[ℂ] ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a))
    (s x : R) (hs : s * s = 1) (hcoset : τ (s * x) = 0) :
    symmetryExpectation τ s x = τ x • 1 ∧
      symmetryExpectation τ s (x * s) = τ x • s := by
  constructor
  · simp only [symmetryExpectation_apply, hcoset, zero_smul, add_zero]
  · have hxs : τ (x * s) = 0 := (htr x s).trans hcoset
    have hconj : τ (s * (x * s)) = τ x := by
      rw [← mul_assoc, htr (s * x) s, ← mul_assoc, hs, one_mul]
    simp only [symmetryExpectation_apply, hxs, hconj, zero_smul, zero_add]

/-- Bimodularity and the tower identity transfer the free-compression
expectation to a dihedral Fourier entry. -/
theorem compressed_dihedral_fourier_entry
    (w d : Rˣ) (hd : d * w = w⁻¹ * d) (f h : R)
    (EC E₀ : R →ₗ[ℂ] R) (γ : ℤ → ℂ) (u : ℂ)
    (hEC : EC h = u ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (↑(w ^ j) : R) * EC h * (↑(w ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R))) =
        E₀ ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : R) * f = f * (↑(w ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R)) = γ l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      γ l • (↑(w⁻¹ * d) : R)) (j k : ℤ) :
    E₀ ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (u ^ 2 / 2) • (γ (j - k) • (1 : R) +
        γ (j + k + 1) • (↑(w⁻¹ * d) : R)) := by
  rw [← htower j k, hbimod, hEC, mul_smul_comm, smul_mul_assoc, map_smul]
  have hproduct : (↑(w ^ j) : R) * (f * dihedralHalfProjection d) *
      (↑(w ^ (-k)) : R) =
      f * ((↑(w ^ j) : R) * dihedralHalfProjection d * (↑(w ^ (-k)) : R)) := by
    rw [← mul_assoc (↑(w ^ j) : R) f, hcomm j]
    simp only [mul_assoc]
  rw [hproduct, dihedral_fourier_entry w d hd f E₀ γ hrot href, smul_smul]
  congr 1
  ring

/-- The normalized corner coefficient is exactly `u` when `u = 2t`. -/
theorem normalized_corner_scalar (t : ℂ) (ht : t ≠ 0) :
    t⁻¹ * ((2 * t) ^ 2 / 2) = 2 * t := by field_simp

end Algebra
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_apply _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_single _root_.OAI.KadisonSimilarity.FiniteOrthogonalColumns.unitary_symm_apply _root_.OAI.KadisonSimilarity.FullColumnCoordinates.extend_apply _root_.OAI.KadisonSimilarity.columnEntry_apply _root_.OAI.KadisonSimilarity.constantCopies_adjoint_apply _root_.OAI.KadisonSimilarity.constantCopies_apply _root_.OAI.KadisonSimilarity.copyCorner_apply _root_.OAI.KadisonSimilarity.copyEmbeddingMap_apply_image _root_.OAI.KadisonSimilarity.copyInsert_apply _root_.OAI.KadisonSimilarity.copyMatrixUnit_apply _root_.OAI.KadisonSimilarity.finiteCopyIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.l2FiniteCoordinates_apply _root_.OAI.KadisonSimilarity.mapCopies_apply _root_.OAI.KadisonSimilarity.mapCopies_sub _root_.OAI.KadisonSimilarity.matrixEntryCompression_apply _root_.OAI.KadisonSimilarity.matrixEntryCompression_matrixOperator _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_apply _root_.OAI.KadisonSimilarity.rectangularMatrixOperator_zero _root_.OAI.KadisonSimilarity.representedMatrixHom_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dense tracial vectors determine the word-level operator compression.
In particular the matrix-entry identity is proved from the trace and the
two-sided expectation identity, rather than supplied as an operator hypothesis. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [CompleteSpace K] in
/-- Matrix coefficients on any dense family determine a bounded operator. -/
theorem operator_eq_of_dense_coefficients {ι : Type*} (v : ι → K)
    (hv : DenseRange v) (A B : K →L[ℂ] K)
    (h : ∀ i j, inner ℂ (v i) (A (v j)) = inner ℂ (v i) (B (v j))) : A = B := by
  have hvec (j : ι) : A (v j) = B (v j) := by
    apply ext_inner_left ℂ
    have heq := hv.equalizer
      (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
      (funext (fun i => h i j))
    exact congrFun heq
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer A.continuous B.continuous (funext hvec))

variable {R : Type*} [Ring R] [StarRing R]

/-- Removing the supporting corner in a tracial word leaves precisely the
two Fourier powers around the test operator. -/
theorem tracial_corner_word (w : Rˣ) (hw : star w = w⁻¹)
    (e h a b : R) (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (j k : ℤ) :
    star (e * (↑(w ^ (-j)) : R) * a) *
        (h * (e * (↑(w ^ (-k)) : R) * b)) =
      star a * ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) * b := by
  rw [star_mul, star_mul, star_unitary_zpow w hw, neg_neg, he]
  calc
    _ = star a * (↑(w ^ j) : R) * (e * h * e) * (↑(w ^ (-k)) : R) * b := by
      simp only [mul_assoc]
    _ = _ := by rw [heh, hhe]; simp only [mul_assoc]

variable [Algebra ℂ R] [StarModule ℂ R]

/-- A trace-preserving bimodule projection preserves all matrix coefficients
against its range algebra. -/
theorem tracial_expectation_test (A : StarSubalgebra ℂ R)
    (τ : R →ₗ[ℂ] ℂ) (E : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E x) = τ x)
    (hbimod : ∀ (a b : A) x, E ((a : R) * x * (b : R)) =
      (a : R) * E x * (b : R)) (a b : A) (x : R) :
    τ (star (a : R) * x * (b : R)) = τ (star (a : R) * E x * (b : R)) := by
  have h := htrace (star (a : R) * x * (b : R))
  have he : E (star (a : R) * x * (b : R)) = star (a : R) * E x * (b : R) :=
    hbimod (star a) b x
  rw [he] at h
  exact h.symm

/-- Word-level compression computed from dense tracial vectors. `ρ` is the
compression of the left action to the base Hilbert space; it need only be
linear on the full algebra. -/
theorem tracial_word_compression_entry
    (A : StarSubalgebra ℂ R) (τ : R →ₗ[ℂ] ℂ)
    (V : R →ₗ[ℂ] H) (L : R →ₗ[ℂ] (H →L[ℂ] H))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (v : A → K) (hv : DenseRange v) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (v a) (ρ x (v b)) = τ (star (a : R) * x * (b : R)))
    (E : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E x) = τ x)
    (hbimod : ∀ (a b : A) x, E ((a : R) * x * (b : R)) =
      (a : R) * E x * (b : R))
    (w : Rˣ) (hw : star w = w⁻¹) (e h : R)
    (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (c q : ℂ) (hc : star c * c = q) (j k : ℤ)
    (Uj Uk : K →L[ℂ] H)
    (hUj : ∀ a : A, Uj (v a) = c • V (e * (↑(w ^ (-j)) : R) * (a : R)))
    (hUk : ∀ a : A, Uk (v a) = c • V (e * (↑(w ^ (-k)) : R) * (a : R))) :
    Uj.adjoint.comp ((L h).comp Uk) =
      q • ρ (E ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R))) := by
  apply operator_eq_of_dense_coefficients v hv
  intro a b
  change inner ℂ (v a) (Uj.adjoint (L h (Uk (v b)))) =
    inner ℂ (v a) (q • ρ (E _) (v b))
  change (starRingEnd ℂ) c * c = q at hc
  rw [ContinuousLinearMap.adjoint_inner_right, hUj, hUk, map_smul,
    inner_smul_left, inner_smul_right, hleft, hinner,
    tracial_corner_word w hw e h (a : R) (b : R) he heh hhe j k,
    tracial_expectation_test A τ E htrace hbimod a b,
    inner_smul_right, hρ, ← mul_assoc, hc]

omit [StarRing R] [StarModule ℂ R] in
/-- Once the algebraic entry calculation is known, linearity and the exact
corner normalization give the whole finite Toeplitz-plus-Hankel matrix. -/
theorem finite_dihedral_compression
    {N : ℕ} (U : Fin N → K →L[ℂ] H) (T : H →L[ℂ] H)
    (ρ : R →ₗ[ℂ] (K →L[ℂ] K)) (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (s : R) (γ : ℤ → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hentry : ∀ i j,
      (U i).adjoint.comp (T.comp (U j)) =
        t⁻¹ • ρ (((2 * t) ^ 2 / 2) •
          (γ ((i : ℕ) - (j : ℤ)) • (1 : R) +
            γ ((i : ℕ) + (j : ℤ) + 1) • s))) :
    (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      (2 * t) • matrixOperator (fun i j =>
        γ ((i : ℕ) - (j : ℤ)) • ContinuousLinearMap.id ℂ K +
          γ ((i : ℕ) + (j : ℤ) + 1) • ρ s) := by
  have he : (fun i j => (U i).adjoint.comp (T.comp (U j))) =
      fun (i j : Fin N) => (2 * t) • (γ ((i : ℕ) - (j : ℤ)) • ContinuousLinearMap.id ℂ K +
        γ ((i : ℕ) + (j : ℤ) + 1) • ρ s) := by
    funext i j
    rw [hentry, map_smul, map_add, map_smul, map_smul, hρone,
      smul_smul, normalized_corner_scalar t ht]
  rw [sumColumns_compression, he]
  ext x i
  simp [matrixOperator, Finset.smul_sum]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite narrow-arc compression, assembled from the trace calculation,
the dihedral expectation, and the actual Fourier integral. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite operator matrix identity used by the Hankel test. Every entry
comes from tracial vectors and the two expectation identities. -/
theorem narrow_arc_tracial_compression
    {N : ℕ} (hN : 0 < N)
    (A : StarSubalgebra ℂ R) (τ : R →ₗ[ℂ] ℂ)
    (V : R →ₗ[ℂ] H) (L : R →ₗ[ℂ] (H →L[ℂ] H))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (v : A → K) (hv : DenseRange v) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (v a) (ρ x (v b)) = τ (star (a : R) * x * (b : R)))
    (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (E₀ EC : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E₀ x) = τ x)
    (hbase : ∀ (a b : A) x, E₀ ((a : R) * x * (b : R)) =
      (a : R) * E₀ x * (b : R))
    (w d : Rˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (e f h : R) (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (t : ℝ) (ht : 0 < t) (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → K →L[ℂ] H)
    (hU : ∀ i (a : A), U i (v a) =
      c • V (e * (↑(w ^ (-(i.val : ℤ))) : R) * (a : R)))
    (hEC : EC h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (↑(w ^ j) : R) * EC h * (↑(w ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R))) =
        E₀ ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : R) * f = f * (↑(w ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R)) =
      arcFourierIntegral (arcWidth N) l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      arcFourierIntegral (arcWidth N) l • (↑(w⁻¹ * d) : R)) :
    (sumColumns U).adjoint.comp ((L h).comp (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ K +
        (arcHankelMatrix N i j : ℂ) • ρ (↑(w⁻¹ * d) : R)) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hentry : ∀ i j : Fin N,
      (U i).adjoint.comp ((L h).comp (U j)) =
        (t : ℂ)⁻¹ • ρ (((2 * (t : ℂ)) ^ 2 / 2) •
          (arcFourierIntegral (arcWidth N) ((i.val : ℤ) - j.val) • (1 : R) +
            arcFourierIntegral (arcWidth N) ((i.val : ℤ) + j.val + 1) •
              (↑(w⁻¹ * d) : R))) := by
    intro i j
    rw [tracial_word_compression_entry A τ V L hinner hleft v hv ρ hρ E₀ htrace hbase
      w hw e h he heh hhe c (t : ℂ)⁻¹ hc i.val j.val (U i) (U j) (hU i) (hU j),
      compressed_dihedral_fourier_entry w d hd f h EC E₀
        (arcFourierIntegral (arcWidth N)) (2 * (t : ℂ)) hEC hbimod htower hcomm hrot href]
  have hmatrix := finite_dihedral_compression U (L h) ρ hρone
    (↑(w⁻¹ * d) : R) (arcFourierIntegral (arcWidth N)) (t : ℂ) htc hentry
  have hθ : 0 ≤ arcWidth N := (arcWidth_pos hN).le
  have hπ : arcWidth N ≤ Real.pi := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwidth : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have hcoeff : ∀ i j : Fin N,
      realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) + j.val + 1) =
        arcHankelMatrix N i j := by
    intro i j
    have h := realArcFourierCoefficient_pos_index (N := N)
      (l := i.val + j.val + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, arcHankelMatrix] using h
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat,
    arcFourierIntegral_eq_real hθ hπ, hcoeff] using hmatrix

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The expectation of a free compression

Scalar tracial freeness is expressed by vanishing alternating centered words.
The formula `E(e b e) = τ(e)^2 b` is derived by testing against the second
algebra, rather than included among the free-product input data.
-/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]

namespace ScalarFree

variable {τ : R →ₗ[ℂ] ℂ} {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)

include hf in
theorem trace_triple {a b c : R} (ha : a ∈ Q) (hb : b ∈ P) (hc : c ∈ Q)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) : τ (a * b * c) = 0 := by
  have h := hf false a [b, c]
    (.cons (by simpa) ha0 (.cons (by simpa) hb0 (.cons (by simpa) hc0 (.nil true))))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

include hf in
theorem trace_quadruple {a b c d : R} (ha : a ∈ Q) (hb : b ∈ P)
    (hc : c ∈ Q) (hd : d ∈ P)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) (hd0 : τ d = 0) :
    τ (a * b * c * d) = 0 := by
  have h := hf false a [b, c, d]
    (.cons (by simpa) ha0 (.cons (by simpa) hb0
      (.cons (by simpa) hc0 (.cons (by simpa) hd0 (.nil false)))))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

end ScalarFree

/-- Orthogonality against the second algebra removes all three mixed terms
in the free-compression expansion. -/
theorem trace_test_free_compression_errors
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    {a b c : R} (ha : a ∈ P) (ha0 : τ a = 0)
    (hb : b ∈ Q) (hb0 : τ b = 0) (hc : c ∈ Q) :
    τ (c * (a * b)) = 0 ∧ τ (c * (b * a)) = 0 ∧ τ (c * (a * b * a)) = 0 := by
  have hc0 := traceCentered_trace τ hτ c
  have hcm := traceCentered_mem τ Q hc
  have hab := hf.trace_pair ha hb ha0 hb0
  have hcab := hf.trace_triple hcm ha hb hc0 ha0 hb0
  have hcaba := hf.trace_quadruple hcm ha hb ha hc0 ha0 hb0 ha0
  have hba2 : τ (b * (a * a)) = 0 := by
    rw [htr]
    -- The product a² need not be centered; center it before pairing with b.
    have hp := hf.trace_pair (traceCentered_mem τ P (P.mul_mem ha ha)) hb
      (traceCentered_trace τ hτ _) hb0
    have heq : τ ((a * a) * b) = τ (traceCentered τ (a * a) * b) := by
      rw [traceCentered, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, hb0]
      simp
    exact heq.trans hp
  have haba : τ (a * b * a) = 0 := by
    rw [htr (a * b) a]
    have ha2b : τ ((a * a) * b) = 0 := by rw [htr]; exact hba2
    simpa only [mul_assoc] using ha2b
  have hfirst : τ (c * (a * b)) = 0 := by
    rw [← traceCentered_add τ c, add_mul, smul_mul_assoc, one_mul, map_add, map_smul]
    have hcab' : τ (traceCentered τ c * (a * b)) = 0 := by
      simpa only [mul_assoc] using hcab
    rw [hcab', hab, smul_zero, add_zero]
  have hsecond : τ (c * (b * a)) = 0 := by
    rw [← mul_assoc, htr]
    exact trace_centered_mul_of_free τ hτ hf ha ha0 (Q.mul_mem hc hb)
  have hthird : τ (c * (a * b * a)) = 0 := by
    rw [← traceCentered_add τ c, add_mul, smul_mul_assoc, one_mul, map_add, map_smul]
    have hcaba' : τ (traceCentered τ c * (a * b * a)) = 0 := by
      simpa only [mul_assoc] using hcaba
    rw [hcaba', haba, smul_zero, add_zero]
  exact ⟨hfirst, hsecond, hthird⟩

/-- The expectation formula in `lem:free-compression`, proved from scalar
freeness and the defining trace-pairing property of conditional expectation.
The projection condition on `e` is not needed for this algebraic identity. -/
theorem expectation_free_compression
    (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (hfaithful : ∀ z, τ (star z * z) = 0 → z = 0)
    {P Q : StarSubalgebra ℂ R} (hf : ScalarFree τ P Q)
    (E : R →ₗ[ℂ] R) (hE : ∀ x, E x ∈ Q)
    (htrace : ∀ x c, c ∈ Q → τ (c * E x) = τ (c * x))
    {e b : R} (he : e ∈ P) (hb : b ∈ Q) (hb0 : τ b = 0) :
    E (e * b * e) = (τ e) ^ 2 • b := by
  let a := traceCentered τ e
  have ha : a ∈ P := traceCentered_mem τ P he
  have ha0 : τ a = 0 := traceCentered_trace τ hτ e
  have hexpand : e * b * e = (τ e) ^ 2 • b +
      τ e • (a * b) + τ e • (b * a) + a * b * a := by
    calc
      _ = (a + τ e • 1) * b * (a + τ e • 1) := by
        dsimp [a]
        rw [traceCentered_add]
      _ = _ := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
          one_mul, mul_one, smul_add, smul_smul, pow_two]
        abel
  apply expectation_eq_of_trace_pairings τ Q hfaithful E hE htrace _ _ (Q.smul_mem hb _)
  intro c hc
  obtain ⟨h1, h2, h3⟩ := trace_test_free_compression_errors τ hτ htr hf ha ha0 hb hb0 hc
  rw [hexpand]
  simp only [mul_add, mul_smul_comm, map_add, map_smul, h1, h2, h3,
    smul_zero, add_zero]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

theorem baseInclusion_adjoint_self :
    (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
      (G.baseInclusion A).toContinuousLinearMap = ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  have h := (G.baseInclusion A).adjoint_comp_self
  exact h

theorem baseCompression_one : G.baseCompression A 1 = ContinuousLinearMap.id ℂ (G.baseSpace A) := by
  change (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    ((G.left 1).comp (G.baseInclusion A).toContinuousLinearMap) = _
  rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    G.baseInclusion_adjoint_self]

/-- The coefficient formula required by the tracial Fourier compression. -/
theorem baseCompression_inner (a b : A) (x : P) :
    inner ℂ (G.baseVector A a) (G.baseCompression A x (G.baseVector A b)) =
      G.trace (star (a : P) * x * (b : P)) := by
  change inner ℂ (G.baseVector A a)
    ((G.baseInclusion A).toContinuousLinearMap.adjoint
      (G.left x ((G.baseInclusion A).toContinuousLinearMap (G.baseVector A b)))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (G.vector (a : P)) (G.left x (G.vector (b : P))) = _
  rw [G.left_vector, G.inner_vector, mul_assoc]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialExpectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The trace-pairing description of conditional expectation. Its uniqueness,
bimodule law, tower law, and Hilbert projection formula are derived here. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

/-- Faithfulness of the algebra-vector realization implies faithfulness of
its positive trace pairing. -/
theorem trace_faithful (G : TracialCornerGeometry P H)
    (hfaithful : Function.Injective G.vector) (x : P)
    (hx : G.trace (star x * x) = 0) : x = 0 := by
  apply hfaithful
  rw [map_zero]
  exact inner_self_eq_zero.mp (by rw [G.inner_vector, hx])

end TracialCornerGeometry

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {A : StarSubalgebra ℂ P}
  (E : TracialExpectation τ A)

/-- Expectation preserves the trace by testing its pairing with the unit. -/
theorem trace_map (x : P) : τ (E.map x) = τ x := by
  simpa only [one_mul] using E.pairing x 1 A.one_mem

variable (hf : ∀ x, τ (star x * x) = 0 → x = 0)

include hf

theorem map_of_mem {x : P} (hx : x ∈ A) : E.map x = x :=
  E.eq_of_pairings hf x x hx (fun _ _ => rfl)

@[simp] theorem map_one : E.map 1 = 1 := E.map_of_mem hf A.one_mem

@[simp] theorem map_map (x : P) : E.map (E.map x) = E.map x :=
  E.map_of_mem hf (E.range x)

theorem bimodule (htr : ∀ x y, τ (x * y) = τ (y * x))
    (a b x : P) (ha : a ∈ A) (hb : b ∈ A) :
    E.map (a * x * b) = a * E.map x * b := by
  rw [E.map_mul_right hf htr _ b hb, E.map_mul_left hf a x ha]

/-- Scalar freeness now gives the free-compression expectation formula for
this actual expectation map. -/
theorem free_compression (hτ : τ 1 = 1)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    {D : StarSubalgebra ℂ P} (hfree : ScalarFree τ D A)
    {e b : P} (he : e ∈ D) (hb : b ∈ A) (hb0 : τ b = 0) :
    E.map (e * b * e) = (τ e) ^ 2 • b :=
  expectation_free_compression τ hτ htr hf hfree E.map E.range E.pairing he hb hb0

end TracialExpectation

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (E : TracialExpectation G.trace A)

/-- Conditional expectation on algebra vectors is exactly orthogonal
projection onto the actual closed base Hilbert space. -/
theorem expectation_base_projection (x : P) :
    (G.baseInclusion A).toContinuousLinearMap.adjoint (G.vector x) =
      G.baseVector A ⟨E.map x, E.range x⟩ := by
  apply ext_inner_left ℂ
  intro y
  refine (G.baseVector_dense A).induction_on y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (G.vector (a : P)) (G.vector x) =
    inner ℂ (G.vector (a : P)) (G.vector (E.map x))
  rw [G.inner_vector, G.inner_vector]
  exact (E.pairing x (star (a : P)) (star_mem a.property)).symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ExpectationWordClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending the two-dimensional expectation range from word vectors to
their tracial Hilbert closure. Orthogonal projection supplies continuity. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The expectation of a Hilbert limit of word vectors still lies in the
span of the unit and the specified base element. -/
theorem expectation_span_of_word_closure (E : TracialExpectation G.trace A)
    (hfaithful : Function.Injective G.vector) (s : P) (words : Set P)
    (hword : ∀ x ∈ words, ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (x : P) (hx : G.vector x ∈
      (Submodule.span ℂ (G.vector '' words)).topologicalClosure) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  let F : H →L[ℂ] H := (G.baseInclusion A).toContinuousLinearMap.comp
    (G.baseInclusion A).toContinuousLinearMap.adjoint
  have hF (y : P) : F (G.vector y) = G.vector (E.map y) := by
    change (G.baseInclusion A)
      ((G.baseInclusion A).toContinuousLinearMap.adjoint (G.vector y)) = _
    rw [G.expectation_base_projection A E]
    rfl
  let B : Submodule ℂ H := Submodule.span ℂ {G.vector 1, G.vector s}
  have : FiniteDimensional ℂ B := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  have hclosed : IsClosed (B : Set H) := B.closed_of_finiteDimensional
  have hspan : Submodule.span ℂ (G.vector '' words) ≤ B.comap F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    change F (G.vector y) ∈ B
    rw [hF]
    obtain ⟨α, β, h⟩ := hword y hy
    rw [h, map_add, map_smul, map_smul]
    exact B.add_mem (B.smul_mem α (Submodule.subset_span (by simp)))
      (B.smul_mem β (Submodule.subset_span (by simp)))
  have hmem := (Submodule.span ℂ (G.vector '' words)).topologicalClosure_minimal
    hspan (hclosed.preimage F.continuous) hx
  change F (G.vector x) ∈ B at hmem
  rw [hF] at hmem
  obtain ⟨α, β, h⟩ := Submodule.mem_span_pair.mp hmem
  refine ⟨α, β, ?_⟩
  apply hfaithful
  simpa only [map_add, map_smul] using h.symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeWordExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base expectation kills every reduced word starting in the other
free factor. This is derived from scalar freeness by trace tests. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {τ : P →ₗ[ℂ] ℂ}
  {A D : StarSubalgebra ℂ P}

namespace TracialExpectation

/-- A reduced word beginning in the other factor has zero base expectation,
including when its final letter belongs to the base algebra. -/
theorem map_reduced_word (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (x : P) (xs : List P) (hword : AlternatingCenteredWord τ D A true (x :: xs)) :
    E.map ((x :: xs).prod) = 0 := by
  apply E.eq_of_pairings hfaithful _ 0 A.zero_mem
  intro c hc
  have hzero := hfree true x xs hword
  have htest : τ (traceCentered τ c * (x :: xs).prod) = 0 := by
    have h := hfree false (traceCentered τ c) (x :: xs)
      (.cons (by simpa using traceCentered_mem τ A hc)
        (traceCentered_trace τ hτ c) hword)
    exact h
  rw [mul_zero, map_zero]
  calc
    τ (c * (x :: xs).prod) =
        τ ((traceCentered τ c + τ c • 1) * (x :: xs).prod) := by
      rw [traceCentered_add]
    _ = 0 := by
      rw [add_mul, smul_mul_assoc, one_mul, map_add, map_smul, htest, hzero]
      simp

/-- A base letter at the front of such a word is removed by bimodularity. -/
theorem map_base_mul_reduced_word (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (a : P) (ha : a ∈ A) (x : P) (xs : List P)
    (hword : AlternatingCenteredWord τ D A true (x :: xs)) :
    E.map (a * (x :: xs).prod) = 0 := by
  rw [E.map_mul_left hfaithful a _ ha, E.map_reduced_word hfaithful hτ hfree x xs hword,
    mul_zero]

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerExpectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting a tracial expectation to a corner. The normalized corner
trace and the restricted expectation are constructed from the ambient ones. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CStarCorner

variable (p : P) (hp : IsStarProjection p)

theorem normalizedTrace_one (τ : P →ₗ[ℂ] ℂ) (ht : τ p ≠ 0) :
    normalizedTrace p hp τ 1 = 1 := by
  rw [normalizedTrace_apply, coe_one, inv_mul_cancel₀ ht]

theorem normalizedTrace_faithful (τ : P →ₗ[ℂ] ℂ) (ht : τ p ≠ 0)
    (hf : ∀ x, τ (star x * x) = 0 → x = 0)
    (x : CStarCorner p hp) (hx : normalizedTrace p hp τ (star x * x) = 0) :
    x = 0 := by
  apply Subtype.ext
  apply hf
  change (τ p)⁻¹ * τ (star (x : P) * (x : P)) = 0 at hx
  exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero ht)

end CStarCorner

namespace TracialExpectation

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P}
  (E : TracialExpectation τ C)
  (hf : ∀ x, τ (star x * x) = 0 → x = 0)
  (htr : ∀ x y, τ (x * y) = τ (y * x))
  (p : P) (hp : IsStarProjection p) (hpC : p ∈ C)

include hf htr in
/-- The ambient expectation formula used in the dihedral corner follows
from freeness in the normalized corner, rather than being extra data. -/
theorem free_corner_compression (ht : τ p ≠ 0)
    (D : StarSubalgebra ℂ P) (hpD : p ∈ D)
    (hfree : ScalarFree (CStarCorner.normalizedTrace p hp τ)
      (CStarCorner.subalgebra p hp D hpD) (CStarCorner.subalgebra p hp C hpC))
    (e b : CStarCorner p hp) (he : (e : P) ∈ D) (hb : (b : P) ∈ C)
    (hb0 : τ (b : P) = 0) :
    E.map ((e : P) * (b : P) * (e : P)) =
      ((τ p)⁻¹ * τ (e : P)) ^ 2 • (b : P) := by
  have h := (E.corner hf htr p hp hpC).free_compression
    (CStarCorner.normalizedTrace_faithful p hp τ ht hf)
    (CStarCorner.normalizedTrace_one p hp τ ht)
    (CStarCorner.normalizedTrace_tracial p hp τ htr) hfree (e := e) (b := b) he hb
    (by simp only [CStarCorner.normalizedTrace_apply, hb0, mul_zero])
  exact congrArg (fun x : CStarCorner p hp => (x : P)) h

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded Borel spectral calculus input, specialized to the centered
arc of a Haar rotation in a finite dihedral von Neumann algebra. Blackadar,
Operator Algebras, I.6.2.4 and I.6.2.8, supply the calculus and commutation;
integration against its Haar spectral measure gives the stated moments.

The interface is local to the specified trace and algebra. Its intended
application has the normal finite trace and the von Neumann algebra generated
by the two symmetries. No existence assertion is made for an arbitrary C-star
subalgebra or an arbitrary linear functional. The corner estimates below are
proved from the spectral data, rather than included in the published input. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace DihedralSpectralArc

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P} {w d : Pˣ} {θ : ℝ}
  (F : DihedralSpectralArc τ C w d θ)

theorem trace_zero (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ F.element = 0 := by
  have h := F.rotation_moment 0
  simpa only [zpow_zero, Units.val_one, mul_one, arcFourierIntegral_zero hθ hπ] using h

theorem rotation_commutes (l : ℤ) :
    (↑(w ^ l) : P) * F.element = F.element * (↑(w ^ l) : P) :=
  (F.commute_rotation.units_zpow_right l).eq.symm

/-- The reflection used in the Hankel term is `w⁻¹d`, rather than `d`.
Traciality shifts the Fourier index and supplies its zero mixed moment. -/
theorem shifted_reflection_moment (htr : ∀ x y, τ (x * y) = τ (y * x)) (l : ℤ) :
    τ ((↑(w⁻¹ * d) : P) * (F.element * (↑(w ^ l) : P))) = 0 := by
  have hpow : w ^ l * w⁻¹ = w ^ (l - 1) := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
  rw [htr]
  have hid : (F.element * (↑(w ^ l) : P)) * (↑(w⁻¹ * d) : P) =
      (F.element * (↑(w ^ (l - 1)) : P)) * (d : P) := by
    have hval : (↑(w ^ l) : P) * (↑w⁻¹ : P) = (↑(w ^ (l - 1)) : P) := by
      rw [← Units.val_mul, hpow]
    calc
      _ = F.element * ((↑(w ^ l) : P) * (↑w⁻¹ : P)) * (d : P) := by
        simp only [Units.val_mul, mul_assoc]
      _ = _ := by rw [hval]
  rw [hid, F.reflection_moment]

theorem corner_mem (hp : IsStarProjection (dihedralHalfProjection d))
    (hdC : (d : P) ∈ C) : (F.corner hp : P) ∈ C :=
  C.mul_mem F.mem (C.smul_mem (C.add_mem C.one_mem hdC) _)

theorem corner_trace_zero (hp : IsStarProjection (dihedralHalfProjection d))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) : τ (F.corner hp : P) = 0 := by
  have hd0 : τ (F.element * (d : P)) = 0 := by
    simpa only [zpow_zero, Units.val_one, mul_one] using F.reflection_moment 0
  simp only [corner_coe, dihedralHalfProjection, mul_smul_comm, mul_add, mul_one,
    map_smul, map_add, F.trace_zero hθ hπ, hd0, add_zero, smul_zero]

/-- The trace-pairing expectation of the actual compressed arc is derived
from normalized corner freeness. The factor `2t` is not an extra hypothesis. -/
theorem compressed_expectation
    (E : TracialExpectation τ C)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (htr : ∀ x y, τ (x * y) = τ (y * x))
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpC : dihedralHalfProjection d ∈ C)
    (D : StarSubalgebra ℂ P) (hpD : dihedralHalfProjection d ∈ D)
    (htp : τ (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp τ)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C hpC))
    (e : CStarCorner (dihedralHalfProjection d) hp) (heD : (e : P) ∈ D)
    (hdC : (d : P) ∈ C) {t : ℝ} (hte : τ (e : P) = (t : ℂ))
    (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    E.map ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) =
      (2 * (t : ℂ)) ^ 2 • (F.element * dihedralHalfProjection d) := by
  have htne : τ (dihedralHalfProjection d) ≠ 0 := by rw [htp]; norm_num
  have h := E.free_corner_compression hfaithful htr (dihedralHalfProjection d) hp hpC
    htne D hpD hfree e (F.corner hp) heD (F.corner_mem hp hdC)
    (F.corner_trace_zero hp hθ hπ)
  simpa only [F.corner_coe, htp, hte, one_div, inv_inv] using h

end DihedralSpectralArc
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryExpectation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identifying a tracial expectation whose range lies in the two-dimensional
algebra generated by a centered symmetry. The Fourier identities then require
only scalar trace moments, not operator-valued moment assumptions. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P] {τ : P →ₗ[ℂ] ℂ}
  {A : StarSubalgebra ℂ P}

namespace TracialExpectation

/-- Trace preservation and the trace pairing with s determine both
coefficients of the conditional expectation. -/
theorem map_eq_symmetryExpectation (E : TracialExpectation τ A)
    (hτ : τ 1 = 1) (s : P) (hsA : s ∈ A) (hs0 : τ s = 0) (hs2 : s * s = 1)
    (x : P) (hspan : ∃ α β : ℂ, E.map x = α • (1 : P) + β • s) :
    E.map x = symmetryExpectation τ s x := by
  obtain ⟨α, β, he⟩ := hspan
  have hα : τ x = α := by
    rw [← E.trace_map x, he, map_add, map_smul, map_smul, hτ, hs0]
    simp
  have hβ : τ (s * x) = β := by
    rw [← E.pairing x s hsA, he, mul_add, mul_smul_comm, mul_smul_comm,
      mul_one, hs2, map_add, map_smul, map_smul, hs0, hτ]
    simp
  rw [he, symmetryExpectation_apply, hα, hβ]

/-- The rotation and reflection expectation identities follow from scalar
Fourier moments once the free-word calculation puts these expectations in
span{1,s}. -/
theorem rotation_reflection_of_scalar_moments (E : TracialExpectation τ A)
    (hτ : τ 1 = 1) (htr : ∀ x y, τ (x * y) = τ (y * x))
    (s : P) (hsA : s ∈ A) (hs0 : τ s = 0) (hs2 : s * s = 1)
    (x : P) (γ : ℂ) (hcoef : τ x = γ) (hcoset : τ (s * x) = 0)
    (hspan : ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (hspan' : ∃ α β : ℂ, E.map (x * s) = α • (1 : P) + β • s) :
    E.map x = γ • (1 : P) ∧ E.map (x * s) = γ • s := by
  rw [E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 x hspan,
    E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 (x * s) hspan']
  simpa only [hcoef] using symmetryExpectation_mul_symmetry τ htr s x hs2 hcoset

/-- On the word algebra, a two-dimensional base expectation factors through
any intermediate algebra containing the symmetry. No global tower inclusion
of the entire base algebra is required. -/
theorem restricted_tower_of_symmetry_span (E : TracialExpectation τ A)
    {C S : StarSubalgebra ℂ P} (EC : TracialExpectation τ C) (hCS : C ≤ S)
    (hτ : τ 1 = 1) (s : P) (hsA : s ∈ A) (hsC : s ∈ C)
    (hs0 : τ s = 0) (hs2 : s * s = 1)
    (hspan : ∀ x, x ∈ S → ∃ α β : ℂ, E.map x = α • (1 : P) + β • s)
    (x : P) (hx : x ∈ S) : E.map (EC.map x) = E.map x := by
  rw [E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 _ (hspan _ (hCS (EC.range x))),
    E.map_eq_symmetryExpectation hτ s hsA hs0 hs2 x (hspan x hx)]
  simp only [symmetryExpectation_apply, EC.trace_map, EC.pairing x s hsC]

end TracialExpectation
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The base expectation on the algebra generated by the other free factor
and one centered symmetry. The only density datum is the ordinary reduced
word span; the two-dimensional expectation range is proved. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace CenteredSymmetryWord

variable {τ : P →ₗ[ℂ] ℂ} {D A : StarSubalgebra ℂ P} {s : P}

theorem alternating (hs : s ∈ A) (hs0 : τ s = 0)
    {side : Bool} {xs : List P} (h : CenteredSymmetryWord τ D s side xs) :
    AlternatingCenteredWord τ D A side xs := by
  induction h with
  | nil side => exact .nil side
  | other hd hz _ ih => exact .cons (by simpa using hd) hz ih
  | symmetry _ ih => exact .cons (by simpa using hs) hs0 ih

/-- The expectation of a reduced word is either zero, the unit, or the
specified symmetry. This follows from freeness and bimodularity. -/
theorem expectation_span
    (E : TracialExpectation τ A)
    (hfaithful : ∀ x, τ (star x * x) = 0 → x = 0)
    (hτ : τ 1 = 1) (hfree : ScalarFree τ D A)
    (hs : s ∈ A) (hs0 : τ s = 0)
    {side : Bool} {xs : List P} (h : CenteredSymmetryWord τ D s side xs) :
    ∃ α β : ℂ, E.map xs.prod = α • (1 : P) + β • s := by
  cases h with
  | nil side =>
    refine ⟨1, 0, ?_⟩
    simp only [List.prod_nil, E.map_one hfaithful, one_smul, zero_smul, add_zero]
  | @other d xs hd hz tail =>
    refine ⟨0, 0, ?_⟩
    have hw : AlternatingCenteredWord τ D A true (d :: xs) :=
      .cons (by simpa using hd) hz (tail.alternating hs hs0)
    rw [E.map_reduced_word hfaithful hτ hfree d xs hw]
    simp
  | @symmetry xs tail =>
    cases tail with
    | nil =>
      refine ⟨0, 1, ?_⟩
      simp only [List.prod_cons, List.prod_nil, mul_one,
        E.map_of_mem hfaithful hs, zero_smul, one_smul, zero_add]
    | @other d ys hd hz tail =>
      refine ⟨0, 0, ?_⟩
      have hw : AlternatingCenteredWord τ D A true (d :: ys) :=
        .cons (by simpa using hd) hz (tail.alternating hs hs0)
      change E.map (s * (d :: ys).prod) = _
      rw [E.map_base_mul_reduced_word hfaithful hτ hfree s hs d ys hw]
      simp

end CenteredSymmetryWord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D S : StarSubalgebra ℂ P)

/-- Passage from the actual reduced words to their L² closure supplies the
word-algebra range hypothesis of the Fourier compression. -/
theorem expectation_span_of_symmetry_word_density
    (E : TracialExpectation G.trace A) (hfaithful : Function.Injective G.vector)
    (hτ : G.trace 1 = 1) (hfree : ScalarFree G.trace D A)
    (s : P) (hs : s ∈ A) (hs0 : G.trace s = 0)
    (hdense : ∀ x, x ∈ S → G.vector x ∈
      (Submodule.span ℂ (G.vector '' centeredSymmetryWordProducts G.trace D s)).topologicalClosure)
    (x : P) (hx : x ∈ S) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  apply G.expectation_span_of_word_closure A E hfaithful s
    (centeredSymmetryWordProducts G.trace D s) _ x (hdense x hx)
  rintro y ⟨side, xs, hw, rfl⟩
  exact hw.expectation_span E (G.trace_faithful hfaithful) hτ hfree hs hs0

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SymmetryWordAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic normal forms for the algebra generated by a star subalgebra
and a symmetry. Centering the other-factor letters and cancelling adjacent
symmetries proves the reduced-word density used by the base expectation. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace SymmetryWordAlgebra

variable (τ : P →ₗ[ℂ] ℂ) (D : StarSubalgebra ℂ P) (s : P)

variable (hτ : τ 1 = 1)

variable (hsq : s * s = 1)

variable (hstar : star s = s)

theorem generated_le_span :
    StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) ≤ spanStarAlgebra τ D s hτ hsq hstar := by
  apply StarAlgebra.adjoin_le
  rintro x (hx | hx)
  · exact other_mem τ D s hτ x hx
  · exact Set.mem_singleton_iff.mp hx ▸ symmetry_mem τ D s

end SymmetryWordAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem symmetry_word_density_of_generated_density
    (D : StarSubalgebra ℂ P) (s : P) (hτ : G.trace 1 = 1)
    (hsq : s * s = 1) (hstar : star s = s) (x : P)
    (hx : G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))).topologicalClosure) :
    G.vector x ∈ (Submodule.span ℂ
      (G.vector '' centeredSymmetryWordProducts G.trace D s)).topologicalClosure := by
  apply Submodule.topologicalClosure_mono (s := Submodule.span ℂ
    (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))) _ hx
  apply Submodule.span_le.mpr
  rintro y ⟨a, ha, rfl⟩
  have hmem := SymmetryWordAlgebra.generated_le_span G.trace D s hτ hsq hstar ha
  change a ∈ Submodule.span ℂ (centeredSymmetryWordProducts G.trace D s) at hmem
  clear ha
  induction hmem using Submodule.span_induction with
  | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

/-- The base expectation of the actual generated von Neumann algebra has
the range needed in the Fourier argument. Only ordinary generated-algebra
L² density remains, rather than an assumed range formula. -/
theorem expectation_span_of_generated_symmetry_algebra
    (A D S : StarSubalgebra ℂ P) (E : TracialExpectation G.trace A)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (hfree : ScalarFree G.trace D A) (s : P) (hs : s ∈ A)
    (hs0 : G.trace s = 0) (hsq : s * s = 1) (hstar : star s = s)
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {s}) : Set P))).topologicalClosure)
    (x : P) (hx : x ∈ S) :
    ∃ α β : ℂ, E.map x = α • (1 : P) + β • s := by
  apply G.expectation_span_of_symmetry_word_density A D S E hf hτ hfree s hs hs0 _ x hx
  intro y hy
  exact G.symmetry_word_density_of_generated_density D s hτ hsq hstar y (hdense y hy)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Fourier matrix with the actual base compression and actual
trace-pairing expectations. Only scalar moments of the arc remain as data. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Scalar Fourier moments and the expectation range on the tested word
algebra determine the finite operator matrix on the actual tracial base. -/
theorem arc_compression_of_scalar_moments
    (E : TracialExpectation G.trace A) {C S : StarSubalgebra ℂ P}
    (EC : TracialExpectation G.trace C) (hCS : C ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hspan : ∀ x, x ∈ S → ∃ α β : ℂ,
      E.map x = α • (1 : P) + β • (↑(w⁻¹ * d) : P))
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (e f h : P) (hestar : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (hfC : f ∈ C) (hhS : h ∈ S)
    {N : ℕ} (hN : 0 < N) (t : ℝ) (ht : 0 < t) (c : ℂ)
    (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector (e * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P)))
    (hEC : EC.map h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : P) * f = f * (↑(w ^ j) : P))
    (hcoef : ∀ l : ℤ, G.trace (f * (↑(w ^ l) : P)) =
      arcFourierIntegral (arcWidth N) l)
    (hcoset : ∀ l : ℤ,
      G.trace ((↑(w⁻¹ * d) : P) * (f * (↑(w ^ l) : P))) = 0) :
    (sumColumns U).adjoint.comp ((G.left h).comp (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  have hfaithful := G.trace_faithful hf
  have hrotref (l : ℤ) := E.rotation_reflection_of_scalar_moments hτ G.tracial
    (↑(w⁻¹ * d) : P) hsA hs0 hs2 (f * (↑(w ^ l) : P))
    (arcFourierIntegral (arcWidth N) l) (hcoef l) (hcoset l)
    (hspan _ (hCS (C.mul_mem hfC (hpower l))))
    (hspan _ (hCS (C.mul_mem (C.mul_mem hfC (hpower l)) hsC)))
  apply narrow_arc_tracial_compression hN A G.trace G.vector G.left.toLinearMap
    G.inner_vector G.left_vector (G.baseVector A) (G.baseVector_dense A)
    (G.baseCompression A) (G.baseCompression_inner A) (G.baseCompression_one A)
    E.map EC.map E.trace_map (fun a b x => E.bimodule hfaithful G.tracial
      (a : P) (b : P) x a.property b.property)
    w d hw hd e f h hestar heh hhe t ht c hc U hU hEC
  · intro j k
    exact EC.bimodule hfaithful G.tracial _ _ h (hpower j) (hpower (-k))
  · intro j k
    exact E.restricted_tower_of_symmetry_span EC hCS hτ _ hsA hsC hs0 hs2 hspan _
      (S.mul_mem (S.mul_mem (hCS (hpower j)) hhS) (hCS (hpower (-k))))
  · exact hcomm
  · exact fun l => (hrotref l).1
  · exact fun l => (hrotref l).2

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialSpectralCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerAlgebra _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral-arc compression matrix. The normalized corner
expectation and the shifted reflection moment are derived here, leaving no
operator-valued Fourier identity among the hypotheses. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem spectral_arc_compression_oai
    (A C D S : StarSubalgebra ℂ P)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCS : C ≤ S) (hDS : D ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (hfreeDA : ScalarFree G.trace D A)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hdC : (d : P) ∈ C)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hsstar : star (↑(w⁻¹ * d) : P) = (↑(w⁻¹ * d) : P))
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(↑(w⁻¹ * d) : P)}):
        Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpD : dihedralHalfProjection d ∈ D)
    (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C
        (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
    (e : CStarCorner (dihedralHalfProjection d) hp)
    (he : IsStarProjection (e : P)) (heD : (e : P) ∈ D)
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C w d (arcWidth N))
    (t : ℝ) (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector ((e : P) * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P))) :
    (sumColumns U).adjoint.comp
      ((G.left ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))).comp
        (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  have hpC : dihedralHalfProjection d ∈ C :=
    C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2)
  have hspan := G.expectation_span_of_generated_symmetry_algebra A D S E hf hτ hfreeDA
    (↑(w⁻¹ * d) : P) hsA hs0 hs2 hsstar hdense
  have hwidth : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsmall : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have heh : (e : P) * ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) =
      (e : P) * (F.element * dihedralHalfProjection d) * (e : P) := by
    simp only [← mul_assoc, he.isIdempotentElem.eq]
  have hhe : ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) * (e : P) =
      (e : P) * (F.element * dihedralHalfProjection d) * (e : P) := by
    rw [mul_assoc, he.isIdempotentElem.eq]
  exact G.arc_compression_of_scalar_moments A E EC hCS hf hτ w d hw hd hsA hsC hs0 hs2
    hspan hpower (e : P) F.element
    ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))
    he.isSelfAdjoint.star_eq heh hhe F.mem
    (S.mul_mem (S.mul_mem (hDS heD) (hCS (C.mul_mem F.mem hpC))) (hDS heD))
    hN t ht c hc U hU
    (F.compressed_expectation EC (G.trace_faithful hf) G.tracial hp hpC D hpD htp
      hfree e heD hdC hte (arcWidth_pos hN).le hwidth)
    F.rotation_commutes F.rotation_moment (F.shifted_reflection_moment G.tracial)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.spectral_arc_compression_oai.{u_1, u_2}
