-- Prove2me | solution 1 for OAI.Kaplansky.kaplansky_quasitrace_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:52:17.848867+00:00
-- url     : https://prove2.me/submissions/56f17f08-f445-4b9b-80ec-4c90442c1327

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyQuasitrace
import Definitions.Def_OAIQ4Kq011
import Theorems.Thm_OAI_Kaplansky_mainTarget_of_actualDefectQuasitrace

section
-- module Solutions.OAIQ4_Kq.Cuntz_State
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Dimension states of the Cuntz monoid and positivity. -/

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace CuntzDimensionState

theorem value_le_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.value a ≤ a.size := (d.value_mono a.le_unit).trans_eq (d.value_unit a.size)

end CuntzDimensionState
end Kaplansky

open scoped Matrix CStarAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Regularization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Regularized dimensions, cutoff calculus, and topological regularization. -/

open scoped Matrix CStarAlgebra Topology

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace CuntzDimensionState

theorem regularized_le_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularized a ≤ a.size := (d.regularized_le_value a).trans (d.value_le_size a)

end CuntzDimensionState

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Distribution
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral distributions, integrals, and scalar covariance. -/

open scoped Matrix CStarAlgebra
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem cuntzCutoff_one_of_lt {t : ℝ} (ht : t < 1) :
    cuntzCutoff (1 : A) t = (1 - t) • (1 : A) := by
  have h := cfc_algebraMap (A := A) (1 : ℝ) (fun x : ℝ => max (x - t) 0)
  simpa only [cuntzCutoff, map_one, max_eq_left (sub_nonneg.mpr ht.le),
    Algebra.algebraMap_eq_smul_one] using h

namespace CuntzDimensionState

theorem distribution_le_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) (t : ℝ) :
    d.distribution a t ≤ a.size := d.regularized_le_size _

theorem spectralValue_le_norm_mul_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.spectralValue a ≤ ‖CStarMatrix.ofMatrix a.matrix‖ * a.size := by
  have h := intervalIntegral.integral_mono_on (norm_nonneg (CStarMatrix.ofMatrix a.matrix))
    (d.distribution_intervalIntegrable a 0 _) intervalIntegrable_const
    (fun t _ => d.distribution_le_size a t)
  simpa only [spectralValue, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h


/-- A normalized dimension state forces the underlying algebra to be nonzero. -/
theorem nontrivial (d : CuntzDimensionState A) : Nontrivial A := by
  rcases subsingleton_or_nontrivial A with h | h
  · let := h
    have he := d.regularized_of_matrix_eq_zero (.unit 1) (Subsingleton.elim _ _)
    rw [d.regularized_unit] at he
    norm_num at he
  · exact h

theorem distribution_unit_of_lt (d : CuntzDimensionState A) (n : ℕ) {t : ℝ} (ht : t < 1) :
    d.distribution (.unit n) t = (n : ℝ) := by
  have hp : 0 < 1-t := sub_pos.mpr ht
  have he := cuntzCutoff_one_of_lt (A := CStarMatrix (Fin n) (Fin n) A) ht
  rw [← d.regularized_unit n]
  apply d.regularized_eq
  change CuntzEquivalent (CStarMatrix.ofMatrix.symm
    (cuntzCutoff (1 : CStarMatrix (Fin n) (Fin n) A) t)) (1 : Matrix (Fin n) (Fin n) A)
  rw [he]
  exact cuntzEquivalent_pos_smul 1 hp

/-- The finite spectral integral has exactly the required matrix-unit values. -/
theorem spectralValue_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.spectralValue (.unit n) = (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    have h := d.spectralValue_le_norm_mul_size (.unit 0)
    have hp := d.spectralValue_nonneg (.unit 0)
    change d.spectralValue (.unit 0) ≤ ‖CStarMatrix.ofMatrix (CuntzPositiveMatrix.unit (A := A) 0).matrix‖ * ((0 : ℕ) : ℝ) at h
    rw [Nat.cast_zero, mul_zero] at h
    simpa only [Nat.cast_zero] using le_antisymm h hp
  · let := d.nontrivial
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    change (∫ t in (0 : ℝ)..‖(1 : CStarMatrix (Fin n) (Fin n) A)‖,
      d.distribution (.unit n) t) = _
    rw [norm_one]
    have he := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (f := d.distribution (.unit n)) (g := fun _ : ℝ => (n : ℝ))
      (fun t ht => d.distribution_unit_of_lt n ht.2)
    simpa using he

end CuntzDimensionState

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral candidates on squares, orthogonal elements, and complex elements. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace CuntzDimensionState

theorem complexValue_one (d : CuntzDimensionState A) (n : ℕ) :
    d.complexValue (1 : CStarMatrix (Fin n) (Fin n) A) = (n : ℂ) := by
  rw [d.complexValue_of_nonneg zero_le_one]
  change (d.spectralValue (.unit n) : ℂ) = _
  rw [d.spectralValue_unit]
  norm_cast

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Cuntz_Quasitrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Corner-compatible spectral quasitraces and nonunital abelian complex linearity. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {A : Type*} [CStarAlgebra A]

theorem spectralCorner_posPart {n : ℕ} (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    (corner i a)⁺ = corner i a⁺ := by
  exact ((spectralCornerHom (A := A) i).map_cfcₙ (fun t : ℝ => t⁺) a
    (ha := ha) (hφa := corner_selfAdjoint i ha)).symm

theorem spectralCorner_negPart {n : ℕ} (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    (corner i a)⁻ = corner i a⁻ := by
  exact ((spectralCornerHom (A := A) i).map_cfcₙ (fun t : ℝ => t⁻) a
    (ha := ha) (hφa := corner_selfAdjoint i ha)).symm

theorem spectralCorner_realPart {n : ℕ} (i : Fin n) (a : A) :
    (ℜ (corner i a) : CStarMatrix (Fin n) (Fin n) A) = corner i (ℜ a : A) :=
  (map_realPart (spectralCornerHom (A := A) i) a).symm

theorem spectralCorner_imaginaryPart {n : ℕ} (i : Fin n) (a : A) :
    (ℑ (corner i a) : CStarMatrix (Fin n) (Fin n) A) = corner i (ℑ a : A) :=
  (map_imaginaryPart (spectralCornerHom (A := A) i) a).symm

/-- A single rectangular entry implements equality of spectral values between
any positive corner and its one-by-one matrix. -/
theorem CuntzDimensionState.positiveValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) {a : A} (ha : 0 ≤ a) :
    d.positiveValue (corner i a) (corner_nonneg i ha) =
      d.positiveValue (corner (0 : Fin 1) a) (corner_nonneg _ ha) := by
  let S := CFC.sqrt a
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  let x : Matrix (Fin n) (Fin 1) A := Matrix.single i 0 S
  have hx : x*x.conjTranspose = CStarMatrix.ofMatrix.symm (corner i a) := by
    dsimp only [x]
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
    change Matrix.single i i (S*star S) = Matrix.single i i a
    rw [hS, CFC.sqrt_mul_sqrt_self a ha]
  have hy : x.conjTranspose*x = CStarMatrix.ofMatrix.symm (corner (0 : Fin 1) a) := by
    dsimp only [x]
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
    change Matrix.single 0 0 (star S*S) = Matrix.single 0 0 a
    rw [hS, CFC.sqrt_mul_sqrt_self a ha]
  have hp : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose) := by rw [hx]; exact corner_nonneg i ha
  have hq : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x) := by rw [hy]; exact corner_nonneg _ ha
  simpa only [hx, hy, positiveValue] using d.spectralValue_rectangular_gram x hp hq

theorem CuntzDimensionState.signedValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    d.signedValue (corner i a) = d.signedValue (corner (0 : Fin 1) a) := by
  simp only [signedValue, spectralCorner_posPart i ha, spectralCorner_negPart i ha,
    spectralCorner_posPart (0 : Fin 1) ha, spectralCorner_negPart (0 : Fin 1) ha,
    d.positiveValue_corner i (CFC.posPart_nonneg a), d.positiveValue_corner i (CFC.negPart_nonneg a)]

/-- Whole-algebra corner compatibility for the same stabilized construction. -/
theorem CuntzDimensionState.complexValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) (a : A) :
    d.complexValue (corner i a) = d.complexValue (corner (0 : Fin 1) a) := by
  simp only [complexValue, spectralCorner_realPart, spectralCorner_imaginaryPart,
    d.signedValue_corner i (ℜ a).property, d.signedValue_corner i (ℑ a).property]

namespace CuntzDimensionState

theorem baseValue_one (d : CuntzDimensionState A) : d.baseValue (1 : A) = 1 := by
  unfold baseValue
  have hc : corner (0 : Fin 1) (1 : A) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [corner, entry]
  rw [hc, d.complexValue_one]
  norm_num

theorem spectralCandidate_corner (d : CuntzDimensionState A) (a : A) :
    d.spectralCandidate.2 (upperLeft a) = d.spectralCandidate.1 a := by
  change d.complexValue (upperLeft a) = d.baseValue a
  rw [upperLeft_eq_corner]
  exact d.complexValue_corner (0 : Fin 2) a

theorem normalizedTwoQuasitrace_of_spectral_linearity (d : CuntzDimensionState A)
    (hlin : ∀ S : NonUnitalStarSubalgebra ℂ A, IsClosed (S : Set A) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x)
    (hlin2 : ∀ S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) A),
      IsClosed (S : Set (CStarMatrix (Fin 2) (Fin 2) A)) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.complexValue (x : CStarMatrix (Fin 2) (Fin 2) A)) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo := by
  let σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A) := {
    toFun := d.complexValue
    square_nonneg := d.complexValue_square_nonneg
    square_swap := d.complexValue_square_swap
    real_imag := d.complexValue_real_imag
    abelian_linear := hlin2 }
  exact ⟨d.oneQuasitraceOfSpectralCandidate hlin, d.baseValue_one,
    σ, d.spectralCandidate_corner⟩

/-- The exact abelian-linearity axiom for the fixed matrix spectral candidate. -/
theorem complexValue_abelian_linear (d : CuntzDimensionState A) (n : ℕ)
    (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin n) (Fin n) A))
    (hS : IsClosed (S : Set (CStarMatrix (Fin n) (Fin n) A)))
    (hcomm : ∀ x y : S, x*y=y*x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.complexValue (x : CStarMatrix (Fin n) (Fin n) A) := by
  let : IsClosed (S : Set (CStarMatrix (Fin n) (Fin n) A)) := hS
  let : NonUnitalCommCStarAlgebra S := { (inferInstance : NonUnitalCStarAlgebra S) with mul_comm := hcomm }
  exact ⟨d.nonunitalCommutativeValueLinearMap (NonUnitalStarSubalgebraClass.subtype S),
    fun x => d.nonunitalCommutativeValueLinearMap_apply _ x⟩

/-- The same axiom at size one, expressed on the original coefficient algebra. -/
theorem baseValue_abelian_linear (d : CuntzDimensionState A)
    (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hcomm : ∀ x y : S, x*y=y*x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x := by
  let : IsClosed (S : Set A) := hS
  let : NonUnitalCommCStarAlgebra S := { (inferInstance : NonUnitalCStarAlgebra S) with mul_comm := hcomm }
  let φ := (spectralCornerHom (A := A) (0 : Fin 1)).comp (NonUnitalStarSubalgebraClass.subtype S)
  exact ⟨d.nonunitalCommutativeValueLinearMap φ,
    fun x => d.nonunitalCommutativeValueLinearMap_apply φ x⟩

/-- A normalized two-quasitrace from a dimension state, with both original
abelian-linearity premises now discharged for the SAME spectral construction. -/
theorem normalizedTwoQuasitrace_exists (d : CuntzDimensionState A) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo :=
  d.normalizedTwoQuasitrace_of_spectral_linearity d.baseValue_abelian_linear
    (d.complexValue_abelian_linear 2)

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence of a normalized two-quasitrace on the actual M48 algebra and a fixed positive contraction pair with universal real defect at least 1/144. -/

section

noncomputable section
namespace Kaplansky

theorem actual_normalizedTwoQuasitrace_exists :
    ∃ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized ∧ τ.IsTwo :=
  actualCuntzDimensionState.normalizedTwoQuasitrace_exists

theorem kaplansky_quasitrace_counterexample_oai : MainTarget :=
  mainTarget_of_actualDefectQuasitrace actual_normalizedTwoQuasitrace_exists

end Kaplansky

end
end

end OAI
end

theorem solution : type_of% @OAI.Kaplansky.kaplansky_quasitrace_counterexample_oai := @OAI.Kaplansky.kaplansky_quasitrace_counterexample_oai
