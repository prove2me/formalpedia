-- Prove2me | solution 1 for OAI.KaplanskyConsequences.actualAlgebra_no_tracialState
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:50:55.158075+00:00
-- url     : https://prove2.me/submissions/8d5992d6-41d3-4cfb-a27c-532fdc831b0f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf010

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Products
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The coordinate column identities give the actual product identity. -/
theorem boundedProduct_column {N : ℕ} (x : Fin N → ∀ i, A i)
    (hx : ∀ k i, ‖x k i‖ ≤ 1)
    (hcol : ∀ i, ∑ k, star (x k i) * x k i = 1) :
    ∑ k, star (boundedProductLift (x k) (hx k)) * boundedProductLift (x k) (hx k) =
      (1 : BoundedProduct A) := by
  ext i
  rw [boundedProduct_sum_apply]
  change (∑ k, star (x k i) * x k i) = 1
  exact hcol i

theorem boundedProduct_row {N : ℕ} (x : Fin N → ∀ i, A i)
    (hx : ∀ k i, ‖x k i‖ ≤ 1) (c : ℝ)
    (hrow : ∀ i, ∑ k, x k i * star (x k i) ≤ (c : ℂ) • (1 : A i)) :
    ∑ k, boundedProductLift (x k) (hx k) * star (boundedProductLift (x k) (hx k)) ≤
      (c : ℂ) • (1 : BoundedProduct A) := by
  apply (boundedProduct_le_iff _ _).mpr
  intro i
  rw [boundedProduct_sum_apply]
  change (∑ k, x k i * star (x k i)) ≤ (c : ℂ) • (1 : A i)
  exact hrow i

end Kaplansky

end

noncomputable section
open TopologicalSpace
open scoped Pointwise
namespace Kaplansky

/-- Countably many letters have only countably many finite multiplicative words. -/
theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A}
    (hs : s.Countable) : (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := inferInstanceAs (Countable (List s))
  rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
  exact Set.countable_range _

variable {A : Type*} [CStarAlgebra A]

theorem generatedAlgebra_separable {s : Set A} (hs : s.Countable) :
    SeparableSpace (generatedAlgebra s) := by
  have hstar : (star s).Countable := by
    convert hs.image star using 1
    all_goals try with_reducible_and_instances rfl
    ext a
    simp
  have hw := countable_monoid_closure (hs.union hstar)
  have hspan := hw.isSeparable.span (R := ℂ)
  rw [← StarAlgebra.adjoin_eq_span] at hspan
  have hc := hspan.closure
  exact hc.separableSpace

instance finiteGeneratedAlgebra_separable {N : ℕ} (x : Fin N → A) :
    SeparableSpace (generatedAlgebra (Set.range x)) :=
  generatedAlgebra_separable (Set.countable_range x)

end Kaplansky

end

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder
attribute [local instance] CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

attribute [local instance] OAI.Kaplansky.closedSubalgebraLE
attribute [local instance] OAI.Kaplansky.closedSubalgebraPreorder
/-- Closed C*-subalgebras reflect positivity. The square-root witness
belongs to the subalgebra by continuous functional calculus. -/
theorem closedSubalgebra_nonneg_iff (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (a : S) : 0 ≤ a ↔ 0 ≤ (a : A) := by
  constructor
  · intro h
    obtain ⟨x,rfl⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := a)).mp h
    exact star_mul_self_nonneg (x : A)
  · intro h
    have hmem : CFC.sqrt (a : A) ∈ S := by
      rw [CFC.sqrt_eq_real_sqrt _ h]
      exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
    let b : S := ⟨CFC.sqrt (a : A),hmem⟩
    apply (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := a)).mpr
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change (a : A) = star (CFC.sqrt (a : A)) * CFC.sqrt (a : A)
    rw [(CFC.sqrt_nonneg (a : A)).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ h]

theorem closedSubalgebra_le_iff (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (a b : S) : a ≤ b ↔ (a : A) ≤ (b : A) := by
  rw [← sub_nonneg, closedSubalgebra_nonneg_iff]
  exact sub_nonneg

theorem generatedGenerator_column {N : ℕ} (x : Fin N → A)
    (hx : ∑ k, star (x k) * x k = 1) :
    ∑ k, star (generatedGenerator x k) * generatedGenerator x k = 1 := by
  apply Subtype.ext
  change (generatedAlgebra (Set.range x)).subtype
      (∑ k, star (generatedGenerator x k) * generatedGenerator x k) = _
  rw [map_sum]
  exact hx

theorem generatedGenerator_row {N : ℕ} (x : Fin N → A) (c : ℝ)
    (hx : ∑ k, x k * star (x k) ≤ (c : ℂ) • (1 : A)) :
    ∑ k, generatedGenerator x k * star (generatedGenerator x k) ≤ (c : ℂ) • 1 := by
  apply (closedSubalgebra_le_iff _ _ _).mpr
  change (generatedAlgebra (Set.range x)).subtype
      (∑ k, generatedGenerator x k * star (generatedGenerator x k)) ≤ _
  rw [map_sum]
  exact hx

theorem bounded_generated_relations {I : Type*} {A : I → Type*}
    [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
    {N : ℕ} (x : Fin N → ∀ i, A i) (hx : ∀ k i, ‖x k i‖ ≤ 1)
    (c : ℝ) (hcol : ∀ i, ∑ k, star (x k i) * x k i = 1)
    (hrow : ∀ i, ∑ k, x k i * star (x k i) ≤ (c : ℂ) • (1 : A i)) :
    let y := fun k => boundedProductLift (x k) (hx k)
    let z := generatedGenerator y
    (∑ k, star (z k) * z k = 1) ∧ (∑ k, z k * star (z k) ≤ (c : ℂ) • 1) := by
  dsimp only
  exact ⟨generatedGenerator_column _ (boundedProduct_column x hx hcol),
    generatedGenerator_row _ c (boundedProduct_row x hx c hrow)⟩

end Kaplansky

end

noncomputable section
namespace Kaplansky

/-- The closed generated algebra contains the ambient unit and is
nontrivial whenever the ambient algebra is nontrivial. -/
theorem generatedAlgebra_nontrivial {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (s : Set A) : Nontrivial (generatedAlgebra s) := by
  infer_instance

theorem boundedGeneratedAlgebra_nontrivial {I : Type*} [Nonempty I] {A : I → Type*}
    [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] {N : ℕ}
    (x : Fin N → ∀ i, A i) (hx : ∀ k i, ‖x k i‖ ≤ 1) :
    Nontrivial (generatedAlgebra (Set.range (fun k => boundedProductLift (x k) (hx k)))) := by
  let : Nontrivial (BoundedProduct A) := boundedProduct_nontrivial
  exact generatedAlgebra_nontrivial _

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Shift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)]

variable [∀ j, CompleteSpace (E j)]

theorem forwardShift_single (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (j : ℕ) (v : E j) : forwardShift T hT (lp.single 2 j v) =
      lp.single 2 (j+1) (T j v) := by
  have he : lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v) =
      lp.single 2 j (T j v) := by
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]
  change successorInclusion (lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v)) = _
  rw [he]
  exact OrthogonalFamily.linearIsometry_apply_single _ _

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]

/-- A forward shift has zero output in degree zero. -/
theorem forwardShift_apply_zero (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) : forwardShift T hT f 0 = 0 := by
  have he : (lp.evalCLM ℂ E 2 0).comp (forwardShift T hT) = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro j
    ext v
    change forwardShift T hT (lp.single 2 j v) 0 = 0
    rw [forwardShift_single]
    simp
  exact DFunLike.congr_fun he f

/-- On degree j+1, the forward shift is exactly its j-th block. -/
theorem forwardShift_apply_succ (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) : forwardShift T hT f (j+1) = T j (f j) := by
  have he : (lp.evalCLM ℂ E 2 (j+1)).comp (forwardShift T hT) =
      (T j).comp (lp.evalCLM ℂ E 2 j) := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    ext v
    change forwardShift T hT (lp.single 2 k v) (j+1) = T j (lp.single 2 k v j)
    rw [forwardShift_single]
    by_cases hk : j = k
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (show j+1 ≠ k+1 by omega)]
  exact DFunLike.congr_fun he f

/-- The adjoint lowers degree, using the adjoint of the actual block. -/
theorem forwardShift_adjoint_apply (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) :
    (forwardShift T hT).adjoint f j = (T j).adjoint (f (j+1)) := by
  apply ext_inner_left ℂ
  intro v
  rw [← lp.inner_single_left j v, ContinuousLinearMap.adjoint_inner_right,
    forwardShift_single, lp.inner_single_left, ContinuousLinearMap.adjoint_inner_right]

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal ComplexOrder
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]
variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1))
  (hT : ∀ i j, ‖T i j‖ ≤ 1)

theorem forwardShift_column
    (hcol : ∀ j, ∑ i, (T i j).adjoint.comp (T i j) = ContinuousLinearMap.id ℂ (E j)) :
    ∑ i, (forwardShift (T i) (hT i)).adjoint * forwardShift (T i) (hT i) = 1 := by
  ext f j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_adjoint_apply, forwardShift_apply_succ]
  simpa using DFunLike.congr_fun (hcol j) (f j)

theorem forwardShift_row_zero (f : FiberHilbertSum E) :
    (∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f 0 = 0 := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_apply_zero, Finset.sum_const_zero]

theorem forwardShift_row_succ (f : FiberHilbertSum E) (j : ℕ) :
    (∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f (j+1) =
      (∑ i, (T i j).comp (T i j).adjoint) (f (j+1)) := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_apply_succ, forwardShift_adjoint_apply,
    ContinuousLinearMap.comp_apply]

theorem forwardShift_row_positive (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ j, ((c : ℂ) • ContinuousLinearMap.id ℂ (E (j+1)) -
      ∑ i, (T i j).comp (T i j).adjoint).IsPositive) :
    ((c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) -
      ∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro f
  suffices hn : 0 ≤ inner ℂ (((c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) -
      ∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f) f by
    rcases RCLike.nonneg_iff.mp hn with ⟨hre,him⟩
    exact ⟨Complex.ext rfl him.symm, hre⟩
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro j
  cases j with
  | zero =>
      simp only [sub_apply, smul_apply,
        one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        forwardShift_row_zero, sub_zero, inner_smul_left]
      exact mul_nonneg (by simpa using hc) (by rw [inner_self_eq_norm_sq_to_K]; positivity)
  | succ j =>
      simpa only [sub_apply, smul_apply,
        one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        forwardShift_row_succ, ContinuousLinearMap.id_apply] using
          (hrow j).inner_nonneg_left (f (j+1))

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Words
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky.NormalizedHermitianTuple
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

local instance instCompleteSpace_r53a7bc_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
attribute [local instance] OAI.Kaplansky.NormalizedHermitianTuple.instCompleteSpace_1
theorem operator_row (T : NormalizedHermitianTuple E F) :
    ((2/3 : ℂ) • ContinuousLinearMap.id ℂ F -
      ∑ i, (T.operator i).comp (T.operator i).adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro w
  simp_rw [operator_adjoint]
  let A : F →ₗ[ℂ] F := (2/3 : ℂ) • LinearMap.id - ∑ i, (T.forward i).comp (T.reverse i)
  have h : 0 ≤ inner ℂ w (A w) := T.row w
  rcases RCLike.nonneg_iff.mp h with ⟨hre,him⟩
  change (inner ℂ w (A w)).im = 0 at him
  have he : inner ℂ (A w) w = inner ℂ w (A w) := by
    rw [← inner_conj_symm]
    apply Complex.ext
    · rfl
    · change -(inner ℂ w (A w)).im = (inner ℂ w (A w)).im
      rw [him,neg_zero]
  change (↑((inner ℂ (A w) w).re) = inner ℂ (A w) w) ∧ 0 ≤ (inner ℂ (A w) w).re
  rw [he]
  exact ⟨Complex.ext rfl him.symm,hre⟩

end Kaplansky.NormalizedHermitianTuple

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_ShiftAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generated Hilbert-shift algebra and its concrete realization. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Hilbert-space positivity gives an actual square-root factorization. -/
theorem operator_positive_square {a : H →L[ℂ] H} (ha : a.IsPositive) :
    ∃ b : H →L[ℂ] H, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr ha)

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

/-- Connect the ordinary operator order to the spectral order of the
bounded-product checkpoint. -/
theorem operator_positive_spectral {a : H →L[ℂ] H} (ha : a.IsPositive) : 0 ≤ a := by
  obtain ⟨b,rfl⟩ := operator_positive_square ha
  exact star_mul_self_nonneg b

variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]
variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ i j, ‖T i j‖ ≤ 1)

theorem forwardShift_row_spectral (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ j, ((c : ℂ) • ContinuousLinearMap.id ℂ (E (j+1)) -
      ∑ i, (T i j).comp (T i j).adjoint).IsPositive) :
    ∑ i, forwardShift (T i) (hT i) * star (forwardShift (T i) (hT i)) ≤
      (c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) := by
  exact sub_nonneg.mp (operator_positive_spectral (forwardShift_row_positive T hT c hc hrow))

theorem hilbertShift_generated_relations {I : Type*} {G : I → ℕ → Type*}
    [∀ z j, NormedAddCommGroup (G z j)] [∀ z j, InnerProductSpace ℂ (G z j)]
    [∀ z j, CompleteSpace (G z j)] [∀ z, Nontrivial (FiberHilbertSum (G z))]
    (X : Fin n → ∀ z j, G z j →L[ℂ] G z (j+1)) (hX : ∀ i z j, ‖X i z j‖ ≤ 1)
    (c : ℝ) (hc : 0 ≤ c)
    (hcol : ∀ z j, ∑ i, (X i z j).adjoint.comp (X i z j) = ContinuousLinearMap.id ℂ (G z j))
    (hrow : ∀ z j, ((c : ℂ) • ContinuousLinearMap.id ℂ (G z (j+1)) -
      ∑ i, (X i z j).comp (X i z j).adjoint).IsPositive) :
    let x := fun i z => forwardShift (X i z) (hX i z)
    let y := fun i => boundedProductLift (x i) (fun z => forwardShift_norm_le (X i z) (hX i z))
    let b := generatedGenerator y
    (∑ i, star (b i) * b i = 1) ∧ (∑ i, b i * star (b i) ≤ (c : ℂ) • 1) := by
  exact bounded_generated_relations _ (fun i z => forwardShift_norm_le (X i z) (hX i z)) c
    (fun z => forwardShift_column (fun i => X i z) (fun i => hX i z) (hcol z))
    (fun z => forwardShift_row_spectral (fun i => X i z) (fun i => hX i z) c hc (hrow z))

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

attribute [local instance] fiberHilbertSum_nontrivial

theorem source_shift_algebra {I : Type*} [Nonempty I] {G : I → ℕ → Type*}
    [∀ z j, NormedAddCommGroup (G z j)] [∀ z j, InnerProductSpace ℂ (G z j)]
    [∀ z j, CompleteSpace (G z j)] [∀ z, Nontrivial (G z 0)] {n : ℕ}
    (X : Fin n → ∀ z j, G z j →L[ℂ] G z (j+1))
    (hcol : ∀ z j, ∑ i, (X i z j).adjoint.comp (X i z j) = ContinuousLinearMap.id ℂ (G z j))
    (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ z j, ((c : ℂ) • ContinuousLinearMap.id ℂ (G z (j+1)) -
      ∑ i, (X i z j).comp (X i z j).adjoint).IsPositive) :
    let hX := fun i z j => block_norm_le_of_column (fun k => X k z j) (hcol z j) i
    let x := fun i z => forwardShift (X i z) (hX i z)
    let y := fun i => boundedProductLift (x i) (fun z => forwardShift_norm_le (X i z) (hX i z))
    let B := generatedAlgebra (Set.range y)
    let b := generatedGenerator y
    Nontrivial B ∧ TopologicalSpace.SeparableSpace B ∧
      (∑ i, star (b i) * b i = 1) ∧ (∑ i, b i * star (b i) ≤ (c : ℂ) • 1) := by
  let : ∀ z, Nontrivial (FiberHilbertSum (G z)) := fun z => fiberHilbertSum_nontrivial
  dsimp only
  refine ⟨boundedGeneratedAlgebra_nontrivial _ _, inferInstance, ?_⟩
  exact hilbertShift_generated_relations X _ c hc hcol hrow

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete test operators, their C-star algebra, and its faithful representation. -/

open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

theorem actualTestOperator_column (z : ActualTestIndex) (j : ℕ) :
    ∑ i, (actualTestOperator i z j).adjoint.comp (actualTestOperator i z j) =
      ContinuousLinearMap.id ℂ (ActualTestFiber z j) :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_column
    exact h

theorem actualTestOperator_row (z : ActualTestIndex) (j : ℕ) :
    ((2/3 : ℂ) • ContinuousLinearMap.id ℂ (ActualTestFiber z (j+1)) -
      ∑ i, (actualTestOperator i z j).comp (actualTestOperator i z j).adjoint).IsPositive :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_row
    exact h

open scoped BigOperators

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

theorem actual_test_shift_algebra :
    Nontrivial ActualAlgebra ∧ TopologicalSpace.SeparableSpace ActualAlgebra ∧
      (∑ i, star (generatedGenerator actualBoundedGenerator i) *
        generatedGenerator actualBoundedGenerator i = 1) ∧
      (∑ i, generatedGenerator actualBoundedGenerator i *
        star (generatedGenerator actualBoundedGenerator i) ≤ (2/3 : ℂ) • 1) := by
  have hrow : ∀ z j, ((((2/3 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ActualTestFiber z (j+1))) -
      ∑ i, (actualTestOperator i z j).comp (actualTestOperator i z j).adjoint).IsPositive := by
    intro z j
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using actualTestOperator_row z j
  have h := source_shift_algebra actualTestOperator actualTestOperator_column (2/3)
    (by norm_num) hrow
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
  exact h


theorem actualAlgebra_nontrivial_separable :
    Nontrivial ActualAlgebra ∧ TopologicalSpace.SeparableSpace ActualAlgebra := by
  have h := actual_test_shift_algebra
  exact ⟨h.1,h.2.1⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_Extraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KaplanskyConsequences
open scoped BigOperators ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem no_tracialState_of_finite_obstruction {n : ℕ} (y : Fin n → A)
    (hcol : ∑ i, star (y i) * y i = 1)
    (hrow : ‖∑ i, y i * star (y i)‖ < 1) : IsEmpty (TracialState A) := by
  refine ⟨fun τ => ?_⟩
  have heq : τ.functional (∑ i, y i * star (y i)) = 1 := by
    calc
      τ.functional (∑ i, y i * star (y i)) =
          ∑ i, τ.functional (y i * star (y i)) := map_sum _ _ _
      _ = ∑ i, τ.functional (star (y i) * y i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact τ.tracial _ _
      _ = τ.functional (∑ i, star (y i) * y i) := (map_sum _ _ _).symm
      _ = 1 := by rw [hcol, τ.normalized]
  have hpos : 0 ≤ ∑ i, y i * star (y i) := by
    exact Finset.sum_nonneg fun i _ => mul_star_self_nonneg (y i)
  have hbound := τ.functional.norm_apply_le_of_nonneg _ hpos
  rw [heq, τ.normalized, norm_one, one_mul] at hbound
  exact (not_le_of_gt hrow) hbound

end KaplanskyConsequences

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_TraceFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences


open Kaplansky SpectralKernel
open scoped BigOperators ComplexOrder
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

lemma no_tracialState_of_twoThirds {A : Type*} [CStarAlgebra A] [Nontrivial A] {n : ℕ}
    (y : Fin n → A) (hcol : ∑ i, star (y i)*y i = 1)
    (hrow : ∑ i, y i*star (y i) ≤ (2/3 : ℂ) • (1 : A)) :
    IsEmpty (TracialState A) := by
  apply no_tracialState_of_finite_obstruction y hcol
  have hpos : 0 ≤ ∑ i, y i*star (y i) := Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
  apply lt_of_le_of_lt (CStarAlgebra.norm_le_norm_of_le_of_nonneg hrow hpos)
  calc
    ‖(2/3 : ℂ) • (1 : A)‖ = ‖(2/3 : ℂ)‖ * ‖(1 : A)‖ := norm_smul _ _
    _ ≤ ‖(2/3 : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left (le_of_eq (norm_one (α := A))) (norm_nonneg _)
    _ < 1 := by norm_num [Complex.norm_div]

theorem actualAlgebra_no_tracialState_oai : IsEmpty (TracialState ActualAlgebra) := by
  have := actualAlgebra_nontrivial_separable.1
  apply no_tracialState_of_twoThirds (generatedGenerator actualBoundedGenerator)
  · exact actual_test_shift_algebra.2.2.1
  · exact actual_test_shift_algebra.2.2.2


end KaplanskyConsequences

end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.actualAlgebra_no_tracialState_oai := @OAI.KaplanskyConsequences.actualAlgebra_no_tracialState_oai
