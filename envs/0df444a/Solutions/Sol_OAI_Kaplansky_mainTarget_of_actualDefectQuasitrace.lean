-- Prove2me | solution 1 for OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:52:19.045979+00:00
-- url     : https://prove2.me/submissions/796c1b6b-4a45-4c01-a8b6-3913b51b8b94

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyQuasitrace
import Definitions.Def_OAIQ4Kq011

section
-- module Solutions.OAIQ4_Kq.Kaplansky_Shift
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
-- module Solutions.OAIQ4_Kq.Kaplansky_Words
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

local instance instCompleteSpace_r186616_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
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
-- module Solutions.OAIQ4_Kq.Kaplansky_Products
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

/-- Positivity in the bounded product is equivalent to coordinatewise
positivity. Boundedness of the adjoint-square witnesses is proved. -/
theorem boundedProduct_nonneg_iff (f : BoundedProduct A) :
    0 ≤ f ↔ ∀ i, 0 ≤ f i := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (BoundedProduct A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (BoundedProduct A) := CStarAlgebra.instNonnegSpectrumClass'
  constructor
  · intro h
    obtain ⟨x,rfl⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := f)).mp h
    intro i
    exact star_mul_self_nonneg (x i)
  · intro h
    choose x hx using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (h i)
    obtain ⟨C,hC⟩ := f.property.bddAbove
    have hb (i : I) : ‖x i‖ ≤ |C|+1 := by
      have hi : ‖x i‖ * ‖x i‖ ≤ C := by
        rw [← CStarRing.norm_star_mul_self, ← hx i]
        exact hC ⟨i,rfl⟩
      have hnorm := norm_nonneg (x i)
      have hCa := le_abs_self C
      have hC0 := abs_nonneg C
      nlinarith
    let g : BoundedProduct A := ⟨x, memℓp_infty ⟨|C|+1, by rintro _ ⟨i,rfl⟩; exact hb i⟩⟩
    apply (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := f)).mpr
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact funext hx

theorem boundedProduct_le_iff (f g : BoundedProduct A) : f ≤ g ↔ ∀ i, f i ≤ g i := by
  rw [← sub_nonneg, boundedProduct_nonneg_iff]
  exact forall_congr' (fun i => sub_nonneg)

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

/-- A nonempty family of nontrivial coordinate algebras has a nontrivial
bounded product. Nonemptiness is explicit; an empty product is excluded. -/
theorem boundedProduct_nontrivial {I : Type*} [Nonempty I] {A : I → Type*}
    [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] : Nontrivial (BoundedProduct A) := by
  let i : I := Classical.arbitrary I
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  have he := congrArg (fun f : BoundedProduct A => f i) h
  exact zero_ne_one he

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
-- module Solutions.OAIQ4_Kq.Kaplansky_ShiftAlgebra
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
-- module Solutions.OAIQ4_Kq.Kaplansky_TestAlgebra
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
-- module Solutions.OAIQ4_Kq.Quasitrace_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive square-symmetric quasitraces with complex linearity on closed nonunital abelian subalgebras. -/

section

noncomputable section
open scoped ComplexOrder IsMulCommutative

namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

/-- The closed unital abelian case follows from the actual nonunital axiom. -/
theorem OneQuasitrace.linearOn (τ : OneQuasitrace A)
    (S : StarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hcomm : ∀ x y : S, x * y = y * x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = τ x := by
  exact τ.abelian_linear S.toNonUnitalStarSubalgebra hS hcomm

namespace OneQuasitrace

variable (τ : OneQuasitrace A)

theorem map_smul_of_mem (S : StarSubalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (hcomm : ∀ x y : S, x * y = y * x)
    (c : ℂ) {a : A} (ha : a ∈ S) : τ (c • a) = c * τ a := by
  obtain ⟨f, hf⟩ := τ.linearOn S hS hcomm
  exact (hf (c • (⟨a, ha⟩ : S))).symm.trans
    ((f.map_smul c ⟨a, ha⟩).trans (congrArg (c * ·) (hf _)))

@[simp] theorem map_zero : τ 0 = 0 := by
  let S := StarAlgebra.elemental ℂ (0 : A)
  obtain ⟨f, hf⟩ := τ.linearOn S (StarAlgebra.elemental.isClosed ℂ 0)
    (fun x y => mul_comm x y)
  exact (hf 0).symm.trans f.map_zero

theorem map_smul_selfAdjoint (c : ℂ) {a : A} (ha : IsSelfAdjoint a) :
    τ (c • a) = c * τ a := by
  let := ha.isStarNormal
  exact τ.map_smul_of_mem (StarAlgebra.elemental ℂ a)
    (StarAlgebra.elemental.isClosed ℂ a) (fun x y => mul_comm x y) c
    (StarAlgebra.elemental.self_mem ℂ a)

/-- Abelian linearity applied to the closed star algebra generated by a
commuting family of self-adjoint elements. -/
theorem linearOn_hull (s : Set A) (hsa : ∀ a ∈ s, IsSelfAdjoint a)
    (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∃ f : (StarAlgebra.adjoin ℂ s).topologicalClosure →ₗ[ℂ] ℂ,
      ∀ x, f x = τ x := by
  have := StarAlgebra.isMulCommutative_adjoin ℂ
    (fun element helement other hother => hc element helement other hother)
    (by
      intro element helement other hother
      rw [(hsa other hother).star_eq]
      exact hc element helement other hother)
  have hs : ∀ x y : (StarAlgebra.adjoin ℂ s).toSubalgebra, x * y = y * x := fun x y => mul_comm x y
  letI := Subalgebra.commSemiringTopologicalClosure (StarAlgebra.adjoin ℂ s).toSubalgebra hs
  have key : ∀ a b : (StarAlgebra.adjoin ℂ s).toSubalgebra.topologicalClosure, a * b = b * a :=
    fun a b => mul_comm a b
  exact τ.linearOn _ (StarSubalgebra.isClosed_topologicalClosure _)
    (fun a b => key a b)

/-- Only commuting self-adjoint pairs are added here. -/
theorem map_add {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hc : Commute a b) : τ (a + b) = τ a + τ b := by
  obtain ⟨f, hf⟩ := τ.linearOn_hull {a,b}
    (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption)
    (by intro x hx y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exact hc.eq
        · exact hc.eq.symm
        · rfl)
  have ha' : a ∈ (StarAlgebra.adjoin ℂ ({a,b} : Set A)).topologicalClosure :=
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (by simp))
  have hb' : b ∈ (StarAlgebra.adjoin ℂ ({a,b} : Set A)).topologicalClosure :=
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (by simp))
  exact (hf (⟨a, ha'⟩ + ⟨b, hb'⟩)).symm.trans
    ((f.map_add ⟨a, ha'⟩ ⟨b, hb'⟩).trans (congrArg₂ (· + ·) (hf _) (hf _)))

theorem map_neg {a : A} (ha : IsSelfAdjoint a) : τ (-a) = -τ a := by
  simpa using τ.map_smul_selfAdjoint (-1) ha

theorem map_sub {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hc : Commute a b) : τ (a - b) = τ a - τ b := by
  simpa [sub_eq_add_neg, τ.map_neg hb] using τ.map_add ha hb.neg hc.neg_right

/-- Finite additivity is derived only for pairwise commuting self-adjoints. -/
theorem map_sum {ι : Type*} (s : Finset ι) (f : ι → A)
    (hsa : ∀ i ∈ s, IsSelfAdjoint (f i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (f j)) :
    τ (∑ i ∈ s, f i) = ∑ i ∈ s, τ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : IsSelfAdjoint (∑ i ∈ s, f i) := by
      change star (∑ i ∈ s, f i) = ∑ i ∈ s, f i
      rw [star_sum]
      exact Finset.sum_congr rfl (fun i hi => (hsa i (Finset.mem_insert_of_mem hi)).star_eq)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      τ.map_add (hsa a (Finset.mem_insert_self a s)) hs
        (Commute.sum_right s f (f a) (fun i hi =>
          hc a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hsa i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]

end OneQuasitrace
end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Order
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Order preservation and pointwise bounds for normalized quasitraces. -/

section

noncomputable section
open scoped ComplexOrder
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Positivity on all positive elements follows from the square axiom. -/
theorem OneQuasitrace.map_nonneg (τ : OneQuasitrace A) {a : A} (ha : 0 ≤ a) :
    0 ≤ τ a := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact τ.square_nonneg x

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Matrix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner-compatible two-quasitraces on the usual CStarMatrix algebra and the fixed-pair counterexample proposition. -/

section

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

theorem corner_commute {i j : n} (hij : i ≠ j) (a b : A) :
    Commute (corner i a) (corner j b) := by
  change Matrix.single i i a * Matrix.single j j b = Matrix.single j j b * Matrix.single i i a
  rw [Matrix.single_mul_single_of_ne a i i j hij b,
    Matrix.single_mul_single_of_ne b j j i hij.symm a]

theorem diagonal_eq_sum (a : n → A) : diagonal a = ∑ i, corner i (a i) := by
  change Matrix.diagonal a = ∑ i, Matrix.single i i (a i)
  exact (Matrix.sum_single_eq_diagonal a).symm

theorem corner_square_swap (τ : OneQuasitrace (CStarMatrix n n A)) (i : n) (x : A) :
    τ (corner i (star x*x)) = τ (corner i (x*star x)) := by
  simpa using τ.square_swap (corner i x)

theorem corner_square_equal (τ : OneQuasitrace (CStarMatrix n n A)) (i j : n) (x : A) :
    τ (corner i (star x*x)) = τ (corner j (star x*x)) := by
  have h := τ.square_swap (entry i j x)
  simp only [entry_star, entry_mul] at h
  exact (corner_square_swap τ i x).trans h.symm

theorem map_diagonal (τ : OneQuasitrace (CStarMatrix n n A)) (a : n → A)
    (ha : ∀ i, IsSelfAdjoint (a i)) :
    τ (diagonal a) = ∑ i, τ (corner i (a i)) := by
  rw [diagonal_eq_sum]
  apply τ.map_sum
  · intro i _; exact corner_selfAdjoint i (ha i)
  · intro i _ j _
    by_cases hij : i = j
    · subst j; exact Commute.refl _
    · exact corner_commute hij _ _

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Extension
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix order and the normalization of genuine corner extensions. -/

section

noncomputable section
open scoped ComplexOrder BigOperators CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

theorem diagonal_nonneg (a : n → A) (ha : ∀ i, 0 ≤ a i) : 0 ≤ diagonal a := by
  rw [diagonal_eq_sum]
  exact Finset.sum_nonneg (fun i _ => corner_nonneg i (ha i))

theorem diagonal_positiveContraction (a : n → A) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, a i ≤ 1) : PositiveContraction (diagonal a) := by
  have hpos := diagonal_nonneg a ha
  choose x hx using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (ha i)
  refine ⟨⟨diagonal x, ?_⟩, ?_⟩
  · change Matrix.diagonal a = (Matrix.diagonal x).conjTranspose * Matrix.diagonal x
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    exact funext hx
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos]
  apply sub_nonneg.mp
  have h := diagonal_nonneg (fun i => 1 - a i) (fun i => sub_nonneg.mpr (hb i))
  change 0 ≤ diagonal ((fun _ => (1 : A)) - a) at h
  rw [diagonal_sub, diagonal_one] at h
  exact h

theorem corner_positive_equal (τ : OneQuasitrace (CStarMatrix n n A)) (i j : n)
    {a : A} (ha : 0 ≤ a) : τ (corner i a) = τ (corner j a) := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact corner_square_equal τ i j x

theorem map_positive_diagonal (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    (a : n → A) (ha : ∀ i, 0 ≤ a i) :
    τ (diagonal a) = ∑ i, τ (corner k (a i)) := by
  rw [map_diagonal τ a (fun i => (ha i).isSelfAdjoint)]
  exact Finset.sum_congr rfl (fun i _ => corner_positive_equal τ i k (ha i))

theorem corner_normalization (τ : OneQuasitrace (CStarMatrix n n A))
    (hτ : τ.Normalized) (k : n) : (Fintype.card n : ℂ) * τ (corner k (1 : A)) = 1 := by
  have h := map_positive_diagonal τ k (fun _ => (1 : A)) (fun _ => zero_le_one)
  change τ 1 = 1 at hτ
  simpa only [diagonal_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hτ] using h.symm

/-- Scalar translation uses the corner identity, not the ambient unit. -/
theorem corner_scalar_sub (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    (c : ℝ) {a : A} (ha : IsSelfAdjoint a) :
    τ (corner k ((c : ℂ) • (1 : A) - a)) =
      (c : ℂ) * τ (corner k (1 : A)) - τ (corner k a) := by
  rw [corner_sub, corner_smul]
  have h1 := corner_selfAdjoint k (IsSelfAdjoint.one A)
  have hc : IsSelfAdjoint ((c : ℂ) • corner k (1 : A)) := by
    change star ((c : ℂ) • corner k (1 : A)) = _
    simp [star_smul, h1.star_eq]
  have hcomm : Commute ((c : ℂ) • corner k (1 : A)) (corner k a) := by
    change ((c : ℂ) • corner k (1 : A)) * corner k a = _
    simp [smul_mul_assoc, mul_smul_comm]
  rw [τ.map_sub hc (corner_selfAdjoint k ha) hcomm,
    τ.map_smul_selfAdjoint (c : ℂ) h1]

theorem corner_scalar_upper_bound (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    (c : ℝ) {a : A} (ha : 0 ≤ a) (hca : a ≤ (c : ℂ) • (1 : A)) :
    (τ (corner k a)).re ≤ c * (τ (corner k (1 : A))).re := by
  have h := τ.map_nonneg (corner_nonneg k (sub_nonneg.mpr hca))
  rw [corner_scalar_sub τ k c ha.isSelfAdjoint] at h
  have hr : 0 ≤ ((c : ℂ) * τ (corner k (1 : A)) - τ (corner k a)).re := h.1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  linarith

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Quasitrace_Defect
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed positive contraction pair and its uniform real additivity defect. -/

section

namespace Kaplansky
open scoped BigOperators

theorem defect_telescoping (H J u v : ℕ → ℂ) (N : ℕ)
    (h0 : H 0 = 0) (j0 : J 0 = 0) (huv : ∀ i < N, u i = v i) :
    (∑ i ∈ Finset.range N,
      ((H (i+1) - H i - u i) + (-J (i+1) + J i + v i))) = H N - J N := by
  induction N with
  | zero => simp [h0,j0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => huv i (Nat.lt_succ_of_lt hi)),
      huv N (Nat.lt_succ_self N)]
    ring

theorem defect_constant : ((1 : ℝ) - 2/3) / (2*24) = 1/144 := by norm_num

end Kaplansky

end

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem partialSum_succ (f : ℕ → A) (i : ℕ) :
    partialSum f (i+1) = partialSum f i + f i := Finset.sum_range_succ f i

theorem partialSum_nonneg (f : ℕ → A) (hf : ∀ i, 0 ≤ f i) (i : ℕ) :
    0 ≤ partialSum f i := Finset.sum_nonneg (fun j _ => hf j)

theorem partialSum_mono (f : ℕ → A) (hf : ∀ i, 0 ≤ f i) {i j : ℕ} (hij : i ≤ j) :
    partialSum f i ≤ partialSum f j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
  intro k _ _; exact hf k

theorem term_le_partialSum (f : ℕ → A) (hf : ∀ i, 0 ≤ f i) {i N : ℕ} (hi : i < N) :
    f i ≤ partialSum f N := by
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_range.mpr hi)

theorem defect_entries_bounds (x : ℕ → A) (N : ℕ)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ 1) :
    (∀ i, 0 ≤ defectAEntries x N i ∧ defectAEntries x N i ≤ 1) ∧
    (∀ i, 0 ≤ defectBEntries x N i ∧ defectBEntries x N i ≤ 1) := by
  have hu : ∀ i, 0 ≤ leftSquare x i := fun i => star_mul_self_nonneg (x i)
  have hv : ∀ i, 0 ≤ rightSquare x i := fun i => mul_star_self_nonneg (x i)
  constructor
  · intro i; cases i with
    | inl i =>
      exact ⟨partialSum_nonneg _ hu _,
        (partialSum_mono _ hu (Nat.le_of_lt i.isLt)).trans_eq hcol⟩
    | inr i =>
      exact ⟨sub_nonneg.mpr ((partialSum_mono _ hv (Nat.le_of_lt i.isLt)).trans hrow),
        sub_le_self _ (partialSum_nonneg _ hv _)⟩
  · intro i; cases i with
    | inl i => exact ⟨hu _, (term_le_partialSum _ hu i.isLt).trans_eq hcol⟩
    | inr i => exact ⟨sub_nonneg.mpr ((term_le_partialSum _ hv i.isLt).trans hrow),
        sub_le_self _ (hv _)⟩

/-- Positivity and the C*-norm contraction condition for the actual pair. -/
theorem defect_pair_positiveContractions (x : ℕ → A) (N : ℕ)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ 1) :
    PositiveContraction (defectA x N) ∧ PositiveContraction (defectB x N) := by
  obtain ⟨ha, hb⟩ := defect_entries_bounds x N hcol hrow
  exact ⟨diagonal_positiveContraction _ (fun i => (ha i).1) (fun i => (ha i).2),
    diagonal_positiveContraction _ (fun i => (hb i).1) (fun i => (hb i).2)⟩

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A n : Type*} [CStarAlgebra A] [Fintype n] [DecidableEq n]

theorem reflected_defect (τ : OneQuasitrace (CStarMatrix n n A)) (k : n)
    {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    τ (corner k ((1-a)+(1-b))) - τ (corner k (1-a)) - τ (corner k (1-b)) =
      -τ (corner k (a+b)) + τ (corner k a) + τ (corner k b) := by
  have heq : (1-a)+(1-b) = ((2 : ℝ) : ℂ) • (1 : A) - (a+b) := by
    rw [show ((2 : ℝ) : ℂ) = 1+1 by norm_num, add_smul, one_smul]
    abel
  have ha1 : τ (corner k (1-a)) = τ (corner k (1 : A)) - τ (corner k a) := by
    simpa only [Complex.ofReal_one, one_smul, one_mul] using corner_scalar_sub τ k 1 ha
  have hb1 : τ (corner k (1-b)) = τ (corner k (1 : A)) - τ (corner k b) := by
    simpa only [Complex.ofReal_one, one_smul, one_mul] using corner_scalar_sub τ k 1 hb
  rw [heq, corner_scalar_sub τ k 2 (ha.add hb), ha1, hb1]
  norm_num
  ring

theorem defect_pair_identity (x : ℕ → A) (N : ℕ)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ 1)
    (τ : OneQuasitrace (CStarMatrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) A))
    (k : Fin N ⊕ Fin N) :
    τ (defectA x N + defectB x N) - τ (defectA x N) - τ (defectB x N) =
      τ (corner k (1 : A)) - τ (corner k (partialSum (rightSquare x) N)) := by
  obtain ⟨ha,hb⟩ := defect_entries_bounds x N hcol hrow
  have hsum := map_positive_diagonal τ k (defectAEntries x N + defectBEntries x N)
    (fun i => add_nonneg (ha i).1 (hb i).1)
  have hA := map_positive_diagonal τ k (defectAEntries x N) (fun i => (ha i).1)
  have hB := map_positive_diagonal τ k (defectBEntries x N) (fun i => (hb i).1)
  change τ (diagonal (defectAEntries x N) + diagonal (defectBEntries x N)) -
    τ (diagonal (defectAEntries x N)) - τ (diagonal (defectBEntries x N)) = _
  rw [← diagonal_add, hsum, hA, hB, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [Fintype.sum_sum_type]
  simp only [defectAEntries, defectBEntries, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]
  have hreflect (i : Fin N) := reflected_defect τ k (b := rightSquare x i.val)
    ((partialSum_nonneg (rightSquare x) (fun j => mul_star_self_nonneg (x j)) i.val).isSelfAdjoint)
    (IsSelfAdjoint.mul_star_self (x i.val))
  simp_rw [hreflect]
  rw [← Finset.sum_add_distrib]
  have htel := defect_telescoping
    (fun i => τ (corner k (partialSum (leftSquare x) i)))
    (fun i => τ (corner k (partialSum (rightSquare x) i)))
    (fun i => τ (corner k (leftSquare x i)))
    (fun i => τ (corner k (rightSquare x i))) N
    (by simp) (by simp) (fun i _ => corner_square_swap τ k (x i))
  rw [← Fin.sum_univ_eq_sum_range] at htel
  simpa only [partialSum_succ, hcol] using htel

end Kaplansky

end
end

section

noncomputable section
open scoped BigOperators ComplexOrder CStarAlgebra
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem scalar_unit_le_one {c : ℝ} (hc : c ≤ 1) : (c : ℂ) • (1 : A) ≤ 1 := by
  simpa only [Complex.coe_smul, one_smul] using
    (smul_le_smul_of_nonneg_right hc (show (0 : A) ≤ 1 from zero_le_one))

theorem uniform_defect (x : ℕ → A) (N : ℕ) (hN : 0 < N) (c : ℝ)
    (_hc0 : 0 ≤ c) (hc : c < 1)
    (hcol : partialSum (leftSquare x) N = 1)
    (hrow : partialSum (rightSquare x) N ≤ (c : ℂ) • (1 : A)) :
    PositiveContraction (defectA x N) ∧ PositiveContraction (defectB x N) ∧
    ∀ τ : OneQuasitrace (CStarMatrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) A),
      τ.Normalized → (1-c) / (2*N) ≤
        (τ (defectA x N + defectB x N) - τ (defectA x N) - τ (defectB x N)).re := by
  have hr1 := hrow.trans (scalar_unit_le_one hc.le)
  obtain ⟨ha,hb⟩ := defect_pair_positiveContractions x N hcol hr1
  refine ⟨ha,hb,?_⟩
  intro τ hτ
  let k : Fin N ⊕ Fin N := Sum.inl ⟨0,hN⟩
  rw [defect_pair_identity x N hcol hr1 τ k, Complex.sub_re]
  have hnorm := congrArg Complex.re (corner_normalization τ hτ k)
  have hcard : (Fintype.card (Fin N ⊕ Fin N) : ℂ) = (2*N : ℝ) := by
    simp [two_mul]
  rw [hcard] at hnorm
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.one_re] at hnorm
  have hbound := corner_scalar_upper_bound τ k c
    (partialSum_nonneg (rightSquare x) (fun i => mul_star_self_nonneg (x i)) N) hrow
  have hpos : (0 : ℝ) < 2*N := by positivity
  apply (div_le_iff₀ hpos).mpr
  nlinarith

theorem uniform_defect_twentyFour (x : ℕ → A)
    (hcol : partialSum (leftSquare x) 24 = 1)
    (hrow : partialSum (rightSquare x) 24 ≤ ((2/3 : ℝ) : ℂ) • (1 : A)) :
    PositiveContraction (defectA x 24) ∧ PositiveContraction (defectB x 24) ∧
    ∀ τ : OneQuasitrace (CStarMatrix (Fin 24 ⊕ Fin 24) (Fin 24 ⊕ Fin 24) A),
      τ.Normalized → (1 : ℝ)/144 ≤
        (τ (defectA x 24 + defectB x 24) - τ (defectA x 24) - τ (defectB x 24)).re := by
  simpa only [Nat.cast_ofNat, defect_constant] using
    uniform_defect x 24 (by decide) (2/3) (by norm_num) (by norm_num) hcol hrow

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Kq.Kaplansky_ActualAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The actual M48 algebra, its fixed defect pair, and its Cuntz dimension state. -/

namespace Kaplansky

section
open scoped BigOperators
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

private theorem partialSum_leftSquare_fin {B : Type*} [CStarAlgebra B] {N : ℕ}
    (g : Fin N → B) :
    partialSum (leftSquare (fun i => if hi : i < N then g ⟨i, hi⟩ else 0)) N =
      ∑ i : Fin N, star (g i) * g i := by
  simp [partialSum, ← Fin.sum_univ_eq_sum_range, leftSquare]

private theorem partialSum_rightSquare_fin {B : Type*} [CStarAlgebra B] {N : ℕ}
    (g : Fin N → B) :
    partialSum (rightSquare (fun i => if hi : i < N then g ⟨i, hi⟩ else 0)) N =
      ∑ i : Fin N, g i * star (g i) := by
  simp [partialSum, ← Fin.sum_univ_eq_sum_range, rightSquare]

attribute [local instance] OAI.Kaplansky.actualAlgebraSemiring
attribute [local instance] OAI.Kaplansky.actualAlgebraSpectralLE
theorem actualGeneratorNat_column : partialSum (leftSquare actualGeneratorNat) 24 = 1 :=
  (partialSum_leftSquare_fin (generatedGenerator actualBoundedGenerator)).trans
    actual_test_shift_algebra.2.2.1

theorem actualGeneratorNat_row :
    partialSum (rightSquare actualGeneratorNat) 24 ≤ ((2/3 : ℝ) : ℂ) • (1 : ActualAlgebra) := by
  have hs := partialSum_rightSquare_fin (generatedGenerator actualBoundedGenerator)
  have hr := actual_test_shift_algebra.2.2.2
  apply (congrArg (fun x : ActualAlgebra =>
    x ≤ ((2/3 : ℝ) : ℂ) • (1 : ActualAlgebra)) hs).mpr
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hr

/-- The fixed pair in the actual 48-by-48 amplification satisfies the
universal defect bound, without assuming that any quasitrace exists. -/
theorem actualDefectPair_spec :
    PositiveContraction actualDefectA ∧ PositiveContraction actualDefectB ∧
      ∀ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized →
        (1 : ℝ)/144 ≤ (τ (actualDefectA+actualDefectB) - τ actualDefectA - τ actualDefectB).re :=
  uniform_defect_twentyFour actualGeneratorNat actualGeneratorNat_column actualGeneratorNat_row

theorem actualDefectAlgebra_separable : TopologicalSpace.SeparableSpace ActualDefectAlgebra := by
  let := actualAlgebra_nontrivial_separable.2
  exact inferInstanceAs (TopologicalSpace.SeparableSpace
    (ActualDefectIndex → ActualDefectIndex → ActualAlgebra))

attribute [local instance] OAI.Kaplansky.actualDefectAlgebraSemiring
theorem mainTarget_of_actualDefectQuasitrace_oai
    (hq : ∃ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized ∧ τ.IsTwo) : MainTarget := by
  refine ⟨ActualDefectAlgebra,inferInstance,actualDefectAlgebra_separable,hq,
    actualDefectA,actualDefectB,actualDefectPair_spec.1,actualDefectPair_spec.2.1,?_⟩
  intro τ hτ _
  exact actualDefectPair_spec.2.2 τ hτ

end

end Kaplansky

end

end OAI
end

theorem solution : type_of% @OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace_oai := @OAI.Kaplansky.mainTarget_of_actualDefectQuasitrace_oai
