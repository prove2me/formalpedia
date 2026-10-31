-- Prove2me | solution 1 for OAI.Generator.Tracial.nonempty_coordinateHaarData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:34:23.314537+00:00
-- url     : https://prove2.me/submissions/4e530da8-90e2-4724-8f7d-de3ad966a01f

import Mathlib
import Definitions.Def_OAIQ11Fg023
import Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_reduced_unitary
import Theorems.Thm_OAI_Generator_Tracial_reduced_integer_moment_closedSpan

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

/-! The actual countable centered coefficients needed to expand words in UV. -/

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

theorem betweenWord_repeat_prefix (v : A) (s : Bool) (n : ℕ) (xs : List (A × Bool)) (b : A) :
    betweenWord v s (List.replicate n (1,s) ++ xs) b =
      algebraSignedLetter v s^n*betweenWord v s xs b := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,betweenWord,ih,pow_succ',mul_assoc]

theorem powerBlockWord_expand (v : A) (s : Bool) (n : ℕ)
    (xs : List (A × (Bool × ℕ))) (b : A) :
    powerBlockWord v s n xs b = betweenWord v s (powerBlockGaps s n xs) b := by
  induction xs generalizing s n with
  | nil =>
    rw [powerBlockGaps,← List.append_nil (List.replicate n (1,s)),betweenWord_repeat_prefix]
    simp [powerBlockWord,betweenWord,pow_succ,mul_assoc]
  | cons a xs ih =>
    rcases a with ⟨d,t,k⟩
    simp only [powerBlockGaps,betweenWord_repeat_prefix,betweenWord,powerBlockWord,ih,
      pow_succ,mul_assoc]

theorem integerPowerBlock_eval (v : unitary A) (n : ℤ) (hn : n ≠ 0) :
    (↑(v^n) : A)=algebraSignedLetter (v : A) (integerPowerBlock n).1^
      ((integerPowerBlock n).2+1) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      change (↑(v^((n+1 : ℕ) : ℤ)) : A)=(v : A)^(n+1)
      rw [zpow_natCast]
      rfl
  | negSucc n =>
    rw [zpow_negSucc]
    change star ((v : A)^(n+1))=_
    simp [integerPowerBlock,algebraSignedLetter,star_pow]

theorem integerWord_blocks (v : unitary A) (x : ℕ → A) (n : ℤ) (hn : n ≠ 0)
    (xs : List (ℕ × ℤ)) (hxs : ∀ a ∈ xs,a.2 ≠ 0) (b : A) :
    integerWord v x n xs b = powerBlockWord (v : A) (integerPowerBlock n).1
      (integerPowerBlock n).2 (xs.map (fun a => (x a.1,integerPowerBlock a.2))) b := by
  induction xs generalizing n with
  | nil => simp [integerWord,powerBlockWord,integerPowerBlock_eval v n hn]
  | cons a xs ih =>
    simp only [integerWord,List.map_cons,powerBlockWord,integerPowerBlock_eval v n hn]
    rw [ih a.2 (hxs a (by simp)) (fun z hz => hxs z (by simp [hz]))]

end Algebra

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem productGaps_repeat_prefix (x : ℕ → Q τ ω) (s : Bool) (n : ℕ)
    (xs : List (Q τ ω × Bool)) (hx : ProductGaps τ ω x s xs) :
    ProductGaps τ ω x s (List.replicate n (1,s)++xs) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    exact ⟨Or.inr ⟨rfl,rfl⟩,ih⟩

theorem productGaps_powerBlocks (x : ℕ → Q τ ω) (s : Bool) (n : ℕ)
    (xs : List (Q τ ω × (Bool × ℕ))) (hx : ∀ z ∈ xs,∃ i,x i=z.1) :
    ProductGaps τ ω x s (powerBlockGaps s n xs) := by
  induction xs generalizing s n with
  | nil =>
    simpa [powerBlockGaps] using productGaps_repeat_prefix τ ω x s n [] trivial
  | cons a xs ih =>
    apply productGaps_repeat_prefix
    exact ⟨Or.inl (hx a (by simp)),ih a.2.1 a.2.2 (fun z hz => hx z (by simp [hz]))⟩

theorem reducedOrderedMoments_integerWord (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Option ℕ) (n : ℤ) (hn : n ≠ 0) (xs : List (ℕ × ℤ))
    (hxs : ∀ z ∈ xs,z.2 ≠ 0) :
    quotientTrace τ ω (optionalCoefficient x a*integerWord v x n xs (optionalCoefficient x b))=0 := by
  rw [integerWord_blocks v x n hn xs hxs,powerBlockWord_expand]
  apply hm
  apply productGaps_powerBlocks
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  exact ⟨j.1,rfl⟩

theorem reducedOrderedMoments_haar (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x) (n : ℤ) (hn : n ≠ 0) :
    quotientTrace τ ω (↑(v^n) : Q τ ω)=0 := by
  simpa [optionalCoefficient,integerWord] using
    reducedOrderedMoments_integerWord τ ω v x hm none none n hn [] (by simp)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LaurentMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem exists_centered_dense_quotient_family (D : Subalgebra ℂ (Q τ ω))
    (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ x : ℕ → Q τ ω,(∀ i,x i ∈ D ∧ quotientTrace τ ω (x i)=0) ∧
      ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x) := by
  let S : Set (Q τ ω) := {d | d ∈ D ∧ quotientTrace τ ω d=0}
  have hS : TopologicalSpace.IsSeparable S := hD.mono (fun _ h => h.1)
  let : TopologicalSpace.SeparableSpace S := hS.separableSpace
  let : Nonempty S := ⟨⟨0,D.zero_mem,(traceLinear τ ω).map_zero⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := S)
  refine ⟨fun i => (v i).val,fun i => (v i).property,?_⟩
  intro d hd ht
  have hh := mem_closure_image continuous_subtype_val.continuousAt (hv (⟨d,hd,ht⟩ : S))
  simpa only [← Set.range_comp,Function.comp_def] using hh

theorem subalgebra_mem_centered_closedSpan (D : Subalgebra ℂ (Q τ ω))
    (x : ℕ → Q τ ω)
    (hx : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x))
    (d : Q τ ω) (hd : d ∈ D) : d ∈ traceClosedSpan τ ω (insert 1 (Set.range x)) := by
  let z := d-quotientTrace τ ω d • (1 : Q τ ω)
  have hzD : z ∈ D := D.sub_mem hd (D.smul_mem D.one_mem _)
  have hzt : quotientTrace τ ω z=0 := by
    change (traceLinear τ ω) (d-quotientTrace τ ω d • (1 : Q τ ω))=0
    rw [map_sub,map_smul]
    change quotientTrace τ ω d-quotientTrace τ ω d*quotientTrace τ ω 1=0
    rw [quotientTrace_one,mul_one,sub_self]
  have hz : z ∈ traceClosedSpan τ ω (insert 1 (Set.range x)) := by
    apply Submodule.closure_subset_topologicalClosure_span
    exact closure_mono (Set.subset_insert _ _) (hx z hzD hzt)
  have h1 : (1 : Q τ ω) ∈ traceClosedSpan τ ω (insert 1 (Set.range x)) :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_insert _ _))
  have hh := (traceClosedSpan τ ω (insert 1 (Set.range x))).add_mem hz
    ((traceClosedSpan τ ω (insert 1 (Set.range x))).smul_mem (quotientTrace τ ω d) h1)
  simpa only [z,sub_add_cancel] using hh

end

/-! Extend a trace identity in each factor to the closed linear span of its
allowed values. This uses separate continuity only. -/

/-! Construct an included Haar unitary and the full nonzero-integer endpoint
formula over any two-norm-separable unital subalgebra of the actual quotient. -/

/-! From the endpoint formula to every alternating word shape. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete each supported partial unitary by the identity on its orthogonal
complement. If the quotient support is one, the quotient value is unchanged. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem bounded_unitary_of_coordinates (a : Bounded M)
    (ha : ∀ j,a.val j ∈ _root_.unitary M.toStarSubalgebra) : a ∈ _root_.unitary (Bounded M) := by
  constructor
  · apply Subtype.ext; funext j; exact (ha j).1
  · apply Subtype.ext; funext j; exact (ha j).2

theorem quotient_unitary_of_coordinates (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
    (a : Bounded M) (ha : ∀ j,a.val j ∈ _root_.unitary M.toStarSubalgebra) :
    quotientMap τ (ω : Filter ℕ) a ∈ _root_.unitary (Q τ ω) := by
  have hu := bounded_unitary_of_coordinates a ha
  constructor
  · rw [← quotientMap_star,← map_mul,hu.1,map_one]
  · rw [← quotientMap_star,← map_mul,hu.2,map_one]

theorem bounded_coordinate_unitaries_inclusion (hNM : N ≤ M) (a : Bounded M)
    (ha : ∀ j,a.val j ∈ _root_.unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) :
    ∃ b : Bounded N,(∀ j,b.val j ∈ _root_.unitary N.toStarSubalgebra) ∧ boundedInclusion hNM b=a := by
  let b : Bounded N := ⟨fun j => ⟨(a.val j).val,(ha j).2⟩,a.property⟩
  refine ⟨b,?_,rfl⟩
  intro j
  constructor
  · apply Subtype.ext
    change star (a.val j).val*(a.val j).val=1
    exact congrArg (fun x : M.toStarSubalgebra => x.val) (ha j).1.1
  · apply Subtype.ext
    change (a.val j).val*star (a.val j).val=1
    exact congrArg (fun x : M.toStarSubalgebra => x.val) (ha j).1.2

end

/-! Ordered independence with actual coordinate unitaries in the included
algebra, obtained by completing the constructed partial-unitary coordinates. -/

/-! Two coordinate-unitary witnesses produce the reduced-moment Haar precursor
while retaining actual unitary coordinates in the included algebra. -/

/-! Full integer endpoint moments and an actual included coordinate-unitary
Haar witness, before imposing an operator topology on generated algebras. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

omit hfactor hdiff hirr hsep in
private theorem coordinate_haar_endpoints_of_coordinates
    (D : Subalgebra ℂ (Q τ ω)) (x : ℕ → Q τ ω)
    (hdense : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x))
    (a : Bounded M)
    (ha : ∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N)
    (hm : ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0 := by
  let t : unitary (Q τ ω) := ⟨quotientMap τ (ω : Filter ℕ) a,
    quotient_unitary_of_coordinates τ ω a (fun j => (ha j).1)⟩
  obtain ⟨b,hb⟩ := bounded_coordinate_unitaries_inclusion hNM a ha
  have hhaar := reducedOrderedMoments_haar τ ω t x hm
  refine ⟨t,⟨b,hb.1,?_⟩,hhaar,?_⟩
  · change quotientMap τ (ω : Filter ℕ) (boundedInclusion hNM b)=quotientMap τ (ω : Filter ℕ) a
    exact congrArg (quotientMap τ (ω : Filter ℕ)) hb.2
  · intro c hc d hd n hn xs hxs
    apply reduced_integer_moment_closedSpan τ ω t x hm c d
      (subalgebra_mem_centered_closedSpan τ ω D x hdense c hc)
      (subalgebra_mem_centered_closedSpan τ ω D x hdense d hd) n hn xs
    intro z hz
    exact ⟨Submodule.closure_subset_topologicalClosure_span _
      (hdense z.1 (hxs z hz).1 (hxs z hz).2.1),(hxs z hz).2.2⟩

private theorem coordinate_haar_endpoints_of_dense_family (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (x : ℕ → Q τ ω)
    (hx : ∀ i,x i ∈ D ∧ quotientTrace τ ω (x i)=0)
    (hdense : ∀ d ∈ D,quotientTrace τ ω d=0 → d ∈ closure (Set.range x)) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0 := by
  obtain ⟨a,ha⟩ := exists_coordinate_reduced_unitary (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
    ω hω x (fun i => (hx i).2)
  exact coordinate_haar_endpoints_of_coordinates τ ω hNM D x hdense a ha.1 ha.2

theorem exists_coordinate_haar_endpoints (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    ∃ t : unitary (Q τ ω),
      (∃ b : Bounded N,(∀ j,b.val j ∈ unitary N.toStarSubalgebra) ∧
        quotientInclusion τ hNM (ω : Filter ℕ)
          (quotientMap (restrictedTrace τ hNM) (ω : Filter ℕ) b)=(t : Q τ ω)) ∧
      (∀ n : ℤ,n ≠ 0 → quotientTrace τ ω (↑(t^n) : Q τ ω)=0) ∧
      ∀ c ∈ D,∀ d ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
        (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        quotientTrace τ ω (c*integerValueWord τ ω t n xs d)=0 := by
  obtain ⟨x,hx⟩ := exists_centered_dense_quotient_family (H := H) (M := M) τ ω D hD
  exact coordinate_haar_endpoints_of_dense_family τ ω hNM hfactor hdiff hirr hsep
    hω D x hx.1 hx.2

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/
section
attribute [local instance] quotientL2AddCommMonoid quotientL2AddCommGroup
  quotientOperatorSemiring quotientOperatorNonAssocSemiring quotientOperatorAlgebra
  quotientOperatorSemitopology
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem nonempty_coordinateHaarData_oai (hω : (ω : Filter ℕ) ≤ atTop)
    (D : Subalgebra ℂ (Q τ ω)) (hD : TopologicalSpace.IsSeparable (D : Set (Q τ ω))) :
    Nonempty (CoordinateHaarData τ ω hNM D) := by
  obtain ⟨t,⟨b,hb,he⟩,_,hep⟩ := exists_coordinate_haar_endpoints
    (H := H) (N := N) (M := M) τ ω hNM hfactor hdiff hirr hsep hω D hD
  exact ⟨⟨t,b,hb,he,hep⟩⟩

end

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.nonempty_coordinateHaarData_oai.{u_1} := @OAI.Generator.Tracial.nonempty_coordinateHaarData_oai.{u_1}
