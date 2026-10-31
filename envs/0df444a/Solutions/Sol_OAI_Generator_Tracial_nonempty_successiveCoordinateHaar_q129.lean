-- Prove2me | solution 1 for OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:39:56.037996+00:00
-- url     : https://prove2.me/submissions/13c0ba90-2ef3-4875-9053-c066660dd5b6

import Mathlib
import Definitions.Def_OAIQ129G015
import Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_ordered_unitary_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A}
    (hs : s.Countable) : (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := inferInstanceAs (Countable (List s))
  rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
  exact Set.countable_range _

theorem separable_countable_star_adjoin {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousSMul ℂ A] {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rw [StarAlgebra.adjoin_eq_span]
  apply TopologicalSpace.IsSeparable.span
  apply Set.Countable.isSeparable
  apply countable_monoid_closure
  exact hs.union (by simpa only [Set.image_star] using hs.image star)

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotientTrace_mul_comm (a b : TracialQuotient τ (ω : Filter ℕ)) :
    quotientTrace τ ω (a*b) = quotientTrace τ ω (b*a) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change traceRep τ ω (a*b) = traceRep τ ω (b*a)
      apply tendsto_nhds_unique (traceRep_tendsto τ ω (a*b))
      have ht := traceRep_tendsto τ ω (b*a)
      change Tendsto (fun n => τ.trace (b.val n*a.val n)) _ _ at ht
      change Tendsto (fun n => τ.trace (a.val n*b.val n)) _ _
      simpa only [τ.trace_mul_comm] using ht

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.traceCyclicOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual trace Hilbert completion of the bounded-sequence tracial quotient.
The vector-trace representation is explicit data; its existence for an arbitrary
factor is not asserted here. No free-independence premise occurs. -/
open Filter
open scoped Topology ComplexConjugate

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem quotient_norm_star (a : Q τ ω) : ‖star a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_eq_trace, inner_eq_trace, star_star, quotientTrace_mul_comm τ ω a (star a)]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.boundedCompletedUnitary_apply _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.sequenceInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

theorem signed_product_split (u v : A) (s : Bool) :
    algebraSignedLetter (u*v) s = productLeft u s*algebraSignedLetter v s*productRight u s := by
  cases s <;> simp [algebraSignedLetter,productLeft,productRight,star_mul]

theorem betweenWord_product (u v : A) (s : Bool) (xs : List (A × Bool)) (b : A) :
    betweenWord (u*v) s xs b = productLeft u s * algebraPatchingWord v
      (productGapList u s xs ++ [(finalWordSign s xs,productRight u (finalWordSign s xs)*b)]) := by
  induction xs generalizing s with
  | nil => simp [betweenWord,productGapList,finalWordSign,algebraPatchingWord,
      signed_product_split,mul_assoc]
  | cons a xs ih =>
    simp only [betweenWord,productGapList,finalWordSign,List.cons_append,
      algebraPatchingWord,signed_product_split,ih,mul_assoc]

end Algebra
section

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem exactOrderedMoments_values (v : Q τ ω) (y : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω v y) (a b : Q τ ω)
    (ha : ∃ i : Option ℕ,optionalCoefficient y i=a)
    (hb : ∃ i : Option ℕ,optionalCoefficient y i=b)
    (xs : List (Bool × Q τ ω)) (hxs : ∀ z ∈ xs,∃ i,y i=z.2) (s : Bool) :
    quotientTrace τ ω (a*algebraPatchingWord v (xs++[(s,b)]))=0 := by
  have hencode : ∃ is : List (Bool × ℕ),is.map (fun z => (z.1,y z.2))=xs := by
    induction xs with
    | nil => exact ⟨[],rfl⟩
    | cons z xs ih =>
      obtain ⟨i,hi⟩ := hxs z (by simp)
      obtain ⟨is,his⟩ := ih (fun z hz => hxs z (by simp [hz]))
      exact ⟨(z.1,i)::is,by simp [hi,his]⟩
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hb
  obtain ⟨is,rfl⟩ := hencode
  exact hm i j is s

end

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem productCenteredFamily_encode (u : Q τ ω) (x : ℕ → Q τ ω) (i : ProductFamilyIndex) :
    productCenteredFamily τ ω u x (Encodable.encode i)=productFamilyValue τ ω u x i := by
  simp [productCenteredFamily]

theorem productCenteredFamily_centered (u : Q τ ω) (x : ℕ → Q τ ω)
    (hu : u*star u=1) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω u x) :
    ∀ i,quotientTrace τ ω (productCenteredFamily τ ω u x i)=0 := by
  intro n
  unfold productCenteredFamily
  cases Encodable.decode (α := ProductFamilyIndex) n with
  | none => exact (traceLinear τ ω).map_zero
  | some i =>
    cases i with
    | inl j => exact hx j
    | inr i =>
      cases i with
      | inl a =>
        rcases a with ⟨s,j⟩
        cases s
        · simpa [productFamilyValue,algebraPatchingWord,algebraSignedLetter,optionalCoefficient]
            using hm j none [] false
        · simpa [productFamilyValue,algebraPatchingWord,algebraSignedLetter,optionalCoefficient]
            using hm none j [] true
      | inr j =>
        change quotientTrace τ ω (star u*x j*u)=0
        rw [quotientTrace_mul_comm τ ω (star u*x j),← mul_assoc,hu,one_mul]
        exact hx j

theorem productFamily_original (u : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=x i :=
  ⟨Encodable.encode (Sum.inl i : ProductFamilyIndex),productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_right (u : Q τ ω) (x : ℕ → Q τ ω) (i : Option ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=optionalCoefficient x i*u :=
  ⟨Encodable.encode (Sum.inr (Sum.inl (false,i)) : ProductFamilyIndex),
    productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_left (u : Q τ ω) (x : ℕ → Q τ ω) (i : Option ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=star u*optionalCoefficient x i :=
  ⟨Encodable.encode (Sum.inr (Sum.inl (true,i)) : ProductFamilyIndex),
    productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_conjugate (u : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) :
    ∃ j,productCenteredFamily τ ω u x j=star u*x i*u :=
  ⟨Encodable.encode (Sum.inr (Sum.inr i) : ProductFamilyIndex),
    productCenteredFamily_encode τ ω u x _⟩

theorem productFamily_optional (u : Q τ ω) (x : ℕ → Q τ ω) (i : Option ℕ) :
    ∃ j : Option ℕ,optionalCoefficient (productCenteredFamily τ ω u x) j=optionalCoefficient x i := by
  cases i with
  | none => exact ⟨none,rfl⟩
  | some i =>
    obtain ⟨j,hj⟩ := productFamily_original τ ω u x i
    exact ⟨some j,hj⟩

theorem productFamily_first (u : Q τ ω) (x : ℕ → Q τ ω) (a : Option ℕ) (s : Bool) :
    ∃ j : Option ℕ,optionalCoefficient (productCenteredFamily τ ω u x) j=
      optionalCoefficient x a*productLeft u s := by
  cases s
  · obtain ⟨j,hj⟩ := productFamily_right τ ω u x a
    exact ⟨some j,hj⟩
  · simpa [productLeft] using productFamily_optional τ ω u x a

theorem productFamily_last (u : Q τ ω) (x : ℕ → Q τ ω) (b : Option ℕ) (s : Bool) :
    ∃ j : Option ℕ,optionalCoefficient (productCenteredFamily τ ω u x) j=
      productRight u s*optionalCoefficient x b := by
  cases s
  · simpa [productRight] using productFamily_optional τ ω u x b
  · obtain ⟨j,hj⟩ := productFamily_left τ ω u x b
    exact ⟨some j,hj⟩

theorem productFamily_gap (u : Q τ ω) (x : ℕ → Q τ ω)
    (s t : Bool) (d : Q τ ω) (hd : (∃ i,x i=d) ∨ (d=1 ∧ s=t)) :
    ∃ j,productCenteredFamily τ ω u x j=productRight u s*d*productLeft u t := by
  rcases hd with ⟨i,rfl⟩ | ⟨rfl,rfl⟩
  · cases s <;> cases t
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_right τ ω u x (some i)
    · simpa [productRight,productLeft] using productFamily_original τ ω u x i
    · simpa [productRight,productLeft] using productFamily_conjugate τ ω u x i
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_left τ ω u x (some i)
  · cases s
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_right τ ω u x none
    · simpa [productRight,productLeft,optionalCoefficient] using productFamily_left τ ω u x none

theorem productGapList_members (u : Q τ ω) (x : ℕ → Q τ ω)
    (s : Bool) (xs : List (Q τ ω × Bool)) (hx : ProductGaps τ ω x s xs) :
    ∀ z ∈ productGapList u s xs,∃ i,productCenteredFamily τ ω u x i=z.2 := by
  induction xs generalizing s with
  | nil => simp [productGapList]
  | cons a xs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact productFamily_gap τ ω u x s a.2 a.1 hx.1
    · exact ih a.2 hx.2 z hz

/-- The product has every reduced signed moment, including same-sign unit gaps. -/
theorem product_reduced_moment (u v : Q τ ω) (x : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω v (productCenteredFamily τ ω u x))
    (a b : Option ℕ) (s : Bool) (xs : List (Q τ ω × Bool))
    (hx : ProductGaps τ ω x s xs) :
    quotientTrace τ ω (optionalCoefficient x a*betweenWord (u*v) s xs
      (optionalCoefficient x b))=0 := by
  rw [betweenWord_product,← mul_assoc]
  exact exactOrderedMoments_values τ ω v _ hm _ _
    (productFamily_first τ ω u x a s)
    (productFamily_last τ ω u x b (finalWordSign s xs)) _
    (productGapList_members τ ω u x s xs hx) _

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_LaurentMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.boundedCompletedUnitary_apply _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem sandwich_trace_inner (a z b : Q τ ω) :
    quotientTrace τ ω (a*z*b)=inner ℂ (star (b*a)) z := by
  rw [inner_eq_trace,star_star,quotientTrace_mul_comm τ ω (a*z),← mul_assoc]

theorem sandwich_trace_closedSpan (S : Set (Q τ ω)) (a b z : Q τ ω)
    (hz : z ∈ traceClosedSpan τ ω S)
    (h : ∀ y ∈ S,quotientTrace τ ω (a*y*b)=0) :
    quotientTrace τ ω (a*z*b)=0 := by
  let f : Q τ ω →L[ℂ] ℂ := innerSL ℂ (star (b*a))
  have hs : Submodule.span ℂ S ≤ LinearMap.ker f.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    change inner ℂ (star (b*a)) y=0
    rw [← sandwich_trace_inner]
    exact h y hy
  have hc := (Submodule.span ℂ S).topologicalClosure_minimal hs f.isClosed_ker
  have hh := hc hz
  change inner ℂ (star (b*a)) z=0 at hh
  rwa [← sandwich_trace_inner] at hh

/-! Extend exact moments by separate trace continuity in the two-norm. No
joint continuity of quotient multiplication, or operator-norm structure on Q,
is assumed. -/

/-- All internal coefficients are extended one at a time, with the other
factors fixed. Uniform bounds on simultaneous approximants are unnecessary. -/
theorem integerValueWord_closedSpan (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (a b : Q τ ω) (n : ℤ) (xs : List (Q τ ω × ℤ))
    (hxs : ∀ z ∈ xs,z.1 ∈ traceClosedSpan τ ω (Set.range x))
    (hm : ∀ is : List ℕ,is.length=xs.length →
      quotientTrace τ ω (a*integerWord v x n (is.zip (xs.map Prod.snd)) b)=0) :
    quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0 := by
  induction xs generalizing a n with
  | nil => exact hm [] rfl
  | cons z xs ih =>
    have hi (i : ℕ) : quotientTrace τ ω
        ((a*(↑(v^n) : Q τ ω)*x i)*integerValueWord τ ω v z.2 xs b)=0 := by
      apply ih (a*(↑(v^n) : Q τ ω)*x i) z.2
      · exact fun y hy => hxs y (by simp [hy])
      · intro is his
        have hh := hm (i::is) (by simp [his])
        simpa only [List.map_cons,List.zip_cons_cons,integerWord,mul_assoc] using hh
    have hh := sandwich_trace_closedSpan τ ω (Set.range x) (a*(↑(v^n) : Q τ ω))
      (integerValueWord τ ω v z.2 xs b) z.1 (hxs z (by simp)) (by
        rintro _ ⟨i,rfl⟩
        exact hi i)
    simpa only [integerValueWord,mul_assoc] using hh

/-- The optional endpoints span the unit and the given centered family. -/
theorem optionalCoefficient_range (x : ℕ → Q τ ω) :
    Set.range (optionalCoefficient x)=insert 1 (Set.range x) := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    cases i <;> simp [optionalCoefficient]
  · intro h
    rcases Set.mem_insert_iff.mp h with rfl | ⟨i,rfl⟩
    · exact ⟨none,rfl⟩
    · exact ⟨some i,rfl⟩

theorem integerWord_right_factor {A : Type*} [Monoid A] [StarMul A]
    (v : unitary A) (x : ℕ → A) (n : ℤ) (xs : List (ℕ × ℤ)) (b : A) :
    integerWord v x n xs b=integerWord v x n xs 1*b := by
  induction xs generalizing n with
  | nil => simp only [integerWord,mul_one]
  | cons z xs ih =>
    simp only [integerWord]
    rw [ih z.2]
    simp only [mul_assoc]

theorem integerWord_closed_endpoints (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Q τ ω)
    (ha : a ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (hb : b ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (n : ℤ) (hn : n ≠ 0) (xs : List (ℕ × ℤ)) (hxs : ∀ z ∈ xs,z.2 ≠ 0) :
    quotientTrace τ ω (a*integerWord v x n xs b)=0 := by
  have hright (i : Option ℕ) :
      quotientTrace τ ω (optionalCoefficient x i*integerWord v x n xs b)=0 := by
    have htail := integerWord_right_factor v x n xs
    rw [htail,← mul_assoc]
    have hh := sandwich_trace_closedSpan τ ω (insert 1 (Set.range x))
      (optionalCoefficient x i*integerWord v x n xs 1) 1 b hb (by
        intro y hy
        rw [← optionalCoefficient_range] at hy
        obtain ⟨j,rfl⟩ := hy
        have hj := reducedOrderedMoments_integerWord τ ω v x hm i j n hn xs hxs
        rw [htail (optionalCoefficient x j)] at hj
        simpa only [mul_one,mul_assoc] using hj)
    simpa only [mul_one] using hh
  have hh := sandwich_trace_closedSpan τ ω (insert 1 (Set.range x)) 1
    (integerWord v x n xs b) a ha (by
      intro y hy
      rw [← optionalCoefficient_range] at hy
      obtain ⟨i,rfl⟩ := hy
      simpa only [one_mul] using hright i)
  simpa only [one_mul] using hh

theorem reduced_integer_moment_closedSpan (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Q τ ω)
    (ha : a ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (hb : b ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hxs : ∀ z ∈ xs,z.1 ∈ traceClosedSpan τ ω (Set.range x) ∧ z.2 ≠ 0) :
    quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0 := by
  apply integerValueWord_closedSpan τ ω v x a b n xs (fun z hz => (hxs z hz).1)
  intro is his
  apply integerWord_closed_endpoints τ ω v x hm a b ha hb n hn
  intro z hz
  have hz' := List.of_mem_zip hz
  obtain ⟨d,hd,he⟩ := List.mem_map.mp hz'.2
  exact he ▸ (hxs d hd).2

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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

theorem exists_coordinate_reduced_unitary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ a : Bounded M,
      (∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) ∧
      ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x := by
  obtain ⟨a,ha,ham⟩ := exists_coordinate_ordered_unitary_q129 τ hNM hfactor hdiff hirr hsep ω hω x hx
  let u := quotientMap τ (ω : Filter ℕ) a
  have hu : u ∈ unitary (Q τ ω) := quotient_unitary_of_coordinates τ ω a (fun j => (ha j).1)
  obtain ⟨b,hb,hbm⟩ := exists_coordinate_ordered_unitary_q129 τ hNM hfactor hdiff hirr hsep ω hω
    (productCenteredFamily τ ω u x) (productCenteredFamily_centered τ ω u x hu.2 hx ham)
  refine ⟨a*b,?_,?_⟩
  · intro j
    exact ⟨(unitary M.toStarSubalgebra).mul_mem (ha j).1 (hb j).1,N.mul_mem (ha j).2 (hb j).2⟩
  · rw [map_mul]
    intro c d sign xs hxs
    exact product_reduced_moment τ ω u (quotientMap τ (ω : Filter ℕ) b) x hbm c d sign xs hxs

end

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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

theorem nonempty_coordinateHaarData (hω : (ω : Filter ℕ) ≤ atTop)
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
section
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

theorem nonempty_successiveCoordinateHaar_q129_oai (hω : (ω : Filter ℕ) ≤ atTop)
    (seed : Set (Q τ ω)) (hseed : seed.Countable) :
    Nonempty (SuccessiveCoordinateHaar τ ω hNM seed) := by
  let : NormedSpace ℂ (Q τ ω) := (quotientInnerProductSpace τ ω).toNormedSpace
  have : IsBoundedSMul ℂ (Q τ ω) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  have : ContinuousSMul ℂ (Q τ ω) := IsBoundedSMul.continuousSMul
  let step (s : {s : Set (Q τ ω) // s.Countable}) := Classical.choice
    (nonempty_coordinateHaarData τ ω hNM hfactor hdiff hirr hsep hω
      (StarAlgebra.adjoin ℂ s.val).toSubalgebra (separable_countable_star_adjoin s.property))
  let S : ℕ → {s : Set (Q τ ω) // s.Countable} := Nat.rec ⟨seed,hseed⟩
    (fun _ s => ⟨insert ((step s).t : Q τ ω) s.val,s.property.insert _⟩)
  refine ⟨⟨fun j => StarAlgebra.adjoin ℂ (S j).val,fun j => step (S j),rfl,?_,
    fun j => separable_countable_star_adjoin (S j).property⟩⟩
  intro j
  change StarAlgebra.adjoin ℂ (insert ((step (S j)).t : Q τ ω) (S j).val)=
    StarAlgebra.adjoin ℂ (insert ((step (S j)).t : Q τ ω)
      (StarAlgebra.adjoin ℂ (S j).val : Set (Q τ ω)))
  apply le_antisymm
  · apply StarAlgebra.adjoin_mono
    exact Set.insert_subset_insert (StarAlgebra.subset_adjoin ℂ _)
  · apply StarAlgebra.adjoin_le
    apply Set.insert_subset
    · exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _)
    · exact StarAlgebra.adjoin_mono (Set.subset_insert _ _)

end

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129_oai.{u_1} := @OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129_oai.{u_1}
