-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_coordinate_reduced_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:23:48.045933+00:00
-- url     : https://prove2.me/submissions/8ecb6732-f59d-4039-9484-5a845477b970

import Mathlib
import Definitions.Def_OAIQ11Fg020
import Definitions.Def_OAIQ11Fg014
import Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_ordered_unitary

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem exists_coordinate_reduced_unitary_oai
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ a : Bounded M,
      (∀ j,a.val j ∈ unitary M.toStarSubalgebra ∧ (a.val j).val ∈ N) ∧
      ReducedOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) a) x := by
  obtain ⟨a,ha,ham⟩ := exists_coordinate_ordered_unitary τ hNM hfactor hdiff hirr hsep ω hω x hx
  let u := quotientMap τ (ω : Filter ℕ) a
  have hu : u ∈ unitary (Q τ ω) := quotient_unitary_of_coordinates τ ω a (fun j => (ha j).1)
  obtain ⟨b,hb,hbm⟩ := exists_coordinate_ordered_unitary τ hNM hfactor hdiff hirr hsep ω hω
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

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_coordinate_reduced_unitary_oai.{u_1} := @OAI.Generator.Tracial.exists_coordinate_reduced_unitary_oai.{u_1}
