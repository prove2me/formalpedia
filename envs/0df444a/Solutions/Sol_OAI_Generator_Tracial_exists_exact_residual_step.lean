-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_exact_residual_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:33:39.473716+00:00
-- url     : https://prove2.me/submissions/4a6ccb51-776c-46f6-bf78-7f297b43269b

import Mathlib
import Definitions.Def_OAIQ11Fg023
import Theorems.Thm_OAI_Generator_Tracial_exactOrderedMoments_add_of_cyclic
import Theorems.Thm_OAI_Generator_Tracial_exists_supported_corner_partial_sequence

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

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

theorem quotientMap_surjective : Function.Surjective (quotientMap τ l) := Quotient.mk_surjective

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerUnitary
variable {p q : AlgebraProjection M}

theorem patch_extends (v : CornerUnitary p) (w : CornerUnitary q) (hpq : p.val*q.val=0) :
    (patch v w hpq).val*(star v.val*v.val)=v.val := by
  have hqp : q.val*p.val=0 := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,q.property.isSelfAdjoint.star_eq,star_zero]
      using congrArg star hpq
  change (v.val+w.val)*(star v.val*v.val)=v.val
  rw [v.initial,add_mul,v.mul_support]
  have he : w.val*p.val=0 := by
    calc w.val*p.val=(w.val*q.val)*p.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,hqp,mul_zero]
  rw [he,add_zero]

end CornerUnitary

end

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/
section
open UltrapowerBridge

theorem map_algebraPatchingWord {A B : Type*} [Ring A] [Ring B]
    [StarRing A] [StarRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →⋆ₐ[ℂ] B) (v : A) (xs : List (Bool × A)) :
    f (algebraPatchingWord v xs) =
      algebraPatchingWord (f v) (xs.map (fun a => (a.1,f a.2))) := by
  induction xs with
  | nil => exact f.map_one
  | cons a xs ih =>
    simp only [algebraPatchingWord,List.map_cons,map_mul,ih]
    congr 2
    cases a.1
    · rfl
    · exact map_star f v

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem bounded_word_evaluation (v : Bounded M) (xs : List (Bool × Bounded M)) (j : ℕ) :
    (algebraPatchingWord v xs).val j =
      patchingWord (v.val j) (xs.map (fun a => (a.1,a.2.val j))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (algebraSignedLetter v a.1).val j * a.2.val j *
      (algebraPatchingWord v xs).val j = _
    rw [ih]
    simp only [List.map_cons,patchingWord]
    cases a.1 <;> rfl

end

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem boundedPartialSupport_projection (v : ℕ → PartialUnitary M) :
    IsStarProjection (boundedPartialSupport v) := by
  constructor
  · apply Subtype.ext
    funext j
    exact (v j).support.property.isIdempotentElem
  · apply Subtype.ext
    funext j
    exact (v j).support.property.isSelfAdjoint

theorem boundedPartialUnitary_initial (v : ℕ → PartialUnitary M) :
    star (boundedPartialUnitary v)*boundedPartialUnitary v = boundedPartialSupport v := by
  apply Subtype.ext
  funext j
  exact (v j).unitary.initial

theorem boundedPartialUnitary_final (v : ℕ → PartialUnitary M) :
    boundedPartialUnitary v*star (boundedPartialUnitary v) = boundedPartialSupport v := by
  apply Subtype.ext
  funext j
  exact (v j).unitary.final

theorem quotient_ordered_moment_zero (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (x : ℕ → Bounded M)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool)
    (hz : Tendsto (fun j => τ.trace (indexedCoefficient (fun i => (x i).val) j first *
      patchingWord (v j).val (xs.map (fun a => (a.1,(x a.2).val j)) ++
        [(s,indexedCoefficient (fun i => (x i).val) j last)]))) atTop (𝓝 0)) :
    quotientTrace τ ω (optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) first *
      algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))
        (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (x a.2))) ++
          [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) last)])) = 0 := by
  let f := quotientStarAlgHom τ (ω : Filter ℕ)
  let b : Bounded M := optionalCoefficient x first * algebraPatchingWord (boundedPartialUnitary v)
    (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])
  have hopt (i : Option ℕ) : f (optionalCoefficient x i) =
      optionalCoefficient (fun i => f (x i)) i := by cases i <;> simp [optionalCoefficient]
  have hb : f b = optionalCoefficient (fun i => f (x i)) first *
      algebraPatchingWord (f (boundedPartialUnitary v))
        (xs.map (fun a => (a.1,f (x a.2))) ++ [(s,optionalCoefficient (fun i => f (x i)) last)]) := by
    simp only [b,map_mul,map_algebraPatchingWord,hopt,List.map_append,List.map_cons,List.map_nil,
      List.map_map,Function.comp_def]
  change quotientTrace τ ω (optionalCoefficient (fun i => f (x i)) first *
    algebraPatchingWord (f (boundedPartialUnitary v))
      (xs.map (fun a => (a.1,f (x a.2))) ++ [(s,optionalCoefficient (fun i => f (x i)) last)])) = 0
  rw [← hb]
  apply tendsto_nhds_unique (traceRep_tendsto τ ω b)
  have he (j : ℕ) : b.val j = indexedCoefficient (fun i => (x i).val) j first *
      patchingWord (v j).val (xs.map (fun a => (a.1,(x a.2).val j)) ++
        [(s,indexedCoefficient (fun i => (x i).val) j last)]) := by
    change (optionalCoefficient x first).val j * _ = _
    rw [bounded_word_evaluation]
    have ho (i : Option ℕ) : (optionalCoefficient x i).val j =
        indexedCoefficient (fun i => (x i).val) j i := by cases i <;> rfl
    simp only [ho,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def]
    rfl
  simpa only [he] using hz.mono_left hω

end

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

theorem algebraPatchingWord_scale {A I : Type*} [Ring A] [Star A] [Algebra ℂ A]
    (v : A) (x y : I → A) (c : I → ℂ) (h : ∀ i,x i=c i • y i)
    (xs : List (Bool × I)) :
    algebraPatchingWord v (xs.map (fun a => (a.1,x a.2))) =
      (xs.map (fun a => c a.2)).prod •
        algebraPatchingWord v (xs.map (fun a => (a.1,y a.2))) := by
  induction xs with
  | nil => simp [algebraPatchingWord]
  | cons a xs ih =>
    simp only [List.map_cons,algebraPatchingWord,ih,List.prod_cons]
    rw [h a.2]
    simp only [
      mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm (c a.2)]

theorem optionalCoefficient_scale {A : Type*} [Ring A] [Algebra ℂ A]
    (x y : ℕ → A) (c : ℕ → ℂ) (h : ∀ i,x i=c i • y i) (i : Option ℕ) :
    optionalCoefficient x i=optionalCoefficient c i • optionalCoefficient y i := by
  cases i <;> simp [optionalCoefficient,h]

theorem ordered_moment_scale {A : Type*} [Ring A] [Star A] [Algebra ℂ A]
    (v : A) (x y : ℕ → A) (c : ℕ → ℂ) (h : ∀ i,x i=c i • y i)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]) =
    (optionalCoefficient c first * ((xs.map (fun a => c a.2)).prod * optionalCoefficient c last)) •
      (optionalCoefficient y first *
        algebraPatchingWord v (xs.map (fun a => (a.1,y a.2)) ++ [(s,optionalCoefficient y last)])) := by
  have hw := algebraPatchingWord_scale v (optionalCoefficient x) (optionalCoefficient y)
    (optionalCoefficient c) (optionalCoefficient_scale x y c h)
    (xs.map (fun a => (a.1,some a.2)) ++ [(s,last)])
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    optionalCoefficient,List.prod_append,List.prod_cons,List.prod_nil,mul_one] at hw
  change algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]) =
    ((xs.map (fun a => c a.2)).prod * optionalCoefficient c last) •
      algebraPatchingWord v (xs.map (fun a => (a.1,y a.2)) ++ [(s,optionalCoefficient y last)]) at hw
  rw [hw,optionalCoefficient_scale x y c h first,smul_mul_assoc,mul_smul_comm,smul_smul]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extension of actual partial unitaries and ordered words from pH.
The empty word maps to p, so word transport retains a final p. -/

/-! Finite partial independence in every nonzero represented subcorner,
with actual ambient support, membership and trace estimates. -/

/-! Ordered-word transport with ambient unit endpoints, and contractive
compression of supported centered coefficients. -/

/-! Diagonal partial independence in genuinely varying Hilbert-space corners.
The result retains an actual ambient partial-unitary sequence. -/
open Filter
open scoped Topology

/-! Actual coordinate partial-unitary witnesses in supported corners, followed
by exact quotient moments and the ambient quarter-support bound. -/
open Filter
open scoped Topology
open UltrapowerBridge
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

theorem exists_quotient_corner_partial_sequence
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (g : Bounded M) (hg : ∀ j,IsStarProjection (g.val j))
    (hgN : ∀ j,(g.val j).val ∈ N) (hg0 : ∀ j,g.val j ≠ 0)
    (x : ℕ → Bounded M) (hx : ∀ i j,‖(x i).val j‖ ≤ 1)
    (hc : ∀ i j,τ.trace ((x i).val j)=0)
    (hl : ∀ i,g*x i=x i) (hr : ∀ i,x i*g=x i) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,g.val j*(v j).support.val=(v j).support.val) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) g)).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (x a.2))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) last)]))=0 := by
  let p := fun j => (⟨g.val j,hg j⟩ : AlgebraProjection M)
  obtain ⟨v,hv,hs,ht,hw⟩ := exists_supported_corner_partial_sequence τ hNM hfactor hdiff hirr hsep
    p hgN hg0 (fun i => (x i).val) hx hc
    (fun i j => congrArg (fun a : Bounded M => a.val j) (hl i))
    (fun i j => congrArg (fun a : Bounded M => a.val j) (hr i))
  refine ⟨v,hv,hs,?_,?_⟩
  · apply le_of_tendsto_of_tendsto
      ((Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω g)).div_const 4)
      (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω (boundedPartialSupport v)))
    exact Eventually.of_forall (fun j => (ht j).le)
  · intro first last xs s
    exact quotient_ordered_moment_zero τ ω hω v x first last xs s (hw first last xs s)

end Generator.Tracial

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
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact coordinate centering in projection corners whose traces have a
uniform positive lower bound. The corner scalar is divided by its actual
trace; no global-centering-to-corner-centering implication is assumed. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem boundedCornerCenter_trace (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) (j : ℕ) :
    τ.trace ((boundedCornerCenter τ f a hf δ hδ hlower).val j)=0 := by
  have hne : τ.trace (f.val j) ≠ 0 := by
    intro h
    have := hlower j
    rw [h,Complex.zero_re] at this
    linarith
  change τ.trace (f.val j*a.val j*f.val j -
    (τ.trace (f.val j*a.val j*f.val j)/τ.trace (f.val j)) • f.val j)=0
  rw [TracialRepresentation.trace_sub,TracialRepresentation.trace_smul,div_mul_cancel₀ _ hne,sub_self]

theorem boundedCornerCenter_supported (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re) :
    f*boundedCornerCenter τ f a hf δ hδ hlower=boundedCornerCenter τ f a hf δ hδ hlower ∧
    boundedCornerCenter τ f a hf δ hδ hlower*f=boundedCornerCenter τ f a hf δ hδ hlower := by
  constructor <;> apply Subtype.ext <;> funext j
  · change f.val j*(f.val j*a.val j*f.val j - _ • f.val j)=_
    simp only [mul_sub,← mul_assoc,mul_smul_comm,(hf j).isIdempotentElem.eq]
    rfl
  · change (f.val j*a.val j*f.val j - _ • f.val j)*f.val j=_
    simp only [sub_mul,mul_assoc,smul_mul_assoc,(hf j).isIdempotentElem.eq]
    rfl

theorem boundedCornerCenter_quotient (ω : Ultrafilter ℕ)
    (f a : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ j,δ ≤ (τ.trace (f.val j)).re)
    (hz : quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (f*a*f))=0) :
    quotientMap τ (ω : Filter ℕ) (boundedCornerCenter τ f a hf δ hδ hlower)=
      quotientMap τ (ω : Filter ℕ) (f*a*f) := by
  apply (quotientMap_eq_iff τ (ω : Filter ℕ) _ _).mpr
  let b := f*a*f
  have ht := ((traceRep_tendsto τ ω b).norm).div_const δ
  change traceRep τ ω b=0 at hz
  rw [hz,norm_zero,zero_div] at ht
  change Tendsto (fun j => τ.norm₂ ((boundedCornerCenter τ f a hf δ hδ hlower).val j - b.val j)) _ _
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) ht
  have he : (boundedCornerCenter τ f a hf δ hδ hlower).val j - b.val j =
      -((τ.trace (b.val j)/τ.trace (f.val j)) • f.val j) := by
    change (b.val j - _)-b.val j = _
    abel
  rw [he]
  have hn : τ.norm₂ (-((τ.trace (b.val j)/τ.trace (f.val j)) • f.val j)) =
      ‖τ.trace (b.val j)/τ.trace (f.val j)‖*τ.norm₂ (f.val j) := by
    change ‖-((τ.trace (b.val j)/τ.trace (f.val j)) • ((f.val j : H →L[ℂ] H) τ.vector))‖ = _
    rw [norm_neg,norm_smul]
    rfl
  change τ.norm₂ (-((τ.trace (b.val j)/τ.trace (f.val j)) • f.val j)) ≤ _
  rw [hn]
  apply (mul_le_of_le_one_right (norm_nonneg _) ((τ.norm₂_le_norm _).trans (hf j).norm_le)).trans
  rw [norm_div]
  exact div_le_div₀ (norm_nonneg _) le_rfl hδ (corner_trace_norm_lower τ f δ hlower j)

end

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem quotientMap_eq_of_eventuallyEq (l : Filter ℕ) (a b : Bounded M)
    (he : a.val =ᶠ[l] b.val) : quotientMap τ l a=quotientMap τ l b := by
  apply (quotientMap_eq_iff τ l a b).mpr
  have hh : (fun _ : ℕ => (0 : ℝ)) =ᶠ[l] (fun j => τ.norm₂ (a.val j-b.val j)) := by
    filter_upwards [he] with j hj
    rw [hj,sub_self,τ.norm₂_zero]
  exact tendsto_const_nhds.congr' hh

end

/-! A projection sequence of positive quotient trace can be changed on an
ultrafilter-null set so every coordinate corner has uniformly positive trace.
Coordinates are replaced only by the unit, preserving subalgebra membership. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_eventually_positive_corner_representative (ω : Ultrafilter ℕ)
    (f : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (ht : 0 < (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f)).re) :
    ∃ δ : ℝ,0 < δ ∧ ∃ g : Bounded M,
      (∀ j,IsStarProjection (g.val j)) ∧ (∀ j,δ ≤ (τ.trace (g.val j)).re) ∧
      g.val =ᶠ[(ω : Filter ℕ)] f.val ∧
      (∀ j,g.val j=f.val j ∨ g.val j=1) := by
  classical
  let t := (traceRep τ ω f).re
  change 0 < t at ht
  let δ : ℝ := min (t/2) (1/2)
  have hδ : 0 < δ := lt_min (half_pos ht) (by norm_num)
  have hδt : δ < t := (min_le_left _ _).trans_lt (half_lt_self ht)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let g : Bounded M := ⟨fun j => if δ ≤ (τ.trace (f.val j)).re then f.val j else 1,
    1,zero_le_one,fun j => by
      change ‖if δ ≤ (τ.trace (f.val j)).re then f.val j else 1‖ ≤ 1
      split_ifs
      · exact (hf j).norm_le
      · exact operator_norm_one_le⟩
  refine ⟨δ,hδ,g,?_,?_,?_,?_⟩
  · intro j
    change IsStarProjection (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)
    split_ifs
    · exact hf j
    · exact IsStarProjection.one _
  · intro j
    change δ ≤ (τ.trace (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)).re
    split_ifs with h
    · exact h
    · simpa only [τ.trace_one,Complex.one_re] using hδ1
  · have he := (tendsto_order.mp
      (Complex.continuous_re.continuousAt.tendsto.comp (traceRep_tendsto τ ω f))).1 δ hδt
    filter_upwards [he] with j hj
    change δ < (τ.trace (f.val j)).re at hj
    change (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=f.val j
    rw [ite_eq_left hj.le]
  · intro j
    change (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=f.val j ∨
      (if δ ≤ (τ.trace (f.val j)).re then f.val j else 1)=1
    split_ifs <;> simp

theorem exists_eventually_centered_corner_representatives (ω : Ultrafilter ℕ)
    (f : Bounded M) (hf : ∀ j,IsStarProjection (f.val j))
    (ht : 0 < (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f)).re)
    (x : ℕ → Q τ ω)
    (hx : ∀ i,quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) f*x i*
      quotientMap τ (ω : Filter ℕ) f)=0) :
    ∃ δ : ℝ,0 < δ ∧ ∃ g : Bounded M,
      (∀ j,IsStarProjection (g.val j)) ∧ (∀ j,δ ≤ (τ.trace (g.val j)).re) ∧
      g.val =ᶠ[(ω : Filter ℕ)] f.val ∧ (∀ j,g.val j=f.val j ∨ g.val j=1) ∧
      ∃ b : ℕ → Bounded M,∀ i,
        g*b i=b i ∧ b i*g=b i ∧ (∀ j,τ.trace ((b i).val j)=0) ∧
        quotientMap τ (ω : Filter ℕ) (b i)=
          quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f := by
  classical
  obtain ⟨δ,hδ,g,hg,hgl,hgf,hgor⟩ :=
    exists_eventually_positive_corner_representative τ ω f hf ht
  have he := quotientMap_eq_of_eventuallyEq τ (ω : Filter ℕ) g f hgf
  choose a ha using fun i => quotientMap_surjective τ (ω : Filter ℕ) (x i)
  let b := fun i => boundedCornerCenter τ g (a i) hg δ hδ hgl
  refine ⟨δ,hδ,g,hg,hgl,hgf,hgor,b,fun i => ?_⟩
  have hclass : quotientMap τ (ω : Filter ℕ) (g*a i*g)=
      quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f := by
    let q := quotientMap τ (ω : Filter ℕ)
    calc
      q ((g*a i)*g) = (q g*q (a i))*q g :=
        (map_mul q (g*a i) g).trans
          (congrArg (fun y : Q τ ω => y*q g) (map_mul q g (a i)))
      _ = q f*x i*q f :=
        congrArg₂ (fun y z : Q τ ω => y*z)
          (congrArg₂ (fun y z : Q τ ω => y*z) he (ha i)) he
  have hzero : quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (g*a i*g))=0 := by
    rw [hclass]
    exact hx i
  obtain ⟨hl,hr⟩ := boundedCornerCenter_supported τ g (a i) hg δ hδ hgl
  exact ⟨hl,hr,boundedCornerCenter_trace τ g (a i) hg δ hδ hgl,
    (boundedCornerCenter_quotient τ ω g (a i) hg δ hδ hgl hzero).trans hclass⟩

end

/-! Scalar normalization preserves exact corner support and centering. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_supported_centered_contraction (g b : Bounded M)
    (hl : g*b=b) (hr : b*g=b) (hc : ∀ j,τ.trace (b.val j)=0) :
    ∃ c : ℂ,c ≠ 0 ∧ ∃ a : Bounded M,
      g*a=a ∧ a*g=a ∧ (∀ j,‖a.val j‖ ≤ 1) ∧
      (∀ j,τ.trace (a.val j)=0) ∧ b=c • a := by
  obtain ⟨C,hC,hbound⟩ := b.property
  let r : ℝ := C+1
  have hpos : 0 < r := by dsimp [r]; linarith
  have hne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  refine ⟨(r : ℂ),hne,(r : ℂ)⁻¹ • b,?_,?_,?_,?_,?_⟩
  · rw [mul_smul_comm,hl]
  · rw [smul_mul_assoc,hr]
  · intro j
    change ‖(r : ℂ)⁻¹ • b.val j‖ ≤ 1
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
    apply (inv_mul_le_iff₀ hpos).mpr
    simpa only [mul_one] using (hbound j).trans (by dsimp [r]; linarith)
  · intro j
    change τ.trace ((r : ℂ)⁻¹ • b.val j)=0
    rw [TracialRepresentation.trace_smul,hc j,mul_zero]
  · rw [smul_smul,mul_inv_cancel₀ hne,one_smul]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/
section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_partial_residual_annihilation (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) :
    v*(1-p)=0 ∧ star v*(1-p)=0 ∧ (1-p)*v=0 ∧ (1-p)*star v=0 := by
  have hpf : p*(1-p)=0 := by rw [mul_sub,mul_one,hp.isIdempotentElem.eq,sub_self]
  have hstar : star (1-p)=1-p := by rw [star_sub,star_one,hp.isSelfAdjoint.star_eq]
  have hright (a : Q τ ω) (ha : star a*a=p) : a*(1-p)=0 := by
    apply trace_square_faithful τ ω
    rw [star_mul,hstar,mul_assoc,← mul_assoc (star a),ha,hpf,mul_zero]
    exact (traceLinear τ ω).map_zero
  have h1 := hright v hi
  have h2 := hright (star v) (by simpa only [star_star] using hf)
  refine ⟨h1,h2,?_,?_⟩
  · simpa only [star_mul,hstar,star_star,star_zero] using congrArg star h2
  · simpa only [star_mul,hstar,star_zero] using congrArg star h1

theorem quotient_residual_compression_trace (v p z : Q τ ω)
    (hp : IsStarProjection p) (hf : v*star v=p) :
    quotientTrace τ ω ((1-p)*z*(1-p)) =
      quotientTrace τ ω z - quotientTrace τ ω (star v*z*v) := by
  have hff : (1-p)*(1-p)=1-p := by
    noncomm_ring [hp.isIdempotentElem.eq]
  calc quotientTrace τ ω ((1-p)*z*(1-p)) = quotientTrace τ ω (z*(1-p)*(1-p)) := by
         rw [mul_assoc (1-p) z (1-p),quotientTrace_mul_comm τ ω (1-p) (z*(1-p))]
       _ = quotientTrace τ ω (z*(1-p)) := by rw [mul_assoc,hff]
       _ = quotientTrace τ ω z - quotientTrace τ ω (z*p) := by
         rw [mul_sub,mul_one]
         exact (traceLinear τ ω).map_sub z (z*p)
       _ = quotientTrace τ ω z - quotientTrace τ ω (star v*z*v) := by
         rw [← hf,← mul_assoc z v (star v),quotientTrace_mul_comm τ ω (z*v) (star v),mul_assoc]

theorem quotient_residual_centered (v p z : Q τ ω) (hp : IsStarProjection p)
    (hf : v*star v=p) (hz : quotientTrace τ ω z=0)
    (hvz : quotientTrace τ ω (star v*z*v)=0) :
    quotientTrace τ ω ((1-p)*z*(1-p))=0 := by
  rw [quotient_residual_compression_trace τ ω v p z hp hf,hz,hvz,sub_self]

theorem algebraPatchingWord_append {A : Type*} [Monoid A] [Star A]
    (v : A) (xs ys : List (Bool × A)) :
    algebraPatchingWord v (xs++ys)=algebraPatchingWord v xs*algebraPatchingWord v ys := by
  induction xs with
  | nil => simp [algebraPatchingWord]
  | cons a xs ih => simp only [List.cons_append,algebraPatchingWord,ih,mul_assoc]

theorem quotient_residual_word_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hf : v*star v=p) (x : ℕ → Q τ ω)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0)
    (i j : ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    quotientTrace τ ω ((1-p)*(x i *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,x j)]))*(1-p))=0 := by
  apply quotient_residual_centered τ ω v p _ hp hf
  · exact hm (some i) (some j) xs s
  · have h := hm none none ((true,i)::(xs++[(s,j)])) false
    simpa [optionalCoefficient,algebraPatchingWord,algebraSignedLetter,
      algebraPatchingWord_append,mul_assoc] using h

/-! All residual middle coefficients from exact independence: the original
centered coefficients, words with two centered endpoints, and the vanishing
compressions when an endpoint is the unit. -/

theorem quotient_residual_signed_annihilation (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (s : Bool) :
    (1-p)*algebraSignedLetter v s=0 ∧ algebraSignedLetter v s*(1-p)=0 := by
  obtain ⟨h1,h2,h3,h4⟩ := quotient_partial_residual_annihilation τ ω v p hp hi hf
  cases s
  · exact ⟨h3,h1⟩
  · exact ⟨h4,h2⟩

theorem quotient_residual_word_unit_left (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (ys : List (Bool × Q τ ω)) (hy : ys ≠ []) :
    (1-p)*algebraPatchingWord v ys=0 := by
  cases ys with
  | nil => exact (hy rfl).elim
  | cons a ys =>
    simp only [algebraPatchingWord,← mul_assoc,
      (quotient_residual_signed_annihilation τ ω v p hp hi hf a.1).1,zero_mul]

theorem quotient_residual_word_unit_right (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (ys : List (Bool × Q τ ω)) (s : Bool) :
    algebraPatchingWord v (ys++[(s,1)])*(1-p)=0 := by
  rw [algebraPatchingWord_append]
  simp only [algebraPatchingWord,mul_one,mul_assoc,
    (quotient_residual_signed_annihilation τ ω v p hp hi hf s).2,mul_zero]

theorem quotient_residual_all_words_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (x : ℕ → Q τ ω)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    quotientTrace τ ω ((1-p)*(optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
        [(s,optionalCoefficient x last)]))*(1-p))=0 := by
  cases first with
  | none =>
    simp only [optionalCoefficient,one_mul]
    rw [quotient_residual_word_unit_left τ ω v p hp hi hf _ (by simp),zero_mul]
    exact (traceLinear τ ω).map_zero
  | some i =>
    cases last with
    | none =>
      change quotientTrace τ ω ((1-p)*(x i*algebraPatchingWord v
        (xs.map (fun a => (a.1,x a.2)) ++ [(s,1)]))*(1-p))=0
      rw [mul_assoc,mul_assoc,
        quotient_residual_word_unit_right τ ω v p hp hi hf,mul_zero,mul_zero]
      exact (traceLinear τ ω).map_zero
    | some j => exact quotient_residual_word_centered τ ω v p hp hf x hm i j xs s

theorem quotient_residual_coefficient_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hf : v*star v=p) (x : ℕ → Q τ ω) (hc : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0) (i : ℕ) :
    quotientTrace τ ω ((1-p)*x i*(1-p))=0 := by
  apply quotient_residual_centered τ ω v p (x i) hp hf (hc i)
  simpa [optionalCoefficient,algebraPatchingWord,algebraSignedLetter] using
      hm none none [(true,i)] false

end

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem residualWordFamily_compression_centered (v p : Q τ ω) (hp : IsStarProjection p)
    (hi : star v*v=p) (hf : v*star v=p) (x : ℕ → Q τ ω)
    (hc : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
      quotientTrace τ ω (optionalCoefficient x first *
        algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
          [(s,optionalCoefficient x last)]))=0) :
    ∀ i,quotientTrace τ ω ((1-p)*residualWordFamily τ ω v x i*(1-p))=0 := by
  intro i
  unfold residualWordFamily
  cases h : Encodable.decode (α := ResidualWordIndex) i with
  | none => simp only [mul_zero,zero_mul]; exact (traceLinear τ ω).map_zero
  | some k =>
    cases k with
    | inl j => exact quotient_residual_coefficient_centered τ ω v p hp hf x hc hm j
    | inr k =>
      rcases k with ⟨first,last,xs,s⟩
      exact quotient_residual_all_words_centered τ ω v p hp hi hf x hm first last xs s

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotientCornerCenter_supported (f z : Q τ ω) (hf : f*f=f) :
    f*quotientCornerCenter τ ω f z=quotientCornerCenter τ ω f z ∧
    quotientCornerCenter τ ω f z*f=quotientCornerCenter τ ω f z := by
  constructor
  · simp only [quotientCornerCenter,mul_sub,mul_smul_comm,← mul_assoc,hf]
  · simp only [quotientCornerCenter,sub_mul,smul_mul_assoc,mul_assoc,hf]

theorem quotientCornerCenter_trace (f z : Q τ ω) (ht : quotientTrace τ ω f ≠ 0) :
    quotientTrace τ ω (quotientCornerCenter τ ω f z)=0 := by
  unfold quotientCornerCenter
  change (traceLinear τ ω) (_-_) = 0
  rw [map_sub]
  change quotientTrace τ ω (f*z*f)-quotientTrace τ ω
    ((quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f)=0
  rw [trace_smul,div_mul_cancel₀ _ ht,sub_self]

theorem cyclicResidualFamily_supported (f : Q τ ω) (hf : f*f=f) (y : ℕ → Q τ ω) :
    ∀ i,f*cyclicResidualFamily τ ω f y i*f=cyclicResidualFamily τ ω f y i := by
  intro i
  unfold cyclicResidualFamily
  cases Encodable.decode (α := CyclicFamilyIndex) i with
  | none => simp only [mul_zero,zero_mul]
  | some k =>
    cases k with
    | inl j => simp only [cyclicFamilyValue,← mul_assoc,hf]; simp only [mul_assoc,hf]
    | inr ab =>
      obtain ⟨hl,hr⟩ := quotientCornerCenter_supported τ ω f
        (optionalCoefficient y ab.2*optionalCoefficient y ab.1) hf
      exact (congrArg (fun z => z*f) hl).trans hr

theorem cyclicResidualFamily_centered (f : Q τ ω) (hf : f*f=f)
    (ht : quotientTrace τ ω f ≠ 0) (y : ℕ → Q τ ω)
    (hy : ∀ i,quotientTrace τ ω (f*y i*f)=0) :
    ∀ i,quotientTrace τ ω (f*cyclicResidualFamily τ ω f y i*f)=0 := by
  intro i
  rw [cyclicResidualFamily_supported τ ω f hf]
  unfold cyclicResidualFamily
  cases Encodable.decode (α := CyclicFamilyIndex) i with
  | none => exact (traceLinear τ ω).map_zero
  | some k =>
    cases k with
    | inl j => exact hy j
    | inr ab => exact quotientCornerCenter_trace τ ω f _ ht

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem boundedPartialResidual_projection (v : ℕ → PartialUnitary M) (j : ℕ) :
    IsStarProjection ((boundedPartialResidual v).val j) := (v j).support.property.one_sub

theorem boundedPartialResidual_mem (v : ℕ → PartialUnitary M)
    (hv : ∀ j,(v j).val.val ∈ N) (j : ℕ) :
    ((boundedPartialResidual v).val j).val ∈ N := by
  have hs : (v j).support.val.val ∈ N := by
    rw [← (v j).unitary.initial]
    have hstar : star ((v j).val.val) ∈ N.toStarSubalgebra :=
      star_mem (show (v j).val.val ∈ N.toStarSubalgebra from hv j)
    exact N.mul_mem hstar (hv j)
  exact N.sub_mem N.one_mem hs

theorem maskPartialSequence_quotient (τ : TracialRepresentation M) (l : Filter ℕ)
    (S : Set ℕ) (hS : S ∈ l) (v : ℕ → PartialUnitary M) :
    quotientMap τ l (boundedPartialUnitary (maskPartialSequence S v))=
      quotientMap τ l (boundedPartialUnitary v) ∧
    quotientMap τ l (boundedPartialSupport (maskPartialSequence S v))=
      quotientMap τ l (boundedPartialSupport v) := by
  constructor
  · apply quotientMap_eq_of_eventuallyEq τ
    filter_upwards [hS] with j hj
    change (maskPartialSequence S v j).val=(v j).val
    simp only [maskPartialSequence,ite_eq_left hj]
  · apply quotientMap_eq_of_eventuallyEq τ
    filter_upwards [hS] with j hj
    change (maskPartialSequence S v j).support.val=(v j).support.val
    simp only [maskPartialSequence,ite_eq_left hj]

theorem maskPartialSequence_mem (S : Set ℕ) (v : ℕ → PartialUnitary M)
    (hv : ∀ j,(v j).val.val ∈ N) : ∀ j,(maskPartialSequence S v j).val.val ∈ N := by
  intro j
  by_cases hj : j ∈ S
  · simpa only [maskPartialSequence,ite_eq_left hj] using hv j
  · simp only [maskPartialSequence,ite_eq_right hj]
    exact N.zero_mem

theorem maskPartialSequence_orthogonal (S : Set ℕ) (v w : ℕ → PartialUnitary M)
    (hw : ∀ j ∈ S,(w j).support ≤ unitResidual (v j)) :
    ∀ j,(v j).support.val*(maskPartialSequence S w j).support.val=0 := by
  intro j
  by_cases hj : j ∈ S
  · simp only [maskPartialSequence,ite_eq_left hj]
    have hh := hw j hj
    change (1-(v j).support.val)*(w j).support.val=(w j).support.val at hh
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  · simp [maskPartialSequence,hj,zeroPartialUnitary]

theorem patchPartialSequence_bounded (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    boundedPartialUnitary (patchPartialSequence v w h)=boundedPartialUnitary v+boundedPartialUnitary w ∧
    boundedPartialSupport (patchPartialSequence v w h)=boundedPartialSupport v+boundedPartialSupport w :=
  ⟨rfl,rfl⟩

theorem patchPartialSequence_mem (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0)
    (hv : ∀ j,(v j).val.val ∈ N) (hw : ∀ j,(w j).val.val ∈ N) :
    ∀ j,(patchPartialSequence v w h j).val.val ∈ N :=
  fun j => N.add_mem (hv j) (hw j)

end

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

private theorem exists_supported_centered_contraction_family
    (g : Bounded M) (b : ℕ → Bounded M)
    (hl : ∀ i, g*b i=b i) (hr : ∀ i, b i*g=b i)
    (hc : ∀ i j, τ.trace ((b i).val j)=0) :
    ∃ (c : ℕ → ℂ) (a : ℕ → Bounded M),
      (∀ i, c i ≠ 0) ∧ (∀ i, g*a i=a i) ∧ (∀ i, a i*g=a i) ∧
      (∀ i j, ‖(a i).val j‖ ≤ 1) ∧ (∀ i j, τ.trace ((a i).val j)=0) ∧
      ∀ i, b i=c i • a i := by
  choose c hcne a hal har han hac hae using fun i =>
    exists_supported_centered_contraction (H := H) (M := M) τ g (b i) (hl i) (hr i) (hc i)
  exact ⟨c, a, hcne, hal, har, han, hac, hae⟩

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

private theorem residual_quotient_increment_of_normalized_representatives
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (x : ℕ → Q τ ω)
    (g : Bounded M) (hg : ∀ j,IsStarProjection (g.val j))
    (hgN : ∀ j,(g.val j).val ∈ N) (hg0 : ∀ j,g.val j ≠ 0)
    (hgf : g.val =ᶠ[(ω : Filter ℕ)] (boundedPartialResidual v).val)
    (c : ℕ → ℂ) (a : ℕ → Bounded M)
    (han : ∀ i j, ‖(a i).val j‖ ≤ 1) (hac : ∀ i j,τ.trace ((a i).val j)=0)
    (hal : ∀ i,g*a i=a i) (har : ∀ i,a i*g=a i)
    (hscale : ∀ i,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
        quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)=
      c i • quotientMap τ (ω : Filter ℕ) (a i)) :
    ∃ w : ℕ → PartialUnitary M,
      (∀ j,(w j).val.val ∈ N) ∧
      (∀ j,(v j).support.val*(w j).support.val=0) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (
          optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
            quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x a.2*
              quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
                quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) last)]))=0 := by
  classical
  let f := boundedPartialResidual v
  obtain ⟨w,hwN,hws,hwt,hwm⟩ := exists_quotient_corner_partial_sequence (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
    ω hω g hg hgN hg0 a han hac hal har
  let S : Set ℕ := {j | g.val j=f.val j}
  have hS : S ∈ (ω : Filter ℕ) := hgf
  have he := maskPartialSequence_quotient τ (ω : Filter ℕ) S hS w
  have heg := quotientMap_eq_of_eventuallyEq τ (ω : Filter ℕ) g f hgf
  refine ⟨maskPartialSequence S w,maskPartialSequence_mem S w hwN,?_,?_,?_⟩
  · apply maskPartialSequence_orthogonal S v w
    intro j hj
    change f.val j*(w j).support.val=(w j).support.val
    exact (congrArg (fun q => q*(w j).support.val) hj.symm).trans (hws j)
  · exact (congrArg₂ (fun q r => (quotientTrace τ ω q).re/4 ≤
        (quotientTrace τ ω r).re) heg he.2.symm).mp hwt
  · intro first last xs s
    let F : Q τ ω → ℂ := fun u => quotientTrace τ ω (
      optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) f*x i*
        quotientMap τ (ω : Filter ℕ) f) first *
      algebraPatchingWord u (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) f*x a.2*
        quotientMap τ (ω : Filter ℕ) f)) ++ [(s,optionalCoefficient
          (fun i => quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f) last)]))
    refine (congrArg F he.1).trans ?_
    exact (congrArg (quotientTrace τ ω)
      (ordered_moment_scale _ _ _ c hscale first last xs s)).trans
      ((trace_smul τ ω _ _).trans
        ((congrArg (fun z => _ * z) (hwm first last xs s)).trans (mul_zero _)))

private theorem residual_quotient_increment_of_representatives
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (δ : ℝ) (hδ : 0 < δ) (g : Bounded M)
    (hg : ∀ j,IsStarProjection (g.val j)) (hgl : ∀ j,δ ≤ (τ.trace (g.val j)).re)
    (hgf : g.val =ᶠ[(ω : Filter ℕ)] (boundedPartialResidual v).val)
    (hgor : ∀ j,g.val j=(boundedPartialResidual v).val j ∨ g.val j=1)
    (b : ℕ → Bounded M) (hb : ∀ i,
      g*b i=b i ∧ b i*g=b i ∧ (∀ j,τ.trace ((b i).val j)=0) ∧
      quotientMap τ (ω : Filter ℕ) (b i)=
        quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
          quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) :
    ∃ w : ℕ → PartialUnitary M,
      (∀ j,(w j).val.val ∈ N) ∧
      (∀ j,(v j).support.val*(w j).support.val=0) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (
          optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
            quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x a.2*
              quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
                quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) last)]))=0 := by
  classical
  let f := boundedPartialResidual v
  have hgN : ∀ j,(g.val j).val ∈ N := by
    intro j
    rcases hgor j with h | h
    · rw [h]; exact boundedPartialResidual_mem v hv j
    · rw [h]; exact N.one_mem
  have hg0 : ∀ j,g.val j ≠ 0 := by
    intro j hz
    have hh := hgl j
    have hztrace : τ.trace (0 : M.toStarSubalgebra)=0 := inner_zero_right _
    rw [hz,hztrace,Complex.zero_re] at hh
    exact (not_le_of_gt hδ) hh
  obtain ⟨c,a,hcne,hal,har,han,hac,hae⟩ :=
    exists_supported_centered_contraction_family (H := H) (M := M) τ g b
      (fun i => (hb i).1) (fun i => (hb i).2.1) (fun i => (hb i).2.2.1)
  have hscale (i : ℕ) : quotientMap τ (ω : Filter ℕ) f*x i*quotientMap τ (ω : Filter ℕ) f=
      c i • quotientMap τ (ω : Filter ℕ) (a i) := by
    exact (hb i).2.2.2.symm.trans
      ((congrArg (quotientMap τ (ω : Filter ℕ)) (hae i)).trans
        (quotientMap_smul τ (ω : Filter ℕ) (c i) (a i)))
  exact residual_quotient_increment_of_normalized_representatives (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v x g hg hgN hg0 hgf c a han hac hal har hscale

theorem exists_residual_quotient_increment
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (ht : 0 < (quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re)
    (x : ℕ → Q τ ω)
    (hc : ∀ i,quotientTrace τ ω (
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))=0) :
    ∃ w : ℕ → PartialUnitary M,
      (∀ j,(w j).val.val ∈ N) ∧
      (∀ j,(v j).support.val*(w j).support.val=0) ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
        (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        quotientTrace τ ω (
          optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
            quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) first *
          algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w))
            (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x a.2*
              quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))) ++
              [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*x i*
                quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) last)]))=0 := by
  let f := boundedPartialResidual v
  obtain ⟨δ,hδ,g,hg,hgl,hgf,hgor,b,hb⟩ :=
    exists_eventually_centered_corner_representatives (H := H) (M := M) τ ω f
      (boundedPartialResidual_projection v) ht x hc
  exact residual_quotient_increment_of_representatives (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v hv x δ hδ g hg hgl hgf hgor b hb

end

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_patch_residual_bound (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0)
    (ht : (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re/4 ≤
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))).re) :
    (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ)
      (boundedPartialResidual (patchPartialSequence v w h)))).re ≤
      (3/4 : ℝ)*(quotientTrace τ ω
        (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re := by
  have he : boundedPartialResidual (patchPartialSequence v w h)=
      boundedPartialResidual v-boundedPartialSupport w := by
    unfold boundedPartialResidual
    rw [(patchPartialSequence_bounded v w h).2]
    abel
  have hsub : quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v) -
        quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w)) =
      quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) -
        quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w)) :=
    (traceLinear τ ω).map_sub
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))
      (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))
  rw [he,map_sub,hsub,Complex.sub_re]
  linarith

end

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem bounded_orthogonal_patch_supported (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    boundedPartialResidual v*boundedPartialUnitary w=boundedPartialUnitary w ∧
    boundedPartialUnitary w*boundedPartialResidual v=boundedPartialUnitary w := by
  have hl (j : ℕ) : (v j).support.val*(w j).val=0 := by
    calc (v j).support.val*(w j).val =
        (v j).support.val*((w j).support.val*(w j).val) := by rw [(w j).unitary.support_mul]
         _ = 0 := by rw [← mul_assoc,h j,zero_mul]
  have hr (j : ℕ) : (w j).val*(v j).support.val=0 := by
    have hqp : (w j).support.val*(v j).support.val=0 := by
      simpa only [star_mul,(v j).support.property.isSelfAdjoint.star_eq,
        (w j).support.property.isSelfAdjoint.star_eq,star_zero] using congrArg star (h j)
    calc (w j).val*(v j).support.val =
        ((w j).val*(w j).support.val)*(v j).support.val := by rw [(w j).unitary.mul_support]
         _ = 0 := by rw [mul_assoc,hqp,mul_zero]
  constructor
  · apply Subtype.ext
    funext j
    change (1-(v j).support.val)*(w j).val=(w j).val
    rw [sub_mul,one_mul,hl j,sub_zero]
  · apply Subtype.ext
    funext j
    change (w j).val*(1-(v j).support.val)=(w j).val
    rw [mul_sub,mul_one,hr j,sub_zero]

theorem quotient_orthogonal_patch_supported (ω : Ultrafilter ℕ)
    (v w : ℕ → PartialUnitary M) (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    ∀ s,quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)*
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s ∧
    algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s*
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) s := by
  have hleft := congrArg (quotientMap τ (ω : Filter ℕ)) (bounded_orthogonal_patch_supported v w h).1
  have hright := congrArg (quotientMap τ (ω : Filter ℕ)) (bounded_orthogonal_patch_supported v w h).2
  rw [map_mul] at hleft hright
  have hf : star (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))=
      quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v) :=
    (((boundedPartialSupport_projection v).one_sub).map
      (quotientStarAlgHom τ (ω : Filter ℕ))).isSelfAdjoint.star_eq
  intro s
  cases s with
  | false => exact ⟨hleft,hright⟩
  | true =>
    constructor
    · simpa only [star_mul,hf,algebraSignedLetter,↓reduceIte] using congrArg star hright
    · simpa only [star_mul,hf,algebraSignedLetter,↓reduceIte] using congrArg star hleft

theorem patchPartialSequence_extends (v w : ℕ → PartialUnitary M)
    (h : ∀ j,(v j).support.val*(w j).support.val=0) :
    ∀ j,v j ≤ patchPartialSequence v w h j := by
  intro j
  change ((v j).unitary.patch (w j).unitary (h j)).val*(v j).support.val=(v j).val
  simpa only [(v j).unitary.initial] using
    (v j).unitary.patch_extends (w j).unitary (h j)

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

private theorem exact_residual_patch_of_centered_family (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (ht : 0 < (quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re)
    (x : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x)
    (hz : ∀ i, let f := quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)
      let V := quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)
      quotientTrace τ ω (f*cyclicResidualFamily τ ω f (residualWordFamily τ ω V x) i*f)=0) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual u))).re ≤
        (3/4 : ℝ)*(quotientTrace τ ω
          (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re := by
  let V := quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)
  let f := quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)
  have hf : f*f=f :=
    (((boundedPartialSupport_projection v).one_sub).map
      (quotientStarAlgHom τ (ω : Filter ℕ))).isIdempotentElem.eq
  let y := residualWordFamily τ ω V x
  let z := cyclicResidualFamily τ ω f y
  obtain ⟨w,hwN,hortho,htrace,hmw⟩ := exists_residual_quotient_increment (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
    ω hω v hv ht z hz
  have hzs : (fun i => f*z i*f)=z := funext (cyclicResidualFamily_supported τ ω f hf y)
  have hwexact : ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)) z := by
    change ExactOrderedMoments τ ω _ (fun i => f*z i*f) at hmw
    rw [hzs] at hmw
    exact hmw
  refine ⟨patchPartialSequence v w hortho,patchPartialSequence_mem v w hortho hv hwN,
    patchPartialSequence_extends v w hortho,?_,quotient_patch_residual_bound τ ω v w hortho htrace⟩
  have he := (congrArg (quotientMap τ (ω : Filter ℕ))
    (patchPartialSequence_bounded v w hortho).1).trans
    (map_add (quotientMap τ (ω : Filter ℕ)) _ _)
  exact (congrArg (fun u => ExactOrderedMoments τ ω u x) he).mpr
    (exactOrderedMoments_add_of_cyclic τ ω V _ f x hm
      (quotient_orthogonal_patch_supported τ ω v w hortho) hwexact)

theorem exists_exact_residual_patch (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (ht : 0 < (quotientTrace τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual u))).re ≤
        (3/4 : ℝ)*(quotientTrace τ ω
          (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re := by
  let V := quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)
  let P := quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v)
  let f := quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)
  have hp : IsStarProjection P := (boundedPartialSupport_projection v).map
    (quotientStarAlgHom τ (ω : Filter ℕ))
  have hfp : f=1-P := by simp only [f,P,boundedPartialResidual,map_sub,map_one]
  have hf : f*f=f := by rw [hfp]; exact hp.one_sub.isIdempotentElem.eq
  have hi : star V*V=P := by
    dsimp only [V,P]
    rw [← quotientMap_star,← map_mul,boundedPartialUnitary_initial]
  have hfinal : V*star V=P := by
    dsimp only [V,P]
    rw [← quotientMap_star,← map_mul,boundedPartialUnitary_final]
  let y := residualWordFamily τ ω V x
  let z := cyclicResidualFamily τ ω f y
  have hy : ∀ i,quotientTrace τ ω (f*y i*f)=0 := by
    rw [hfp]
    exact residualWordFamily_compression_centered τ ω V P hp hi hfinal x hx hm
  have hnonzero : quotientTrace τ ω f ≠ 0 := by
    intro hz
    have hh : 0 < (quotientTrace τ ω f).re := ht
    rw [hz,Complex.zero_re] at hh
    exact lt_irrefl _ hh
  have hz : ∀ i,quotientTrace τ ω (f*z i*f)=0 :=
    cyclicResidualFamily_centered τ ω f hf hnonzero y hy
  exact exact_residual_patch_of_centered_family (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v hv ht x hm hz

end

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem quotientResidualTrace_nonneg (ω : Ultrafilter ℕ) (v : ℕ → PartialUnitary M) :
    0 ≤ quotientResidualTrace τ ω v := by
  have hp := ((boundedPartialSupport_projection v).one_sub).map
    (quotientStarAlgHom τ (ω : Filter ℕ))
  change IsStarProjection (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) at hp
  have hh := trace_square_nonneg τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))
  rwa [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hh

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

theorem exists_exact_residual_step_oai (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      quotientResidualTrace τ ω u ≤ (3/4 : ℝ)*quotientResidualTrace τ ω v := by
  by_cases ht : 0 < quotientResidualTrace τ ω v
  · exact exists_exact_residual_patch (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep ω hω v hv ht x hx hm
  · have hz := le_antisymm (not_lt.mp ht) (quotientResidualTrace_nonneg τ ω v)
    exact ⟨v,hv,fun _ => le_rfl,hm,by rw [hz,mul_zero]⟩

end

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_exact_residual_step_oai.{u_1} := @OAI.Generator.Tracial.exists_exact_residual_step_oai.{u_1}
