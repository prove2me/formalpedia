-- Prove2me | solution 1 for OAI.Generator.Tracial.exactOrderedMoments_add_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:21:35.331144+00:00
-- url     : https://prove2.me/submissions/56661f2e-c376-488b-8694-18251170be3c

import Mathlib
import Definitions.Def_OAIQ11Fg014

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
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
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem residualWordFamily_encode (v : Q τ ω) (x : ℕ → Q τ ω) (k : ResidualWordIndex) :
    residualWordFamily τ ω v x (Encodable.encode k)=residualWordValue τ ω v x k := by
  simp [residualWordFamily]

theorem residualWordFamily_contains_coefficient (v : Q τ ω) (x : ℕ → Q τ ω) (i : ℕ) :
    ∃ j,residualWordFamily τ ω v x j=x i :=
  ⟨Encodable.encode (Sum.inl i : ResidualWordIndex),residualWordFamily_encode τ ω v x (.inl i)⟩

theorem residualWordFamily_contains_word (v : Q τ ω) (x : ℕ → Q τ ω)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    ∃ j,residualWordFamily τ ω v x j=optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]) :=
  ⟨Encodable.encode (Sum.inr (first,last,xs,s) : ResidualWordIndex),
    residualWordFamily_encode τ ω v x (.inr (first,last,xs,s))⟩

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

theorem residualWordFamily_contains_run (v : Q τ ω) (x : ℕ → Q τ ω)
    (i : ℕ) (pre : List (Bool × ℕ)) :
    ∃ j,residualWordFamily τ ω v x j=x i*
      algebraPatchingWord v (pre.map (fun a => (a.1,x a.2))) := by
  induction pre using List.reverseRecOn with
  | nil => simpa [algebraPatchingWord] using residualWordFamily_contains_coefficient τ ω v x i
  | append_singleton pre a ih =>
    simpa [List.map_append,optionalCoefficient] using
      residualWordFamily_contains_word τ ω v x (some i) (some a.2) pre a.1

theorem residualWordFamily_contains_outer_run (v : Q τ ω) (x : ℕ → Q τ ω)
    (first : Option ℕ) (pre : List (Bool × ℕ)) :
    ∃ j : Option ℕ,optionalCoefficient (residualWordFamily τ ω v x) j=
      optionalCoefficient x first*algebraPatchingWord v (pre.map (fun a => (a.1,x a.2))) := by
  induction pre using List.reverseRecOn with
  | nil =>
    cases first with
    | none => exact ⟨none,by simp [optionalCoefficient,algebraPatchingWord]⟩
    | some i =>
      obtain ⟨j,hj⟩ := residualWordFamily_contains_coefficient τ ω v x i
      exact ⟨some j,by simpa [optionalCoefficient,algebraPatchingWord] using hj⟩
  | append_singleton pre a ih =>
    obtain ⟨j,hj⟩ := residualWordFamily_contains_word τ ω v x first (some a.2) pre a.1
    exact ⟨some j,by simpa [List.map_append,optionalCoefficient] using hj⟩

/-- Every actual ordered mixed term is either the original word or an ordered
increment word with enumerated internal blocks and an explicit old prefix. -/
theorem algebraMixedTail_normalize (v w : Q τ ω) (x : ℕ → Q τ ω)
    (last : Option ℕ) (b s : Bool) (xs : List (Bool × Bool × ℕ)) :
    algebraMixedTail v w x last b s xs =
      algebraPatchingWord v (xs.map (fun a => (a.2.1,x a.2.2)) ++
        [(s,optionalCoefficient x last)]) ∨
    ∃ pre : List (Bool × ℕ), ∃ ys : List (Bool × ℕ), ∃ t : Bool, ∃ last' : Option ℕ,
      algebraMixedTail v w x last b s xs =
        algebraPatchingWord v (pre.map (fun a => (a.1,x a.2))) *
        algebraPatchingWord w (ys.map (fun a => (a.1,residualWordFamily τ ω v x a.2)) ++
          [(t,optionalCoefficient (residualWordFamily τ ω v x) last')]) := by
  induction xs with
  | nil =>
    cases b with
    | false => exact Or.inl (by simp [algebraMixedTail,algebraPatchingWord])
    | true =>
      obtain ⟨j,hj⟩ := residualWordFamily_contains_outer_run τ ω v x last []
      refine Or.inr ⟨[],[],s,j,?_⟩
      simp only [List.map_nil,algebraPatchingWord,mul_one] at hj
      simp [algebraMixedTail,algebraPatchingWord,hj]
  | cons a xs ih =>
    rcases a with ⟨c,t,i⟩
    cases c with
    | false =>
      rcases ih with h | ⟨pre,ys,u,last',h⟩
      · exact Or.inl (by simp [algebraMixedTail,algebraPatchingWord,h])
      · exact Or.inr ⟨(t,i)::pre,ys,u,last',by
          simp only [algebraMixedTail,Bool.false_eq_true,↓reduceIte,h,List.map_cons,
            algebraPatchingWord,mul_assoc]⟩
    | true =>
      rcases ih with h | ⟨pre,ys,u,last',h⟩
      · obtain ⟨j,hj⟩ := residualWordFamily_contains_word τ ω v x (some i) last
          (xs.map (fun a => (a.2.1,a.2.2))) s
        refine Or.inr ⟨[],[],t,some j,?_⟩
        simp only [algebraMixedTail,↓reduceIte,h,List.map_nil,List.nil_append,
          algebraPatchingWord,one_mul,mul_one,optionalCoefficient]
        simp only [List.map_map,Function.comp_def,optionalCoefficient] at hj
        rw [hj,mul_assoc]
      · obtain ⟨j,hj⟩ := residualWordFamily_contains_run τ ω v x i pre
        refine Or.inr ⟨[],(t,j)::ys,u,last',?_⟩
        simp only [algebraMixedTail,↓reduceIte,h,List.map_nil,List.map_cons,
          List.cons_append,algebraPatchingWord,one_mul]
        rw [hj]
        simp only [mul_assoc]

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/
section
open UltrapowerBridge Filter

theorem algebraWordCore_endpoints {A : Type*} [Monoid A] [Star A]
    (v : A) (x : ℕ → A) (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) :
    algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
      [(s,optionalCoefficient x last)])=algebraWordCore v x s xs*optionalCoefficient x last := by
  induction xs with
  | nil => simp [algebraPatchingWord,algebraWordCore]
  | cons a xs ih => simp [algebraPatchingWord,algebraWordCore,ih,mul_assoc]

theorem algebraWordCore_map {A : Type*} [Monoid A] [Star A]
    (w : A) (x y : ℕ → A) (k : ℕ → ℕ) (h : ∀ i,x i=y (k i))
    (s : Bool) (xs : List (Bool × ℕ)) :
    algebraWordCore w x s xs=algebraWordCore w y s (xs.map (fun a => (a.1,k a.2))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [algebraWordCore,List.map_cons,h,ih]

theorem algebraWordCore_support {A : Type*} [Monoid A] [Star A]
    (w f : A) (hw : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (x : ℕ → A) (s : Bool) (xs : List (Bool × ℕ)) :
    f*algebraWordCore w x s xs=algebraWordCore w x s xs ∧
      algebraWordCore w x s xs*f=algebraWordCore w x s xs := by
  induction xs with
  | nil => exact hw s
  | cons a xs ih =>
    constructor
    · simp only [algebraWordCore,← mul_assoc,(hw a.1).1]
    · simp only [algebraWordCore,mul_assoc,ih.2]

theorem algebraWordCore_compress {A : Type*} [Monoid A] [Star A]
    (w f : A) (hw : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (x : ℕ → A) (s : Bool) (xs : List (Bool × ℕ)) :
    algebraWordCore w (fun i => f*x i*f) s xs=algebraWordCore w x s xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [algebraWordCore,ih]
    calc algebraSignedLetter w a.1*(f*x a.2*f)*algebraWordCore w x s xs =
        (algebraSignedLetter w a.1*f)*x a.2*(f*algebraWordCore w x s xs) := by
          simp only [mul_assoc]
         _ = _ := by rw [(hw a.1).2,(algebraWordCore_support w f hw x s xs).1]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem exactOrderedMoments_core (w : Q τ ω) (x : ℕ → Q τ ω)
    (h : ExactOrderedMoments τ ω w x) (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) :
    quotientTrace τ ω (algebraWordCore w x s xs*optionalCoefficient x last)=0 := by
  have hh := h none last xs s
  rw [algebraWordCore_endpoints] at hh
  simpa only [optionalCoefficient,one_mul] using hh

theorem trace_supported_cyclic_compression (c f z : Q τ ω)
    (hl : f*c=c) (hr : c*f=c) :
    quotientTrace τ ω (c*(f*z*f))=quotientTrace τ ω (c*z) := by
  calc quotientTrace τ ω (c*(f*z*f)) = quotientTrace τ ω ((c*(f*z))*f) := by simp only [mul_assoc]
       _ = quotientTrace τ ω (f*(c*(f*z))) := quotientTrace_mul_comm τ ω _ _
       _ = quotientTrace τ ω (c*z) := by rw [← mul_assoc f c,hl,← mul_assoc c f,hr]

/-- Transfer exact moments from compressed internal coefficients and centered
cyclic endpoint products. The scalar correction uses the moment with both
endpoints equal to the unit. -/
theorem exact_moment_of_cyclic_family (w f : Q τ ω)
    (hw : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (y z : ℕ → Q τ ω) (k : ℕ → ℕ) (hk : ∀ i,f*y i*f=z (k i))
    (hc : ∀ a b : Option ℕ,∃ j : ℕ,∃ c : ℂ,
      f*(optionalCoefficient y b*optionalCoefficient y a)*f=z j+c • f)
    (hm : ExactOrderedMoments τ ω w z)
    (a b : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    quotientTrace τ ω (optionalCoefficient y a*algebraPatchingWord w
      (xs.map (fun t => (t.1,y t.2)) ++ [(s,optionalCoefficient y b)]))=0 := by
  let C := algebraWordCore w y s xs
  have hs := algebraWordCore_support w f hw y s xs
  have he : C=algebraWordCore w z s (xs.map (fun t => (t.1,k t.2))) := by
    dsimp only [C]
    rw [← algebraWordCore_compress w f hw y s xs]
    exact algebraWordCore_map w _ z k hk s xs
  obtain ⟨j,c,hj⟩ := hc a b
  have hzero : quotientTrace τ ω (C*z j)=0 := by
    rw [he]
    exact exactOrderedMoments_core τ ω w z hm (some j) s _
  have hunit : quotientTrace τ ω C=0 := by
    simpa only [he,optionalCoefficient,mul_one] using
      exactOrderedMoments_core τ ω w z hm none s (xs.map (fun t => (t.1,k t.2)))
  rw [algebraWordCore_endpoints,← mul_assoc]
  change quotientTrace τ ω (optionalCoefficient y a*C*optionalCoefficient y b)=0
  rw [quotientTrace_mul_comm τ ω (optionalCoefficient y a*C),← mul_assoc,
    quotientTrace_mul_comm τ ω (optionalCoefficient y b*optionalCoefficient y a) C]
  rw [← trace_supported_cyclic_compression τ ω C f _ hs.1 hs.2,hj,mul_add,
    mul_smul_comm,hs.2,trace_add,trace_smul,hzero,hunit,mul_zero,add_zero]

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotientCornerCenter_decompose (f z : Q τ ω) :
    f*z*f=quotientCornerCenter τ ω f z+
      (quotientTrace τ ω (f*z*f)/quotientTrace τ ω f) • f := by
  unfold quotientCornerCenter
  abel

theorem cyclicResidualFamily_encode (f : Q τ ω) (y : ℕ → Q τ ω) (k : CyclicFamilyIndex) :
    cyclicResidualFamily τ ω f y (Encodable.encode k)=cyclicFamilyValue τ ω f y k := by
  simp [cyclicResidualFamily]

theorem cyclicResidualFamily_internal (f : Q τ ω) (y : ℕ → Q τ ω) :
    ∃ k : ℕ → ℕ,∀ i,f*y i*f=cyclicResidualFamily τ ω f y (k i) := by
  refine ⟨fun i => Encodable.encode (Sum.inl i : CyclicFamilyIndex),fun i => ?_⟩
  exact (cyclicResidualFamily_encode τ ω f y (.inl i)).symm

theorem cyclicResidualFamily_outer (f : Q τ ω) (y : ℕ → Q τ ω) :
    ∀ a b : Option ℕ,∃ j : ℕ,∃ c : ℂ,
      f*(optionalCoefficient y b*optionalCoefficient y a)*f=
        cyclicResidualFamily τ ω f y j+c • f := by
  intro a b
  refine ⟨Encodable.encode (Sum.inr (a,b) : CyclicFamilyIndex),
    quotientTrace τ ω (f*(optionalCoefficient y b*optionalCoefficient y a)*f)/quotientTrace τ ω f,?_⟩
  rw [cyclicResidualFamily_encode]
  exact quotientCornerCenter_decompose τ ω f _

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem algebraSignedLetter_add' {A : Type*} [AddMonoid A] [StarAddMonoid A]
    (v w : A) (s : Bool) :
    algebraSignedLetter (v+w) s=algebraSignedLetter v s+algebraSignedLetter w s := by
  cases s <;> simp [algebraSignedLetter,star_add]

/-- Distribute every signed letter while preserving the full multiplication
order. The premise is checked for actual mixed terms, not scalar estimates. -/
theorem ordered_sum_zero_of_all_mixed (v w : Q τ ω) (x : ℕ → Q τ ω)
    (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) (a : Q τ ω)
    (h : ∀ cs : List (Bool × Bool × ℕ),∀ b : Bool,
      quotientTrace τ ω (a*algebraMixedTail v w x last b s cs)=0) :
    quotientTrace τ ω (a*algebraPatchingWord (v+w)
      (xs.map (fun t => (t.1,x t.2)) ++ [(s,optionalCoefficient x last)]))=0 := by
  induction xs generalizing a with
  | nil =>
    have hv := h [] false
    have hw := h [] true
    simp only [algebraMixedTail,↓reduceIte,Bool.false_eq_true] at hv hw
    simp only [List.map_nil,List.nil_append,algebraPatchingWord,mul_one,
      algebraSignedLetter_add',add_mul,mul_add,trace_add,hv,hw,add_zero]
  | cons t xs ih =>
    have ht (b : Bool) : quotientTrace τ ω
        ((a*algebraSignedLetter (if b then w else v) t.1*x t.2)*
          algebraPatchingWord (v+w)
            (xs.map (fun t => (t.1,x t.2)) ++ [(s,optionalCoefficient x last)]))=0 := by
      apply ih
      intro cs c
      simpa only [algebraMixedTail,mul_assoc] using h ((b,t.1,t.2)::cs) c
    have hv := ht false
    have hw := ht true
    simp only [Bool.false_eq_true,↓reduceIte] at hv hw
    simp only [List.map_cons,List.cons_append,algebraPatchingWord,algebraSignedLetter_add',
      add_mul,mul_add,trace_add]
    simpa only [mul_assoc,add_zero] using congrArg₂ (·+·) hv hw

theorem exactOrderedMoments_add_of_cyclic_oai (v w f : Q τ ω) (x : ℕ → Q τ ω)
    (hm : ExactOrderedMoments τ ω v x)
    (hs : ∀ s,f*algebraSignedLetter w s=algebraSignedLetter w s ∧
      algebraSignedLetter w s*f=algebraSignedLetter w s)
    (hw : ExactOrderedMoments τ ω w
      (cyclicResidualFamily τ ω f (residualWordFamily τ ω v x))) :
    ExactOrderedMoments τ ω (v+w) x := by
  intro first last xs s
  apply ordered_sum_zero_of_all_mixed τ ω v w x last s xs
  intro cs b
  rcases algebraMixedTail_normalize τ ω v w x last b s cs with h | ⟨pre,ys,t,last',h⟩
  · rw [h]
    simpa only [List.map_map,Function.comp_def] using
      hm first last (cs.map (fun a => (a.2.1,a.2.2))) s
  · obtain ⟨first',hfirst⟩ := residualWordFamily_contains_outer_run τ ω v x first pre
    rw [h,← mul_assoc,← hfirst]
    obtain ⟨k,hk⟩ := cyclicResidualFamily_internal τ ω f (residualWordFamily τ ω v x)
    exact exact_moment_of_cyclic_family τ ω w f hs _ _ k hk
      (cyclicResidualFamily_outer τ ω f _) hw first' last' ys t

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exactOrderedMoments_add_of_cyclic_oai.{u_1} := @OAI.Generator.Tracial.exactOrderedMoments_add_of_cyclic_oai.{u_1}
