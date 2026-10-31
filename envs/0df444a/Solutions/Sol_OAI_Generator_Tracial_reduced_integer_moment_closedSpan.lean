-- Prove2me | solution 1 for OAI.Generator.Tracial.reduced_integer_moment_closedSpan
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:35:50.101617+00:00
-- url     : https://prove2.me/submissions/7b149f52-2070-4873-a64a-c501d145e2bd

import Mathlib
import Definitions.Def_OAIQ11Fg023

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

theorem reduced_integer_moment_closedSpan_oai (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
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

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.reduced_integer_moment_closedSpan_oai.{u_1} := @OAI.Generator.Tracial.reduced_integer_moment_closedSpan_oai.{u_1}
