-- Prove2me | solution 1 for OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:33:05.479613+00:00
-- url     : https://prove2.me/submissions/c2311a72-1a39-4671-810f-84798ac65eda

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G014

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

end Algebra

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

end Algebra

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Words
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! All alternating word shapes, allowing either algebra at either endpoint. -/

/-! Splitting a reduced word at its first occurrence of a specified generator. -/

theorem word_split_first {A : Type*} [DecidableEq A] (n : A)
    (w : List (A × Bool)) (h : ∃ x ∈ w,x.1=n) :
    ∃ a s b,w=a++(n,s)::b ∧ ∀ x ∈ a,x.1 ≠ n := by
  induction w with
  | nil => simp at h
  | cons x w ih =>
    by_cases hx : x.1=n
    · exact ⟨[],x.2,w,by cases x; simp_all,by simp⟩
    · obtain ⟨a,s,b,he,ha⟩ := ih (by
        obtain ⟨y,hy,hn⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact (hx hn).elim
        · exact ⟨y,hy,hn⟩)
      refine ⟨x::a,s,b,by simp [he],?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ha y hy

theorem reduced_append_left {A : Type*} {a b : List (A × Bool)}
    (h : FreeGroup.IsReduced (a++b)) : FreeGroup.IsReduced a :=
  List.IsChain.left_of_append h

theorem reduced_append_right {A : Type*} {a b : List (A × Bool)}
    (h : FreeGroup.IsReduced (a++b)) : FreeGroup.IsReduced b :=
  List.IsChain.right_of_append h

theorem reduced_tail {A : Type*} {a : A × Bool} {w : List (A × Bool)}
    (h : FreeGroup.IsReduced (a::w)) : FreeGroup.IsReduced w :=
  List.IsChain.tail h

/-! Noncommutative ordered row words and coefficient majorization, without commuting-row assumptions. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
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

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem integerValueWord_mul_power (t : unitary (Q τ ω)) (n m : ℤ)
    (xs : List (Q τ ω × ℤ)) (b : Q τ ω) :
    (↑(t^n) : Q τ ω)*integerValueWord τ ω t m xs b=
      integerValueWord τ ω t (n+m) xs b := by
  cases xs <;> simp [integerValueWord,zpow_add,mul_assoc]

/-- Prefixes are absorbed into an arbitrary linear functional. Its centered
endpoint property is preserved when a centered gap is appended. -/
theorem reduced_integer_gap_functional (D : Subalgebra ℂ (Q τ ω))
    (t : unitary (Q τ ω)) (L : Q τ ω →ₗ[ℂ] ℂ)
    (hm : ∀ b ∈ D,∀ n : ℤ,n ≠ 0 → ∀ xs : List (Q τ ω × ℤ),
      (∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
      L (integerValueWord τ ω t n xs b)=0)
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hx : ReducedIntegerGaps τ ω D n xs) (b : Q τ ω) (hb : b ∈ D) :
    L (integerValueWord τ ω t n xs b)=0 := by
  induction xs generalizing L n with
  | nil => exact hm b hb n hn [] (by simp)
  | cons z xs ih =>
    rcases z with ⟨d,m⟩
    rcases hx with ⟨hd,hm0,hgap,hxs⟩
    let d0 := d-quotientTrace τ ω d • (1 : Q τ ω)
    have hd0 : d0 ∈ D := D.sub_mem hd (D.smul_mem D.one_mem _)
    have ht0 : quotientTrace τ ω d0=0 := by
      change (traceLinear τ ω) (d-quotientTrace τ ω d • (1 : Q τ ω))=0
      rw [map_sub,map_smul]
      change quotientTrace τ ω d-quotientTrace τ ω d*quotientTrace τ ω 1=0
      rw [quotientTrace_one,mul_one,sub_self]
    let L' : Q τ ω →ₗ[ℂ] ℂ := L.comp (LinearMap.mulLeft ℂ ((↑(t^n) : Q τ ω)*d0))
    have hL' : ∀ c ∈ D,∀ k : ℤ,k ≠ 0 → ∀ ys : List (Q τ ω × ℤ),
        (∀ z ∈ ys,z.1 ∈ D ∧ quotientTrace τ ω z.1=0 ∧ z.2 ≠ 0) →
        L' (integerValueWord τ ω t k ys c)=0 := by
      intro c hc k hk ys hys
      exact hm c hc n hn ((d0,k)::ys) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hd0,ht0,hk⟩
        · exact hys z hz)
    have hc := ih L' hL' m hm0 hxs
    have hs : quotientTrace τ ω d * L (integerValueWord τ ω t (n+m) xs b)=0 := by
      rcases hgap with hzero | hsign
      · rw [hzero,zero_mul]
      · have hsum : n+m ≠ 0 := by rcases hsign with h | h <;> omega
        rw [ih L hm (n+m) hsum ?_]
        · exact mul_zero _
        · cases xs with
          | nil => trivial
          | cons z ys =>
            rcases hxs with ⟨hz,hnz,hgz,hys⟩
            refine ⟨hz,hnz,?_,hys⟩
            rcases hgz with hzero | hsame
            · exact Or.inl hzero
            · right
              rcases hsign with h | h <;> rcases hsame with h' | h' <;>
                simp only [SamePowerSign] at * <;> omega
    have he : d=d0+quotientTrace τ ω d • (1 : Q τ ω) := by
      simp only [d0,sub_add_cancel]
    change L ((↑(t^n) : Q τ ω)*d*integerValueWord τ ω t m xs b)=0
    rw [he,mul_add,add_mul,map_add]
    change L' (integerValueWord τ ω t m xs b) +
      L (((↑(t^n) : Q τ ω)*(quotientTrace τ ω d • (1 : Q τ ω)))*
        integerValueWord τ ω t m xs b)=0
    rw [hc,mul_smul_comm,mul_one,smul_mul_assoc,map_smul,
      integerValueWord_mul_power,smul_eq_mul,hs,add_zero]

theorem HaarEndpoints.reduced_gaps {D : Subalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D t)
    (a : Q τ ω) (ha : a ∈ D) (b : Q τ ω) (hb : b ∈ D)
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hx : ReducedIntegerGaps τ ω D n xs) :
    quotientTrace τ ω (a*integerValueWord τ ω t n xs b)=0 := by
  apply reduced_integer_gap_functional τ ω D t
    ((traceLinear τ ω).comp (LinearMap.mulLeft ℂ a))
    (fun b hb n hn xs hxs => h a ha b hb n hn xs hxs) n hn xs hx b hb

/-! Expand nonzero integer powers into signs while retaining the exact rule:
only an equal-sign gap may have a nonzero scalar part. -/

theorem signedLetter_integer (t : unitary (Q τ ω)) (s : Bool) :
    algebraSignedLetter (t : Q τ ω) s=(↑(t^signExponent s) : Q τ ω) := by
  cases s
  · simp [signExponent,algebraSignedLetter]
  · change star (t : Q τ ω)=(↑(t^(-1 : ℤ)) : Q τ ω)
    rw [zpow_neg_one]
    rfl

theorem betweenWord_integerValue (t : unitary (Q τ ω)) (s : Bool)
    (xs : List (Q τ ω × Bool)) (b : Q τ ω) :
    betweenWord (t : Q τ ω) s xs b=integerValueWord τ ω t (signExponent s)
      (xs.map (fun z => (z.1,signExponent z.2))) b := by
  induction xs generalizing s with
  | nil => simp [betweenWord,integerValueWord,signedLetter_integer]
  | cons z xs ih => simp [betweenWord,integerValueWord,signedLetter_integer,ih]

theorem signedReducedGaps_integer {D : Subalgebra ℂ (Q τ ω)}
    (s : Bool) (xs : List (Q τ ω × Bool)) (hx : SignedReducedGaps τ ω D s xs) :
    ReducedIntegerGaps τ ω D (signExponent s)
      (xs.map (fun z => (z.1,signExponent z.2))) := by
  induction xs generalizing s with
  | nil => trivial
  | cons z xs ih =>
    refine ⟨hx.1,?_,?_,ih z.2 hx.2.2⟩
    · cases z.2 <;> simp [signExponent]
    · by_cases h : s=z.2
      · right
        rw [h]
        cases z.2 <;> simp [signExponent,SamePowerSign]
      · exact Or.inl (hx.2.1 h)

theorem HaarEndpoints.signed_gaps {D : Subalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D t)
    (a : Q τ ω) (ha : a ∈ D) (b : Q τ ω) (hb : b ∈ D)
    (s : Bool) (xs : List (Q τ ω × Bool)) (hx : SignedReducedGaps τ ω D s xs) :
    quotientTrace τ ω (a*betweenWord (t : Q τ ω) s xs b)=0 := by
  rw [betweenWord_integerValue]
  apply h.reduced_gaps τ ω a ha b hb _ (by cases s <;> simp [signExponent])
  exact signedReducedGaps_integer τ ω s xs hx

theorem signedReducedGaps_repeat {D : Subalgebra ℂ (Q τ ω)}
    (s : Bool) (n : ℕ) (xs : List (Q τ ω × Bool))
    (hx : SignedReducedGaps τ ω D s xs) :
    SignedReducedGaps τ ω D s (List.replicate n (1,s)++xs) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append]
    exact ⟨D.one_mem,fun h => (h rfl).elim,ih⟩

theorem signedReducedGaps_blocks {D : Subalgebra ℂ (Q τ ω)}
    (s : Bool) (n : ℕ) (xs : List (Q τ ω × (Bool × ℕ)))
    (hx : ∀ z ∈ xs,z.1 ∈ D ∧ quotientTrace τ ω z.1=0) :
    SignedReducedGaps τ ω D s (powerBlockGaps s n xs) := by
  induction xs generalizing s n with
  | nil =>
    simpa only [powerBlockGaps,List.append_nil] using
      signedReducedGaps_repeat τ ω (D := D) s n [] trivial
  | cons z xs ih =>
    apply signedReducedGaps_repeat
    exact ⟨(hx z (by simp)).1,fun _ => (hx z (by simp)).2,
      ih _ _ (fun w hw => hx w (by simp [hw]))⟩

theorem integerValueWord_blocks (t : unitary (Q τ ω)) (n : ℤ) (hn : n ≠ 0)
    (xs : List (Q τ ω × ℤ)) (hx : ∀ z ∈ xs,z.2 ≠ 0) (b : Q τ ω) :
    integerValueWord τ ω t n xs b=betweenWord (t : Q τ ω) (integerPowerBlock n).1
      (powerBlockGaps (integerPowerBlock n).1 (integerPowerBlock n).2
        (xs.map (fun z => (z.1,integerPowerBlock z.2)))) b := by
  rw [← powerBlockWord_expand]
  induction xs generalizing n with
  | nil => simp [integerValueWord,powerBlockWord,integerPowerBlock_eval t n hn]
  | cons z xs ih =>
    simp only [integerValueWord,List.map_cons,powerBlockWord,integerPowerBlock_eval t n hn]
    rw [ih z.2 (hx z (by simp)) (fun w hw => hx w (by simp [hw]))]

end

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

theorem betweenWord_absorb_left (u v : A) (s : Bool) (xs : List (A × Bool)) (b : A) :
    betweenWord (u*v) s xs b=productLeft u s*betweenWord v s (absorbedGapList u s xs)
      (productRight u (finalWordSign s xs)*b) := by
  induction xs generalizing s with
  | nil => simp [betweenWord,absorbedGapList,finalWordSign,signed_product_split,mul_assoc]
  | cons z xs ih =>
    simp only [betweenWord,absorbedGapList,finalWordSign,signed_product_split,ih,mul_assoc]
end Algebra
section

open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem absorbedGapList_reduced (D : StarSubalgebra ℂ (Q τ ω))
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D)
    (s : Bool) (xs : List (Q τ ω × Bool))
    (hx : SignedReducedGaps τ ω D.toSubalgebra s xs) :
    SignedReducedGaps τ ω D.toSubalgebra s (absorbedGapList (u : Q τ ω) s xs) := by
  induction xs generalizing s with
  | nil => trivial
  | cons z xs ih =>
    rcases z with ⟨d,r⟩
    refine ⟨?_,?_,ih r hx.2.2⟩
    · cases s <;> cases r <;> simp only [productRight,productLeft,Bool.false_eq_true,
        ↓reduceIte,mul_one,one_mul]
      · exact D.mul_mem hx.1 hu
      · exact hx.1
      · exact D.mul_mem (D.mul_mem (D.star_mem' hu) hx.1) hu
      · exact D.mul_mem (D.star_mem' hu) hx.1
    · intro hne
      cases s <;> cases r
      · exact (hne rfl).elim
      · simpa [productRight,productLeft] using hx.2.1 (by decide)
      · change quotientTrace τ ω (star (u : Q τ ω)*d*(u : Q τ ω))=0
        rw [quotientTrace_mul_comm τ ω (star (u : Q τ ω)*d),← mul_assoc,
          u.property.2,one_mul]
        exact hx.2.1 (by decide)
      · exact (hne rfl).elim

theorem HaarEndpoints.mul_left_signed {D : StarSubalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D.toSubalgebra t)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D)
    (a : Q τ ω) (ha : a ∈ D) (b : Q τ ω) (hb : b ∈ D)
    (s : Bool) (xs : List (Q τ ω × Bool))
    (hx : SignedReducedGaps τ ω D.toSubalgebra s xs) :
    quotientTrace τ ω (a*betweenWord (↑(u*t) : Q τ ω) s xs b)=0 := by
  change quotientTrace τ ω (a*betweenWord ((u : Q τ ω)*(t : Q τ ω)) s xs b)=0
  rw [betweenWord_absorb_left,← mul_assoc]
  apply h.signed_gaps τ ω _ ?_ _ ?_ s _ (absorbedGapList_reduced τ ω D u hu s xs hx)
  · cases s <;> simp only [productLeft,Bool.false_eq_true,↓reduceIte,mul_one]
    · exact D.mul_mem ha hu
    · exact ha
  · cases finalWordSign s xs <;> simp only [productRight,Bool.false_eq_true,↓reduceIte,one_mul]
    · exact hb
    · exact D.mul_mem (D.star_mem' hu) hb

theorem HaarEndpoints.mul_left {D : StarSubalgebra ℂ (Q τ ω)}
    {t : unitary (Q τ ω)} (h : HaarEndpoints τ ω D.toSubalgebra t)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ D) :
    HaarEndpoints τ ω D.toSubalgebra (u*t) := by
  intro a ha b hb n hn xs hxs
  rw [integerValueWord_blocks τ ω _ n hn xs (fun z hz => (hxs z hz).2.2)]
  apply h.mul_left_signed τ ω u hu a ha b hb
  apply signedReducedGaps_blocks
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
  exact ⟨(hxs w hw).1,(hxs w hw).2.1⟩

end

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

omit hfactor hdiff hirr hsep
variable {hNM}

theorem SuccessiveCoordinateHaar.monotone {seed : Set (Q τ ω)}
    (F : SuccessiveCoordinateHaar τ ω hNM seed) : Monotone F.algebra := by
  apply monotone_nat_of_le_succ
  intro j x hx
  rw [F.successor]
  exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ hx)

theorem SuccessiveCoordinateHaar.seed_mem {seed : Set (Q τ ω)}
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (j : ℕ) : seed ⊆ F.algebra j := by
  intro x hx
  apply F.monotone τ ω (Nat.zero_le j)
  rw [F.initial]
  exact StarAlgebra.subset_adjoin ℂ seed hx

theorem SuccessiveCoordinateHaar.previous_mem {seed : Set (Q τ ω)}
    (F : SuccessiveCoordinateHaar τ ω hNM seed) {i j : ℕ} (hij : i < j) :
    ((F.step i).t : Q τ ω) ∈ F.algebra j := by
  apply F.monotone τ ω hij
  rw [F.successor]
  exact StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _)

end

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.variable_mem (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) {i j : ℕ} (hij : i < j) :
    (prefixVariable τ ω u (fun k => (F.step k).t) i : Q τ ω) ∈ F.algebra j := by
  cases i with
  | zero => exact F.previous_mem τ ω hij
  | succ i => exact (F.algebra j).mul_mem (F.seed_mem τ ω j hu) (F.previous_mem τ ω hij)

theorem SuccessiveCoordinateHaar.prefix_mem (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) {k j : ℕ} (hkj : k ≤ j) :
    (prefixProduct τ ω u (fun i => (F.step i).t) k : Q τ ω) ∈ F.algebra j := by
  induction k with
  | zero => exact (F.algebra j).one_mem
  | succ k ih =>
    exact (F.algebra j).mul_mem (ih (by omega)) (F.variable_mem τ ω u hu (by omega))

theorem SuccessiveCoordinateHaar.variable_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (j : ℕ) :
    HaarEndpoints τ ω (F.algebra j).toSubalgebra
      (prefixVariable τ ω u (fun k => (F.step k).t) j) := by
  cases j with
  | zero => exact (F.step 0).endpoints
  | succ j => exact (F.step (j+1)).endpoints.mul_left τ ω u (F.seed_mem τ ω _ hu)

theorem SuccessiveCoordinateHaar.prefix_endpoints (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) :
    HaarEndpoints τ ω (F.algebra ell).toSubalgebra
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)) :=
  (F.variable_endpoints τ ω u hu ell).mul_left τ ω _ (F.prefix_mem τ ω u hu le_rfl)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem unitaryWord_cons {A : Type*} (v : A → unitary (Q τ ω))
    (x : A × Bool) (w : List (A × Bool)) :
    unitaryWord τ ω v (x::w)=algebraSignedLetter (v x.1 : Q τ ω) (!x.2)*unitaryWord τ ω v w := rfl

theorem unitaryWord_append {A : Type*} (v : A → unitary (Q τ ω))
    (a b : List (A × Bool)) : unitaryWord τ ω v (a++b)=unitaryWord τ ω v a*unitaryWord τ ω v b := by
  simp [unitaryWord,List.map_append,List.prod_append]

theorem unitaryWord_mem {A : Type*} (v : A → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (w : List (A × Bool))
    (hv : ∀ x ∈ w,(v x.1 : Q τ ω) ∈ D) : unitaryWord τ ω v w ∈ D := by
  induction w with
  | nil => exact D.one_mem
  | cons x w ih =>
    apply D.mul_mem _ (ih (fun y hy => hv y (by simp [hy])))
    have hx := hv x (by simp)
    change algebraSignedLetter (v x.1 : Q τ ω) (!x.2) ∈ D
    unfold algebraSignedLetter
    split
    · exact star_mem hx
    · exact hx

/-- Scan the tail after a maximal label. Empty gaps can only join equal signs. -/
theorem maximal_word_gaps (v : ℕ → unitary (Q τ ω))
    (D : StarSubalgebra ℂ (Q τ ω)) (n : ℕ)
    (hv : ∀ i < n,(v i : Q τ ω) ∈ D)
    (hzero : ∀ a : List (ℕ × Bool),FreeGroup.IsReduced a → a ≠ [] →
      (∀ x ∈ a,x.1 < n) → quotientTrace τ ω (unitaryWord τ ω v a)=0)
    (w : List (ℕ × Bool)) (s : Bool)
    (hr : FreeGroup.IsReduced ((n,s)::w)) (hn : ∀ x ∈ w,x.1 ≤ n) :
    ∃ xs b,b ∈ D ∧ SignedReducedGaps τ ω D.toSubalgebra (!s) xs ∧
      unitaryWord τ ω v ((n,s)::w)=betweenWord (v n : Q τ ω) (!s) xs b := by
  classical
  by_cases hex : ∃ x ∈ w,x.1=n
  · obtain ⟨a,t,c,he,ha⟩ := word_split_first n w hex
    have hlt : ∀ x ∈ a,x.1 < n := by
      intro x hx
      have := hn x (by rw [he]; simp [hx])
      have := ha x hx
      omega
    have har : FreeGroup.IsReduced a := reduced_append_left (he ▸ reduced_tail hr)
    have hcr : FreeGroup.IsReduced ((n,t)::c) := reduced_append_right (he ▸ reduced_tail hr)
    have hcn : ∀ x ∈ c,x.1 ≤ n := by
      intro x hx
      exact hn x (by rw [he]; simp [hx])
    obtain ⟨xs,b,hb,hxs,hev⟩ := maximal_word_gaps v D n hv hzero c t hcr hcn
    have ham : unitaryWord τ ω v a ∈ D := unitaryWord_mem τ ω v D a (fun x hx => hv _ (hlt x hx))
    have hac : (!s) ≠ (!t) → quotientTrace τ ω (unitaryWord τ ω v a)=0 := by
      intro hst
      apply hzero a har _ hlt
      intro hempty
      have hr' : FreeGroup.IsReduced ((n,s)::(n,t)::c) := by
        simpa only [he,hempty,List.nil_append] using hr
      have hst' : s=t := (FreeGroup.isReduced_cons_cons.mp hr').1 rfl
      exact hst (congrArg Bool.not hst')
    refine ⟨(unitaryWord τ ω v a,!t)::xs,b,hb,⟨ham,hac,hxs⟩,?_⟩
    rw [unitaryWord_cons,he,unitaryWord_append,hev]
    simp only [betweenWord,mul_assoc]
  · refine ⟨[],unitaryWord τ ω v w,?_,trivial,rfl⟩
    apply unitaryWord_mem τ ω v D w
    intro x hx
    apply hv
    have := hn x hx
    have : x.1 ≠ n := fun he => hex ⟨x,hx,he⟩
    omega
termination_by w.length
 decreasing_by simp only [he,List.length_append,List.length_cons]; omega

theorem successive_reduced_word_zero (v : ℕ → unitary (Q τ ω))
    (D : ℕ → StarSubalgebra ℂ (Q τ ω))
    (hv : ∀ i j,i < j → (v i : Q τ ω) ∈ D j)
    (hep : ∀ j,HaarEndpoints τ ω (D j).toSubalgebra (v j))
    (n : ℕ) (w : List (ℕ × Bool)) (hr : FreeGroup.IsReduced w) (hw : w ≠ [])
    (hn : ∀ x ∈ w,x.1 < n) : quotientTrace τ ω (unitaryWord τ ω v w)=0 := by
  classical
  induction n generalizing w with
  | zero =>
    cases w with
    | nil => exact (hw rfl).elim
    | cons x w => have := hn x (by simp); omega
  | succ n ih =>
    by_cases hex : ∃ x ∈ w,x.1=n
    · obtain ⟨a,s,b,he,ha⟩ := word_split_first n w hex
      have halt : ∀ x ∈ a,x.1 < n := by
        intro x hx
        have := hn x (by rw [he]; simp [hx])
        have := ha x hx
        omega
      have hbr : FreeGroup.IsReduced ((n,s)::b) := reduced_append_right (he ▸ hr)
      have hbn : ∀ x ∈ b,x.1 ≤ n := by
        intro x hx
        have := hn x (by rw [he]; simp [hx])
        omega
      obtain ⟨xs,c,hc,hxs,hev⟩ := maximal_word_gaps τ ω v (D n) n
        (fun i hi => hv i n hi) ih b s hbr hbn
      rw [he,unitaryWord_append,hev]
      exact (hep n).signed_gaps τ ω _
        (unitaryWord_mem τ ω v (D n) a (fun x hx => hv _ _ (halt x hx))) c hc _ xs hxs
    · apply ih w hr hw
      intro x hx
      have := hn x hx
      have : x.1 ≠ n := fun he => hex ⟨x,hx,he⟩
      omega

end

/-! The actual free-group representation furnished by successive Haar variables. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem unitaryRepresentation_mk {A : Type*} (v : A → unitary (Q τ ω))
    (w : List (A × Bool)) :
    (unitaryRepresentation τ ω v (FreeGroup.mk w) : Q τ ω)=unitaryWord τ ω v w := by
  rw [unitaryRepresentation,FreeGroup.lift_mk]
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [List.map_cons,List.prod_cons,Submonoid.coe_mul,unitaryWord_cons,ih]
    cases x.2 <;> rfl

theorem successive_freeGroup_trace (v : ℕ → unitary (Q τ ω))
    (D : ℕ → StarSubalgebra ℂ (Q τ ω))
    (hv : ∀ i j,i < j → (v i : Q τ ω) ∈ D j)
    (hep : ∀ j,HaarEndpoints τ ω (D j).toSubalgebra (v j))
    (g : FreeGroup ℕ) (hg : g ≠ 1) :
    quotientTrace τ ω (unitaryRepresentation τ ω v g : Q τ ω)=0 := by
  rw [← FreeGroup.mk_toWord (x := g),unitaryRepresentation_mk]
  apply successive_reduced_word_zero τ ω v D hv hep
    (g.toWord.toFinset.sup Prod.fst+1) g.toWord FreeGroup.isReduced_toWord
    (fun h => hg (FreeGroup.toWord_eq_nil_iff.mp h))
  intro x hx
  have := Finset.le_sup (f := Prod.fst) (List.mem_toFinset.mpr hx)
  omega

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.freeGroup_trace
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed)
    (g : FreeGroup ℕ) (hg : g ≠ 1) :
    quotientTrace τ ω
      (unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t)) g : Q τ ω)=0 :=
  successive_freeGroup_trace τ ω _ F.algebra
    (fun _ _ hij => F.variable_mem τ ω u hu hij) (F.variable_endpoints τ ω u hu) g hg

end

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {D : StarSubalgebra ℂ (Q τ ω)} {W : unitary (Q τ ω)}

theorem HaarEndpoints.base_correlation (hW : HaarEndpoints τ ω D.toSubalgebra W)
    (xi : Q τ ω) (hxi : xi ∈ D) : quotientTrace τ ω (star xi*(W : Q τ ω))=0 := by
  have hstar : star xi ∈ D := star_mem hxi
  have h := hW.signed_gaps τ ω (star xi) hstar 1 D.one_mem false [] trivial
  simpa only [betweenWord,algebraSignedLetter,Bool.false_eq_true,ite_false, if_false,mul_one] using h

theorem HaarEndpoints.positive_conjugate_correlation
    (hW : HaarEndpoints τ ω D.toSubalgebra W)
    (xi : Q τ ω) (hxi : xi ∈ D) (p z : unitary (Q τ ω))
    (hp : (p : Q τ ω) ∈ D) (hz : (z : Q τ ω) ∈ D)
    (hcenter : quotientTrace τ ω (star (p : Q τ ω))=0) :
    quotientTrace τ ω (star xi*(↑(p*(z*star W)*star p) : Q τ ω)*(W : Q τ ω))=0 := by
  have hstar : star xi ∈ D := star_mem hxi
  have hpstar : star (p : Q τ ω) ∈ D := star_mem hp
  have h := hW.signed_gaps τ ω (star xi*(p : Q τ ω)*(z : Q τ ω))
    (D.mul_mem (D.mul_mem hstar hp) hz) 1 D.one_mem true [(star (p : Q τ ω),false)]
    ⟨hpstar,fun _ => hcenter,trivial⟩
  change quotientTrace τ ω ((star xi*(p : Q τ ω)*(z : Q τ ω))*
    (star (W : Q τ ω)*star (p : Q τ ω)*((W : Q τ ω)*1)))=0 at h
  simpa only [Submonoid.coe_mul,Unitary.coe_star,mul_one,mul_assoc] using h

theorem HaarEndpoints.negative_conjugate_correlation
    (hW : HaarEndpoints τ ω D.toSubalgebra W)
    (xi : Q τ ω) (hxi : xi ∈ D) (p z : unitary (Q τ ω))
    (hp : (p : Q τ ω) ∈ D) (hz : (z : Q τ ω) ∈ D) :
    quotientTrace τ ω (star xi*star (↑(p*(z*star W)*star p) : Q τ ω)*(W : Q τ ω))=0 := by
  have hstar : star xi ∈ D := star_mem hxi
  have hpstar : star (p : Q τ ω) ∈ D := star_mem hp
  have hzstar : star (z : Q τ ω) ∈ D := star_mem hz
  have h := hW.signed_gaps τ ω (star xi*(p : Q τ ω)) (D.mul_mem hstar hp)
    1 D.one_mem false [(star (z : Q τ ω)*star (p : Q τ ω),false)]
    ⟨D.mul_mem hzstar hpstar,fun hh => (hh rfl).elim,trivial⟩
  change quotientTrace τ ω ((star xi*(p : Q τ ω))*
    ((W : Q τ ω)*(star (z : Q τ ω)*star (p : Q τ ω))*((W : Q τ ω)*1)))=0 at h
  simpa only [Submonoid.coe_mul,Unitary.coe_star,star_mul,star_star,mul_one,mul_assoc] using h

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

set_option maxHeartbeats 1600000 in
theorem unitaryRepresentation_prefix (u : unitary (Q τ ω))
    (t : ℕ → unitary (Q τ ω)) (k : ℕ) :
    unitaryRepresentation τ ω (prefixVariable τ ω u t) (freePrefix k)=
      prefixProduct τ ω u t k := by
  induction k with
  | zero => exact map_one _
  | succ k ih =>
    rw [freePrefix,(unitaryRepresentation τ ω (prefixVariable τ ω u t)).map_mul,ih]
    change prefixProduct τ ω u t k*FreeGroup.lift (prefixVariable τ ω u t) (FreeGroup.of k)=_
    rw [FreeGroup.lift_apply_of]
    rfl

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.label_mem (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) (p : PrefixLabel ell) :
    (F.labelUnitary τ ω u ell p : Q τ ω) ∈ F.algebra ell := by
  classical
  have hp := p.property
  change p.val ∈ ratioLabels ell at hp
  simp only [ratioLabels,Finset.mem_insert,Finset.mem_image] at hp
  rcases hp with he | ⟨ij,_,he⟩
  · change (unitaryRepresentation τ ω _ p.val : Q τ ω) ∈ _
    rw [he,map_one]
    exact (F.algebra ell).one_mem
  · change (unitaryRepresentation τ ω _ p.val : Q τ ω) ∈ _
    let f := unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t))
    have hright := (f.map_inv (freePrefix (ij.2.val+1))).trans
      (congrArg Inv.inv (unitaryRepresentation_prefix τ ω u (fun k => (F.step k).t) (ij.2.val+1)))
    have hratio := (congrArg f he.symm).trans
      ((f.map_mul (freePrefix (ij.1.val+1)) ((freePrefix (ij.2.val+1))⁻¹)).trans
        (congrArg₂ (fun a b => a*b)
          (unitaryRepresentation_prefix τ ω u (fun k => (F.step k).t) (ij.1.val+1)) hright))
    have hj : star (prefixProduct τ ω u (fun k => (F.step k).t) (ij.2.val+1) : Q τ ω) ∈ F.algebra ell :=
      star_mem (F.prefix_mem τ ω u hu (by omega))
    exact (congrArg (fun a : unitary (Q τ ω) => (a : Q τ ω) ∈ F.algebra ell) hratio).mpr
      ((F.algebra ell).mul_mem (F.prefix_mem τ ω u hu (by omega)) hj)

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_WordCorrelation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Ordered prefix cancellation for the actual common perturbed unitary.
All identities are identities of bounded coordinate sequences. -/
namespace Tracial

/-! The exact first-order trace calculation for the manuscript's prefix labels. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.label_star_trace
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary (Q τ ω))
    (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) (p : PrefixLabel ell) (hp : p.val ≠ 1) :
    quotientTrace τ ω (star (F.labelUnitary τ ω u ell p : Q τ ω))=0 := by
  let f := unitaryRepresentation τ ω (prefixVariable τ ω u (fun k => (F.step k).t))
  have he : (f p.val⁻¹ : Q τ ω)=star (f p.val : Q τ ω) :=
    congrArg Subtype.val (f.map_inv p.val)
  change quotientTrace τ ω (star (f p.val : Q τ ω))=0
  rw [← he]
  exact F.freeGroup_trace τ ω u hu _ (fun h => hp (inv_eq_one.mp h))

theorem SuccessiveCoordinateHaar.conjugate_positive_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (p : PrefixLabel ell) :
    quotientTrace τ ω (star xi*(F.conjugateUnitary τ ω u z ell p : Q τ ω)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      if p.val=1 then quotientTrace τ ω (star xi*(z : Q τ ω)) else 0 := by
  by_cases hp : p.val=1
  · apply Eq.trans ?_ (ite_eq_left hp).symm
    have he : F.labelUnitary τ ω u ell p=1 :=
      (congrArg (unitaryRepresentation τ ω
        (prefixVariable τ ω u (fun k => (F.step k).t))) hp).trans (map_one _)
    let W := prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)
    change quotientTrace τ ω (star xi*(↑(F.labelUnitary τ ω u ell p*(z*star W)*
      star (F.labelUnitary τ ω u ell p)) : Q τ ω)*(W : Q τ ω))=_
    rw [he]
    simp only [star_one,one_mul,mul_one,Submonoid.coe_mul,Unitary.coe_star,mul_assoc,
      Unitary.coe_star_mul_self]
  · apply Eq.trans ?_ (ite_eq_right hp).symm
    exact (F.prefix_endpoints τ ω u hu ell).positive_conjugate_correlation τ ω xi
      (F.seed_mem τ ω ell hxi) (F.labelUnitary τ ω u ell p) z (F.label_mem τ ω u hu ell p)
      (F.seed_mem τ ω ell hz) (F.label_star_trace τ ω u hu ell p hp)

theorem SuccessiveCoordinateHaar.conjugate_negative_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (p : PrefixLabel ell) :
    quotientTrace τ ω (star xi*star (F.conjugateUnitary τ ω u z ell p : Q τ ω)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=0 :=
  (F.prefix_endpoints τ ω u hu ell).negative_conjugate_correlation τ ω xi
    (F.seed_mem τ ω ell hxi) (F.labelUnitary τ ω u ell p) z (F.label_mem τ ω u hu ell p)
    (F.seed_mem τ ω ell hz)

theorem SuccessiveCoordinateHaar.firstOrder_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (c : ℂ) :
    quotientTrace τ ω (star xi*F.firstOrderTerm τ ω u z ell c*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      c*(ell : ℂ)*quotientTrace τ ω (star xi*(z : Q τ ω)) := by
  let W := prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)
  let L := (traceLinear τ ω).comp
    ((LinearMap.mulRight ℂ (W : Q τ ω)).comp (LinearMap.mulLeft ℂ (star xi)))
  have hpos (k j : Fin ell) : L (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)=
      if k=j then quotientTrace τ ω (star xi*(z : Q τ ω)) else 0 := by
    have h := F.conjugate_positive_correlation τ ω u z xi hu hz hxi ell (pairLabel k j)
    change quotientTrace τ ω (star xi*(F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=_
    simpa only [pairLabel,pairRatio_eq_one_iff] using h
  have hneg (k j : Fin ell) : L (star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω))=0 :=
    F.conjugate_negative_correlation τ ω u z xi hu hz hxi ell (pairLabel k j)
  change L (c • ∑ k : Fin ell,∑ j : Fin ell,
    ((F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)-
      star (F.conjugateUnitary τ ω u z ell (pairLabel k j) : Q τ ω)))=_
  simp only [map_smul,map_sum,map_sub,hpos,hneg,sub_zero]
  simp [smul_eq_mul,nsmul_eq_mul,mul_assoc]

theorem SuccessiveCoordinateHaar.linearized_correlation_q129_oai
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (c : ℂ) :
    quotientTrace τ ω (star xi*(1+F.firstOrderTerm τ ω u z ell c)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      c*(ell : ℂ)*quotientTrace τ ω (star xi*(z : Q τ ω)) := by
  rw [mul_add,add_mul,trace_add,mul_one,
    (F.prefix_endpoints τ ω u hu ell).base_correlation τ ω xi (F.seed_mem τ ω ell hxi),zero_add]
  exact F.firstOrder_correlation τ ω u z xi hu hz hxi ell c

end

/-! The first-order term is exactly the sum of the mapped formal rows, and
its correlation is the manuscript's alpha/2 coefficient. -/

/-! The uniform trace correlation for the actual product of coordinate
exponentials. Identifying that product with a single-unitary perturbation word
is a separate remaining step. -/

/-! The uniform correlation now belongs to the literal word in one common
perturbed unitary, as required by eq:perturbation-prefix. -/
open UltrapowerBridge

end Tracial

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129_oai.{u_1} := @OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129_oai.{u_1}
