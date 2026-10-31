-- Prove2me | solution 1 for OAI.Generator.Tracial.SuccessiveCoordinateHaar.prefix_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:28:11.198583+00:00
-- url     : https://prove2.me/submissions/07e90e60-0be3-42d3-9d28-31527327047d

import Mathlib
import Definitions.Def_OAIQ11Fg022
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_variable_endpoints

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

theorem SuccessiveCoordinateHaar.prefix_endpoints_oai (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary (Q τ ω)) (hu : (u : Q τ ω) ∈ seed) (ell : ℕ) :
    HaarEndpoints τ ω (F.algebra ell).toSubalgebra
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1)) :=
  (F.variable_endpoints τ ω u hu ell).mul_left τ ω _ (F.prefix_mem τ ω u hu le_rfl)

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.SuccessiveCoordinateHaar.prefix_endpoints_oai.{u_1} := @OAI.Generator.Tracial.SuccessiveCoordinateHaar.prefix_endpoints_oai.{u_1}
