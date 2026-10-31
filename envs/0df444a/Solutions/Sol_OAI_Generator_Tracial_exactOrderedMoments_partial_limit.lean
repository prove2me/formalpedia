-- Prove2me | solution 1 for OAI.Generator.Tracial.exactOrderedMoments_partial_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:22:41.204826+00:00
-- url     : https://prove2.me/submissions/43424700-bd8b-4ffd-999f-27584f08b7e8

import Mathlib
import Definitions.Def_OAIQ11Fg020
import Definitions.Def_OAIQ11Fg014

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
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_norm_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
      (𝓝 ‖quotientMap τ (ω : Filter ℕ) a‖) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace]
  exact norm₂_tendsto τ ω a

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Two-norm continuity of ordered moments along uniformly operator-bounded
representatives. No topological-ring structure on the two-norm quotient is used. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_bounded_mul_norm (a : Bounded M) (C : ℝ) (ha : ∀ j,‖a.val j‖ ≤ C)
    (b : Q τ ω) : ‖quotientMap τ (ω : Filter ℕ) a*b‖ ≤ C*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (a*b)
    have hb := (quotient_norm_tendsto τ ω b).const_mul C
    rw [map_mul] at hp
    apply le_of_tendsto_of_tendsto hp hb
    exact Eventually.of_forall (fun j => (τ.norm₂_mul_le (a.val j) (b.val j)).trans
      (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)))

theorem quotient_mul_bounded_norm (a : Bounded M) (C : ℝ) (ha : ∀ j,‖a.val j‖ ≤ C)
    (b : Q τ ω) : ‖b*quotientMap τ (ω : Filter ℕ) a‖ ≤ C*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (b*a)
    have hb := (quotient_norm_tendsto τ ω b).const_mul C
    rw [map_mul] at hp
    apply le_of_tendsto_of_tendsto hp hb
    apply Eventually.of_forall
    intro j
    calc τ.norm₂ (b.val j*a.val j) ≤ τ.norm₂ (b.val j)*‖a.val j‖ := τ.norm₂_mul_le_right _ _
         _ ≤ τ.norm₂ (b.val j)*C := mul_le_mul_of_nonneg_left (ha j) (norm_nonneg _)
         _ = C*τ.norm₂ (b.val j) := mul_comm _ _

theorem quotient_fixed_right_tendsto (b : Q τ ω) (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => a n*b) atTop (𝓝 (v*b)) := by
  obtain ⟨b',hb⟩ := quotientMap_surjective τ (ω : Filter ℕ) b
  obtain ⟨C,_,hbound⟩ := b'.property
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mp ha).const_mul C
  apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa only [mul_zero] using ht)
  intro n
  rw [← sub_mul,← hb]
  exact quotient_mul_bounded_norm τ ω b' C hbound (a n-v)

theorem quotient_bounded_mul_tendsto (a : ℕ → Bounded M) (C : ℝ)
    (hC : ∀ n j,‖(a n).val j‖ ≤ C) (v : Q τ ω) (b : ℕ → Q τ ω) (w : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (a n)) atTop (𝓝 v))
    (hb : Tendsto b atTop (𝓝 w)) :
    Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (a n)*b n) atTop (𝓝 (v*w)) := by
  have ht1 := (tendsto_iff_norm_sub_tendsto_zero.mp hb).const_mul C
  have ht2 := tendsto_iff_norm_sub_tendsto_zero.mp (quotient_fixed_right_tendsto τ ω w _ v ha)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa only [mul_zero,zero_add] using ht1.add ht2)
  intro n
  have he : quotientMap τ (ω : Filter ℕ) (a n)*b n-v*w=
      quotientMap τ (ω : Filter ℕ) (a n)*(b n-w)+
        (quotientMap τ (ω : Filter ℕ) (a n)*w-v*w) := by rw [mul_sub,sub_add_sub_cancel]
  rw [he]
  exact (norm_add_le (quotientMap τ (ω : Filter ℕ) (a n)*(b n-w))
    (quotientMap τ (ω : Filter ℕ) (a n)*w-v*w)).trans
      (add_le_add (quotient_bounded_mul_norm τ ω (a n) C (hC n) (b n-w)) le_rfl)

theorem quotient_fixed_left_tendsto (b : Q τ ω) (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => b*a n) atTop (𝓝 (b*v)) := by
  obtain ⟨b',rfl⟩ := quotientMap_surjective τ (ω : Filter ℕ) b
  obtain ⟨C,_,hbound⟩ := b'.property
  exact quotient_bounded_mul_tendsto τ ω (fun _ => b') C (fun _ => hbound) _ a v tendsto_const_nhds ha

theorem quotient_star_tendsto (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => star (a n)) atTop (𝓝 (star v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [← star_sub,quotient_norm_star] using tendsto_iff_norm_sub_tendsto_zero.mp ha

theorem quotient_partial_signed_tendsto (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (s : Bool) : Tendsto (fun n => quotientMap τ (ω : Filter ℕ)
      (algebraSignedLetter (boundedPartialUnitary (a n)) s)) atTop (𝓝 (algebraSignedLetter v s)) := by
  cases s with
  | false => exact ha
  | true => simpa only [algebraSignedLetter,↓reduceIte,quotientMap_star] using quotient_star_tendsto τ ω _ v ha

theorem quotient_partial_core_tendsto (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω) (s : Bool) (xs : List (Bool × ℕ)) :
    Tendsto (fun n => algebraWordCore (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x s xs)
      atTop (𝓝 (algebraWordCore v x s xs)) := by
  have hsign (t : Bool) := quotient_partial_signed_tendsto τ ω a v ha t
  have he (n : ℕ) (t : Bool) : quotientMap τ (ω : Filter ℕ)
      (algebraSignedLetter (boundedPartialUnitary (a n)) t)=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) t := by
    cases t <;> simp only [algebraSignedLetter,Bool.false_eq_true,↓reduceIte,quotientMap_star]
  induction xs with
  | nil => simpa only [algebraWordCore,he] using hsign s
  | cons t xs ih =>
    have hbound : ∀ n j,‖(algebraSignedLetter (boundedPartialUnitary (a n)) t.1).val j‖ ≤ 1 := by
      intro n j
      cases t.1 with
      | false =>
        change ‖(a n j).val‖ ≤ 1
        exact (a n j).unitary.norm_le_one
      | true =>
        change ‖star (a n j).val‖ ≤ 1
        exact (a n j).unitary.adjoint.norm_le_one
    have hh := quotient_bounded_mul_tendsto τ ω
      (fun n => algebraSignedLetter (boundedPartialUnitary (a n)) t.1) 1 hbound _
      (fun n => x t.2*algebraWordCore (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x s xs)
      _ (hsign t.1) (quotient_fixed_left_tendsto τ ω (x t.2) _ _ ih)
    simpa only [he,algebraWordCore,mul_assoc] using hh

theorem quotient_trace_tendsto (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) :
    Tendsto (fun n => quotientTrace τ ω (a n)) atTop (𝓝 (quotientTrace τ ω v)) := by
  have he (b : Q τ ω) : quotientTrace τ ω b=inner ℂ (1 : Q τ ω) b := by
    rw [inner_eq_trace,star_one,one_mul]
  simp only [he]
  exact tendsto_const_nhds.inner ha

theorem exactOrderedMoments_partial_limit_oai (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω)
    (hm : ∀ n,ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) :
    ExactOrderedMoments τ ω v x := by
  intro first last xs s
  have ht := quotient_partial_core_tendsto τ ω a v ha x s xs
  have ht' := quotient_trace_tendsto τ ω _ _ (quotient_fixed_left_tendsto τ ω
    (optionalCoefficient x first) _ _ (quotient_fixed_right_tendsto τ ω (optionalCoefficient x last) _ _ ht))
  rw [algebraWordCore_endpoints]
  apply tendsto_nhds_unique ht'
  apply tendsto_const_nhds.congr
  intro n
  have hh := hm n first last xs s
  rw [algebraWordCore_endpoints] at hh
  exact hh.symm

end

/-! A genuine unitary in the included quotient with every signed ordered
moment zero. This statement does not assert all Haar powers or freeness. -/

/-! Two actual applications of ordered independence produce a unitary with
all reduced signed moments, including runs of same-sign letters. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exactOrderedMoments_partial_limit_oai.{u_1} := @OAI.Generator.Tracial.exactOrderedMoments_partial_limit_oai.{u_1}
