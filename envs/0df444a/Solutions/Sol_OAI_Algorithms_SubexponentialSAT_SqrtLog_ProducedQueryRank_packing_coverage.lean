-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:00:44.81762+00:00
-- url     : https://prove2.me/submissions/48f18306-3d58-4e5b-800a-feca98840c32

import Mathlib
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S107
import Definitions.Def_OAIQ081S109
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_problem_computed_energies

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BlockPacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Packing complete type blocks

The squared-deviation bound and the threshold from Section 5.4 imply a lower
bound for every type count. Enumerating the finite fibers then constructs
pairwise disjoint complete blocks. The construction from supplied enumerations
is explicit; no running-time theorem is asserted here.
-/

namespace SubexponentialSAT.BlockPacking

open scoped BigOperators

section FiniteFibers

variable {α τ : Type*} [Fintype α] [Fintype τ] [DecidableEq τ]

omit [Fintype τ] in
/-- Compatibility with type counts expressed by filtering the coordinates. -/
theorem count_eq_filter_card (label : α → τ) (u : τ) :
    count label u = (Finset.univ.filter fun v => label v = u).card := by
  exact Fintype.card_subtype (fun v => label v = u)

end FiniteFibers

end SubexponentialSAT.BlockPacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_NaturalAssignment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Conditional assignment by natural-number comparisons

The executable chooser and all of its scores use natural numbers. A rational
common-denominator identity is used only to prove that every comparison,
including ties, agrees with the previously verified conditional-expectation
algorithm. Score execution enumerates only the active local pair support.
-/

namespace SubexponentialSAT.Subexp.NaturalAssignment

open scoped BigOperators

section Search

variable {A : Type*}

/-- The chooser depends only on the ordering of scores, including equality. -/
theorem chooseMinNat_eq_chooseMin (natural : A → ℕ) (rational : A → ℚ)
    (horder : ∀ x y, rational x ≤ rational y ↔ natural x ≤ natural y)
    (a : A) (tail : List A) :
    chooseMinNat natural a tail =
      SubexponentialSAT.ConditionalExpectation.chooseMin rational a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [chooseMinNat, SubexponentialSAT.ConditionalExpectation.chooseMin, ih, horder]

theorem assignNat_eq_assignWithEvaluator (a : A) (tail : List A)
    (natural : ℕ → List A → ℕ) (rational : ℕ → List A → ℚ)
    (horder : ∀ n fixed x y,
      rational n (x :: fixed) ≤ rational n (y :: fixed) ↔
        natural n (x :: fixed) ≤ natural n (y :: fixed))
    (n : ℕ) (fixed : List A) :
    assignNat a tail natural n fixed =
      SubexponentialSAT.ConditionalExpectation.assignWithEvaluator a tail rational n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
      have hchoice := chooseMinNat_eq_chooseMin
        (fun x => natural n (x :: fixed)) (fun x => rational n (x :: fixed))
        (horder n fixed) a tail
      simp only [assignNat, SubexponentialSAT.ConditionalExpectation.assignWithEvaluator,
        hchoice, ih]

end Search

end SubexponentialSAT.Subexp.NaturalAssignment

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstructivePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable complete-block packing

All execution definitions use supplied finite lists, filtering, minimum scans,
indexed list access, and index lookup. No execution definition uses classical
choice or an abstract inverse. Mathematical cardinalities occur only in proofs.
-/

namespace SubexponentialSAT.Subexp.ConstructivePacking

open scoped BigOperators

namespace FiniteEnumeration

variable {α : Type*} [DecidableEq α]

theorem length_eq_card [Fintype α] (E : FiniteEnumeration α) :
    E.values.length = Fintype.card α := by
  simpa only [Fintype.card_fin] using Fintype.card_congr E.equivFin

end FiniteEnumeration

namespace PackingData

variable {V U : Type*} [DecidableEq U]

variable [DecidableEq V]

section Cardinalities

variable [Fintype V] [Fintype U]

omit [Fintype U] in
theorem bucket_length_eq_count (P : PackingData V U) (u : U) :
    (P.bucket u).length = BlockPacking.count P.label u := by
  simpa only [Fintype.card_fin, BlockPacking.count] using Fintype.card_congr (P.bucketEquiv u)

omit [DecidableEq V] [Fintype V] [Fintype U] in
theorem minCount_lower (P : PackingData V U) (us : List U) (L C : ℚ)
    (hstart : L ≤ C * P.vertices.values.length)
    (heach : ∀ u ∈ us, L ≤ C * (P.bucket u).length) :
    L ≤ C * P.minCount us := by
  induction us with
  | nil => exact hstart
  | cons u us ih =>
    have htail := ih (fun v hv => heach v (List.mem_cons_of_mem u hv))
    have hhead := heach u (by simp)
    dsimp only [minCount]
    rcases le_total (P.bucket u).length (P.minCount us) with h | h
    · rw [min_eq_left h]
      exact hhead
    · rw [min_eq_right h]
      exact htail

/-- The computed minimum and embedding have the same loss guarantee as the
abstract packing theorem. -/
theorem coverage_of_count_lower (P : PackingData V U) (ε : ℚ)
    (hN : 0 < Fintype.card U) (hε : 0 ≤ ε)
    (hlower : ∀ u, (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * BlockPacking.count P.label u) :
    (1 - ε) * (Fintype.card V : ℚ) ≤ (P.blockCount : ℚ) * Fintype.card U := by
  have hstart : (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * P.vertices.values.length := by
    rw [P.vertices.length_eq_card]
    have hNq : (1 : ℚ) ≤ Fintype.card U := by exact_mod_cast hN
    have hD : (0 : ℚ) ≤ Fintype.card V := by positivity
    have hprod := mul_nonneg (sub_nonneg.mpr hNq) hD
    have hloss := mul_nonneg hε hD
    nlinarith
  have heach : ∀ u ∈ P.types.values, (1 - ε) * (Fintype.card V : ℚ) ≤
      (Fintype.card U : ℚ) * (P.bucket u).length := by
    intro u _
    rw [P.bucket_length_eq_count]
    exact hlower u
  simpa only [blockCount, mul_comm (P.minCount P.types.values : ℚ)] using
    P.minCount_lower P.types.values ((1 - ε) * Fintype.card V) (Fintype.card U) hstart heach

end Cardinalities

end PackingData

end SubexponentialSAT.Subexp.ConstructivePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous type packing and original-variable head balance. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes
noncomputable section

section Counts
variable {I U : Type*} [Fintype I] [Fintype U] [DecidableEq I] [DecidableEq U]
  [Nonempty U]

omit [DecidableEq I] [Nonempty U] in
theorem count_deviation_le (label : I → U) {x : ℚ} (hx : 0 ≤ x)
    (h : energy label ≤ x^2) (u : U) :
    |((Finset.univ.filter fun i => label i = u).card : ℚ) -
      (Fintype.card I : ℚ) / (Fintype.card U : ℚ)| ≤ x := by
  have hone : (((Finset.univ.filter fun i => label i = u).card : ℚ) -
      (Fintype.card I : ℚ) / (Fintype.card U : ℚ))^2 ≤ energy label :=
    show _ ≤ ∑ v : U, (((Finset.univ.filter fun i => label i = v).card : ℚ) -
      (Fintype.card I : ℚ) / (Fintype.card U : ℚ))^2 from
      Finset.single_le_sum
        (fun v _ => sq_nonneg (((Finset.univ.filter fun i => label i = v).card : ℚ) -
          (Fintype.card I : ℚ) / (Fintype.card U : ℚ))) (Finset.mem_univ u)
  simpa only [abs_of_nonneg hx] using sq_le_sq.mp (hone.trans h)

end Counts

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Denominator-cleared scores for incidence/head conditional expectation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section General
variable {A W J : Type*} [DecidableEq A]

private theorem sum_map_div (xs : List J) (f : J → ℚ) (d : ℚ) :
    (xs.map (fun j => f j / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons j xs ih => simp [ih, add_div]

theorem wordExpectation_div (alphabet : List W) (f : (A → W) → ℚ)
    (remaining : List A) (ω : A → W) (d : ℚ) :
    wordExpectation alphabet (fun η => f η / d) remaining ω =
      wordExpectation alphabet f remaining ω / d := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
    simp only [wordExpectation, SubexponentialSAT.ConditionalExpectation.mean]
    simp_rw [ih]
    rw [sum_map_div]
    ring

theorem localEvaluator_div_numerator (alphabet : List W) (ha : alphabet ≠ [])
    (terms : List J) (f : J → (A → W) → ℕ) (support : J → Finset A) (S : ℕ)
    (remaining : List A) (hS : ∀ j, (active (support j) remaining).length ≤ S)
    (ω : A → W) (d offset : ℚ) :
    localEvaluator alphabet terms support (fun j η => (f j η : ℚ) / d)
      offset remaining ω =
      (commonNumerator alphabet terms f support S remaining ω : ℚ) /
        (d * (alphabet.length : ℚ)^S) - offset := by
  unfold localEvaluator
  simp_rw [wordExpectation_div,
    local_average_eq_scaledCount alphabet ha _ _ S remaining (hS _) ω]
  rw [sum_map_div, sum_map_div]
  have hc : (terms.map (fun j =>
      (scaledCount alphabet (f j) (support j) S remaining ω : ℚ))).sum =
      (commonNumerator alphabet terms f support S remaining ω : ℚ) := by
    simp [commonNumerator, Function.comp_def]
  rw [hc]
  ring
end General

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem naturalTerm_div (w : Weights) (x y : ℚ)
    (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator)
    (z : ScoreTerm I V Q) (ω : WordAssignment V E r Q) :
    scoreTerm ivar factor x y z ω =
      (naturalTerm ivar factor w z ω : ℚ) / w.denominator := by
  cases z with
  | inl p => rcases p with ⟨i,j⟩; simp only [scoreTerm, naturalTerm]; split_ifs <;> simp [hy]
  | inr p => rcases p with ⟨t,v,u⟩; simp only [scoreTerm, naturalTerm]; split_ifs <;> simp [hx]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem evaluator_eq_numerator (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator)
    (remaining : List ℕ) (hr : remaining.Nodup) (ω : ℕ → Word r Q) (offset : ℚ) :
    localEvaluator alphabet terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y) offset remaining ω =
      (numerator ivar factor alphabet terms indices w remaining ω : ℚ) /
        ((w.denominator : ℚ) * (alphabet.length : ℚ)^4) - offset := by
  have hf : numberedScoreTerm (r := r) (Q := Q) ivar factor indices x y =
      fun z η => (numberedTerm ivar factor indices w z η : ℚ)/(w.denominator : ℚ) := by
    funext z η
    exact naturalTerm_div ivar factor w x y hy hx z _
  rw [hf]
  apply localEvaluator_div_numerator alphabet ha
  intro z
  exact (active_length_le _ _ hr).trans
    (numberedScoreSupport_card_le ivar factor indices z)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem evaluator_le_iff (alphabet : List (Word r Q)) (ha : alphabet ≠ [])
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator)
    (remaining : List ℕ) (hr : remaining.Nodup) (ω η : ℕ → Word r Q) (offset : ℚ) :
    localEvaluator alphabet terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y) offset remaining ω ≤
    localEvaluator alphabet terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y) offset remaining η ↔
    numerator ivar factor alphabet terms indices w remaining ω ≤
      numerator ivar factor alphabet terms indices w remaining η := by
  rw [evaluator_eq_numerator ivar factor alphabet ha terms indices w x y hy hx remaining hr ω offset,
    evaluator_eq_numerator ivar factor alphabet ha terms indices w x y hy hx remaining hr η offset,
    sub_le_sub_iff_right, div_le_div_iff_of_pos_right]
  · exact_mod_cast Iff.rfl
  · have hq : (0 : ℚ) < alphabet.length := by exact_mod_cast List.length_pos_iff.mpr ha
    have hw : (0 : ℚ) < w.denominator := by exact_mod_cast w.denominator_pos
    positivity
end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype E] [DecidableEq I] in
theorem naturalAssignment_eq (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator) (n : ℕ) (fixed : List (Word r Q)) :
    SubexponentialSAT.Subexp.NaturalAssignment.assignNat a tail
      (sequentialNumerator ivar factor (a::tail) terms indices w a) n fixed =
    SubexponentialSAT.ConditionalExpectation.assignWithEvaluator a tail
      (sequentialEvaluator (a::tail) terms (numberedScoreSupport ivar factor indices)
        (numberedScoreTerm ivar factor indices x y)
        (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a) n fixed := by
  apply SubexponentialSAT.Subexp.NaturalAssignment.assignNat_eq_assignWithEvaluator
  intro n fixed u v
  exact evaluator_le_iff ivar factor (a::tail) (List.cons_ne_nil _ _) terms indices w
    x y hy hx (List.range' (u::fixed).length n) List.nodup_range'
    (decode a (u::fixed)) (decode a (v::fixed)) _
end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramController
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed dynamic assignment controller, specialized to the new exact
weighted scores. The producer contract is explicit and must be discharged by
an actual score-stream program; it is not a unit-cost score operation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Controller
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype E] [DecidableEq I] in
theorem selectedValues_eq_computedWords (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights)
    (x y : ℚ) (hy : y^2 = (w.incidence : ℚ)/w.denominator)
    (hx : x^2 = (w.head : ℚ)/w.denominator) :
    (fun i => decode a (selectedValues ivar factor a tail terms indices w) (indexCode indices i)) =
      computedWords ivar factor a tail terms indices x y := by
  unfold selectedValues computedWords localAssign
  rw [naturalAssignment_eq ivar factor a tail terms indices w x y hy hx]

end Controller
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

theorem factor_index (A N : ℕ) (f : Fin N) :
    LocalExpectation.indexCode (indices A N) (.inr f) = A + f.val := by
  unfold indices
  rw [Packing.headsFirst_index_factor]
  simp [LocalExpectation.indexCode]

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The head mask and factor context are read from the actual assignment
controller's output. Distinct head colors give disjoint ambient masks. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT MulticolorTypes

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

theorem source_head_index (v : Fin n) :
    LocalExpectation.indexCode (LeafHeadFactorsProgram.indices n N) (.inl v)=v.val := by
  unfold LeafHeadFactorsProgram.indices
  rw [Packing.headsFirst_index_head _ _ _ (by simp)]
  simp [LocalExpectation.indexCode]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramWeights
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit positive denominator and bit bounds for the two rational weights. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram

theorem Weights.ofFractions_incidence (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) :
    ((yn : ℚ)/yd)^2 =
      ((Weights.ofFractions xn xd yn yd hxd hyd).incidence : ℚ) /
        (Weights.ofFractions xn xd yn yd hxd hyd).denominator := by
  have hx : (xd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hxd
  have hy : (yd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hyd
  simp only [Weights.ofFractions, Nat.cast_mul, Nat.cast_pow]
  field_simp


theorem Weights.ofFractions_head (xn xd yn yd : ℕ) (hxd : 0 < xd) (hyd : 0 < yd) :
    ((xn : ℚ)/xd)^2 =
      ((Weights.ofFractions xn xd yn yd hxd hyd).head : ℚ) /
        (Weights.ofFractions xn xd yn yd hxd hyd).denominator := by
  have hx : (xd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hxd
  have hy : (yd : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hyd
  simp only [Weights.ofFractions, Nat.cast_mul, Nat.cast_pow]
  field_simp


end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeadsScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native scope selector has precisely the rational weights required by
the correlated-packing proof. All lists here are the actual producer lists. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes PackingProgram
open PackingProgram.Assembly

theorem complete_alphabet_length {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    (a::tail).length=r^Q := by
  have he : (a::tail).toFinset=Finset.univ :=
    Finset.eq_univ_of_forall (fun z => List.mem_toFinset.mpr (haC z))
  calc
    _ = (a::tail).toFinset.card := (List.toFinset_card_of_nodup haN).symm
    _ = r^Q := by rw [he]; simp

theorem problem_x_eq (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    problemX p=(p.incidences:ℚ)/((p.s:ℚ)*(a::tail).length^2) := by
  unfold problemX
  rw [complete_alphabet_length a tail haN haC]
  simp only [card_universalType,Nat.cast_pow]
  rw [show p.Q*(1+1)=p.Q*2 by omega,pow_mul]
  ring

theorem problem_weight_head (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    (problemX p)^2=((problemWeights p a tail).head:ℚ)/(problemWeights p a tail).denominator := by
  rw [problem_x_eq p a tail haN haC]
  simpa only [problemWeights,Scope.weights,Nat.cast_mul,Nat.cast_pow] using
    Weights.ofFractions_head p.incidences (p.s*(a::tail).length^2) p.n (2*p.r)
      (Nat.mul_pos p.hs (pow_pos (by simp) 2)) (Nat.mul_pos (by decide) p.hr)

theorem problem_weight_incidence (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    ((p.n:ℚ)/(2*(p.r:ℚ)))^2=((problemWeights p a tail).incidence:ℚ)/
      (problemWeights p a tail).denominator := by
  simpa only [problemWeights,Scope.weights,Nat.cast_mul,Nat.cast_ofNat] using
    Weights.ofFractions_incidence p.incidences (p.s*(a::tail).length^2) p.n (2*p.r)
      (Nat.mul_pos p.hs (pow_pos (by simp) 2)) (Nat.mul_pos (by decide) p.hr)

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingConcrete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete bucket scans and embeddings for the searched incidence labels. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

section General
variable {I U : Type*} [Fintype I] [Fintype U] [DecidableEq I] [DecidableEq U]
  [Nonempty U]

theorem concrete_coverage_of_energy (P : PackingData I U) (ε : ℚ) (hε : 0 ≤ ε)
    (h : energy P.label ≤ (ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ))^2) :
    (1-ε)*(Fintype.card I : ℚ) ≤ (P.blockCount : ℚ)*Fintype.card U := by
  apply P.coverage_of_count_lower ε Fintype.card_pos hε
  intro u
  have hx : 0 ≤ ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) := by positivity
  have hh := (abs_le.mp (count_deviation_le P.label hx h u)).1
  rw [SubexponentialSAT.BlockPacking.count_eq_filter_card]
  have hN : (0 : ℚ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hl : (1-ε)*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) ≤
      ((Finset.univ.filter fun i => P.label i = u).card : ℚ) := by
    calc
      _ = (Fintype.card I : ℚ)/(Fintype.card U : ℚ) -
          ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) := by ring
      _ ≤ _ := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hN).mp hl
end General

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

theorem packing_label (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (packing p a tail).label=Packing.incidenceType (owner p) (factor p) (words p a tail) := by
  rfl

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankCoverage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native packing's coverage follows from the energy of the actual
conditional-expectation assignment, with no independent quality witness. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LayoutProducedHeads

 theorem words_eq_assignment (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    words p a tail=problemAssignment p a tail := by
  funext v
  have he := congrFun (PackingProgram.selectedValues_eq_computedWords
    (owner p) (factor p) a tail
    (PackingProgram.Assembly.Scope.terms p.scopes p.n p.mask p.Q)
    (PackingIncidenceInput.Semantics.seedIndices p.n p.factors)
    (problemWeights p a tail) (problemX p) ((p.n:ℚ)/(2*(p.r:ℚ)))
    (problem_weight_incidence p a tail) (problem_weight_head p a tail haN haC)) v
  cases v with
  | inl v =>
    have hi : LocalExpectation.indexCode
        (PackingIncidenceInput.Semantics.seedIndices p.n p.factors) (.inl v)=v.val :=
      LeafHeadSetupProgram.source_head_index v
    rw [hi,SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD] at he
    change (p.words a tail).getD v.val a=problemAssignment p a tail (.inl v) at he
    rw [List.getD_eq_getElem _ _ (by rw [p.words_length]; omega)] at he
    simpa only [words,List.get_eq_getElem] using he
  | inr f =>
    have hi : LocalExpectation.indexCode
        (PackingIncidenceInput.Semantics.seedIndices p.n p.factors) (.inr f)=p.n+f.val :=
      LeafHeadFactorsProgram.factor_index p.n p.factors f
    rw [hi,SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD] at he
    change (p.words a tail).getD (p.n+f.val) a=problemAssignment p a tail (.inr f) at he
    rw [List.getD_eq_getElem _ _ (by rw [p.words_length]; omega)] at he
    simpa only [words,List.get_eq_getElem] using he

 theorem packing_coverage_oai (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail)
    (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i => owner p i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i => factor p i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) :
    (1-1/(p.s:ℚ))*(p.incidences:ℚ) ≤
      (packing p a tail).blockCount*(Fintype.card (UniversalType p.r p.Q 1):ℚ) := by
  let : NeZero p.r := ⟨Nat.ne_of_gt p.hr⟩
  have he := (problem_computed_energies p a tail haN haC B b hB hb hM hn hlarge hhead).1
  have henergy : Packing.energy (packing p a tail).label ≤
      ((1/(p.s:ℚ))*(Fintype.card (Fin p.incidences):ℚ)/
        (Fintype.card (UniversalType p.r p.Q 1):ℚ))^2 := by
    rw [packing_label,words_eq_assignment p a tail haN haC]
    simpa only [problemX,Fintype.card_fin,owner,factor] using he
  simpa only [Fintype.card_fin] using
    Packing.concrete_coverage_of_energy (packing p a tail) (1/(p.s:ℚ)) (by positivity) henergy

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage_oai
