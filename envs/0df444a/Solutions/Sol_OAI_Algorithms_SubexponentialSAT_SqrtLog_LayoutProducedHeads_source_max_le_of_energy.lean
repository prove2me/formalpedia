-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:28:57.23709+00:00
-- url     : https://prove2.me/submissions/127611b7-e1aa-414d-94aa-6821c223ea97

import Mathlib
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S091

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem headOrder_injective (p : ℕ → Bool) (n : ℕ) : Function.Injective (headOrder p n) := by
  intro i j hij
  apply List.nodup_iff_injective_getElem.mp (chosenIds_nodup p n)
  exact congrArg Fin.val hij

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingVariance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact collision-energy bounds used in correlated incidence packing. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance

noncomputable section

variable {Ω I U : Type*} [Fintype Ω] [Fintype I] [Fintype U]
  [DecidableEq I] [DecidableEq U] [Nonempty Ω] [Nonempty U]

omit [DecidableEq I] [Nonempty U] in
theorem energy_nonneg (label : I → U) : 0 ≤ energy label := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] [NeZero r] in
theorem head_count_upper (ω : WordAssignment V E r Q) {y : ℚ}
    (hy : 0 ≤ y) (h : headEnergy ω ≤ y^2) (t : Fin Q) (g : Fin r) :
    ((Finset.univ.filter fun v : V => ω (.inl v) t = g).card : ℚ) ≤
      (Fintype.card V : ℚ)/(r : ℚ) + y := by
  have hterm : energy (fun v : V => ω (.inl v) t) ≤ headEnergy ω :=
    Finset.single_le_sum (fun _ _ => energy_nonneg _) (Finset.mem_univ t)
  have hh := (abs_le.mp (count_deviation_le (fun v : V => ω (.inl v) t)
    hy (hterm.trans h) g)).2
  simpa only [Fintype.card_fin] using (show _ ≤ _ from (by linarith :
    ((Finset.univ.filter fun v : V => ω (.inl v) t = g).card : ℚ) ≤
      (Fintype.card V : ℚ)/(Fintype.card (Fin r) : ℚ) + y))

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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

theorem assignNat_length {X : Type*} (a : X) (tail : List X)
    (evaluate : ℕ → List X → ℕ) (n : ℕ) (fixed : List X) :
    (Subexp.NaturalAssignment.assignNat a tail evaluate n fixed).length = n + fixed.length := by
  induction n generalizing fixed with
  | zero => simp [Subexp.NaturalAssignment.assignNat]
  | succ n ih =>
    simp only [Subexp.NaturalAssignment.assignNat, ih, List.length_cons]
    omega

variable {I : Type*} [Fintype I] [DecidableEq I] {A N r Q : ℕ}

omit [Fintype I] [DecidableEq I] in
@[simp] theorem sourceRows_length (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights) :
    (sourceRows owner factor a tail terms w).length = A + N := by
  simp [sourceRows, PackingProgram.selectedValues, assignNat_length]

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

omit [DecidableEq I] in
theorem source_head_row (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator) (v : Fin n) :
    (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w).getD v.val []=
      Subexp.ReadPlan.encodeWord
        (Packing.computedWords owner factor a tail terms (LeafHeadFactorsProgram.indices n N) x y (.inl v)) := by
  let values := PackingProgram.selectedValues owner factor a tail terms
    (LeafHeadFactorsProgram.indices n N) w
  have hlen : values.length=n+N := by
    simp [values,PackingProgram.selectedValues,LeafHeadFactorsProgram.assignNat_length]
  have hv : v.val < values.reverse.length := by
    rw [List.length_reverse,hlen]
    omega
  have he := congrFun (PackingProgram.selectedValues_eq_computedWords
    owner factor a tail terms (LeafHeadFactorsProgram.indices n N) w x y hy hx) (.inl v)
  rw [source_head_index,Subexp.AssignmentEnumeration.decode_eq_reverse_getD,
    List.getD_eq_getElem _ _ hv] at he
  unfold LeafHeadFactorsProgram.sourceRows
  change (values.reverse.map Subexp.ReadPlan.encodeWord).getD v.val []=_
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hv),List.getElem_map,he]

omit [DecidableEq I] in
theorem source_head_predicate (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    HeadIdentifierProgram.predicate
      (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val) v.val=
      (low v && decide (Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x y (.inl v) t=g)) := by
  unfold HeadIdentifierProgram.predicate
  rw [source_head_row owner factor a tail terms w x y hy hx v,
    HeadIdentifierProgram.encodeWord_getD]
  simp [HeadIdentifierProgram.lowBits,List.getD_eq_getElem?_getD]

omit [DecidableEq I] in
theorem selectedHeads_source_mem (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.val∈selectedHeads n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val) ↔
      low v=true ∧ Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x y (.inl v) t=g := by
  simp [selectedHeads,HeadIdentifierProgram.chosenIds,v.isLt,
    source_head_predicate owner factor a tail terms w x y hy hx low t g v]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeads
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emitted original-ID head lists inherit the searched packing's
head bound. Taking the maximum is proof-only and introduces no new search. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LeafHeadSetupProgram

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

omit [DecidableEq I] in
theorem source_selected_length_le
    (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool) (t : Fin Q) (g : Fin r) :
    (selectedHeads n (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)).length ≤
    (Packing.headSupport (Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x y) t g).card := by
  classical
  let : NeZero r := ⟨by have := g.isLt; omega⟩
  let rows := LeafHeadFactorsProgram.sourceRows owner factor a tail terms w
  let p := HeadIdentifierProgram.predicate rows (HeadIdentifierProgram.lowBits low)
    (t.val*r+g.val)
  let S := Packing.headSupport (Packing.computedWords owner factor a tail terms
    (LeafHeadFactorsProgram.indices n N) x y) t g
  let f : Fin (HeadIdentifierProgram.count p n) → S := fun i =>
    ⟨HeadIdentifierProgram.headOrder p n i, by
      apply (Packing.mem_headSupport _ _ _ _).mpr
      exact ((selectedHeads_source_mem owner factor a tail terms w x y hy hx low t g
        (HeadIdentifierProgram.headOrder p n i)).mp (List.getElem_mem i.isLt)).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact HeadIdentifierProgram.headOrder_injective p n (congrArg Subtype.val hij)
  change HeadIdentifierProgram.count p n ≤ S.card
  simpa only [Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

theorem maxSelected_rat_le (n Q r : ℕ) (rows : List (List Bool)) (low : List Bool)
    (bound : ℚ) (hb : 0 ≤ bound)
    (h : ∀ (t : Fin Q) (g : Fin r),
      ((selectedHeads n rows low (t.val*r+g.val)).length : ℚ) ≤ bound) :
    (maxSelected n Q r rows low : ℚ) ≤ bound := by
  unfold maxSelected
  rcases (Finset.univ : Finset (Fin Q × Fin r)).eq_empty_or_nonempty with he | hn
  · simpa only [he,Finset.sup_empty,Nat.bot_eq_zero,Nat.cast_zero] using hb
  · obtain ⟨z,_,hz⟩ := Finset.exists_mem_eq_sup _ hn
      (fun z : Fin Q × Fin r => (selectedHeads n rows low (z.1.val*r+z.2.val)).length)
    rw [hz]
    exact h z.1 z.2

omit [DecidableEq I] in
theorem source_max_le_of_energy_oai
    (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x : ℚ) (hr : 0 < r)
    (hy : ((n:ℚ)/(2*(r:ℚ)))^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool)
    (henergy : Packing.headEnergy (Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) ≤
        ((n:ℚ)/(2*(r:ℚ)))^2) :
    (maxSelected n Q r (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(n:ℚ)/(2*(r:ℚ)) := by
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  have hrq : (0:ℚ) < r := by exact_mod_cast hr
  apply maxSelected_rat_le _ _ _ _ _ _ (by positivity)
  intro t g
  have hlen := source_selected_length_le owner factor a tail terms w x
    ((n:ℚ)/(2*(r:ℚ))) hy hx low t g
  have hhead := Packing.head_count_upper (y := (n:ℚ)/(2*(r:ℚ)))
    (Packing.computedWords owner factor a tail terms (LeafHeadFactorsProgram.indices n N)
      x ((n:ℚ)/(2*(r:ℚ)))) (by positivity) henergy t g
  change ((Packing.headSupport _ t g).card : ℚ) ≤ _ at hhead
  have hlenQ : ((selectedHeads n
      (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) (t.val*r+g.val)).length : ℚ) ≤
      ((Packing.headSupport (Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) t g).card : ℚ) := by
    exact_mod_cast hlen
  calc
    _ ≤ ((Packing.headSupport (Packing.computedWords owner factor a tail terms
        (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) t g).card : ℚ) := hlenQ
    _ ≤ (n:ℚ)/r+(n:ℚ)/(2*(r:ℚ)) := by simpa only [Fintype.card_fin] using hhead
    _ = _ := by field_simp; ring

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy_oai.{u_1}
