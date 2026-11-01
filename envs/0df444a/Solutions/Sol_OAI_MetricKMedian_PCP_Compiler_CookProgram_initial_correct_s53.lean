-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:44:21.709409+00:00
-- url     : https://prove2.me/submissions/d96fce2f-9b7f-4670-950f-b698d8df823b

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K082
import Theorems.Thm_OAI_MetricKMedian_PCP_AlphabetReduction_padded_complete_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_CookProgram_correct_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_LocalRelation_sound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Rates
variable {S T : Type} [Fintype S] [Fintype T]

theorem testRate_nonneg (p : S → Prop) : 0 ≤ testRate p := by
  classical
  exact expect_nonneg (by intro s _; split_ifs <;> norm_num)

theorem testRate_eq_count (p : S → Prop) [DecidablePred p] :
    testRate p = ((univ.filter p).card : ℝ) / Fintype.card S := by
  classical
  rw [testRate, Fintype.expect_eq_sum_div_card]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  apply sum_congr rfl
  intro s _
  split_ifs <;> rfl

theorem testRate_prod (p : S → T → Prop) :
    testRate (fun z : S × T => p z.1 z.2) = 𝔼 s, testRate (p s) := by
  classical
  unfold testRate
  rw [← univ_product_univ, expect_product]

theorem testRate_fst (p : S → Prop) [Nonempty T] :
    testRate (fun z : S × T => p z.1) = testRate p := by
  classical
  rw [testRate_prod (fun s (_ : T) => p s)]
  unfold testRate
  simp only [Fintype.expect_const]

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_LocalReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

variable (R : Relation K) [DecidablePred (· ∈ R)]

theorem rejectionWeight_nonneg (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    0 ≤ rejectionWeight R f h u v := by
  unfold rejectionWeight QuadraticSystem.rejectionWeight
  exact add_nonneg (add_nonneg
    (add_nonneg (add_nonneg (add_nonneg (testRate_nonneg _) (testRate_nonneg _))
      (testRate_nonneg _)) (testRate_nonneg _)) (testRate_nonneg _)) (testRate_nonneg _)

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Queries
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.testNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQueries

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

theorem testRate_pi_eval {I : Type} [Fintype I] [DecidableEq I]
    (S : I → Type) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (i : I) (p : S i → Prop) :
    testRate (fun s : (i : I) → S i => p (s i)) = testRate p := by
  classical
  calc
    _ = testRate (fun s : S i × ((j : {j // j ≠ i}) → S j.val) => p s.1) :=
      testRate_equiv (Equiv.piSplitAt i S) (fun s => p s.1)
    _ = _ := testRate_fst p

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]
variable (R : Relation K) [DecidablePred (· ∈ R)]

theorem packed_rate (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    testRate (fun s => (packed R s).Rejects (assignment R f h u v)) =
      rejectionWeight R f h u v / 6 := by
  classical
  change testRate (fun s : Fin 6 × Pad R =>
    (query R s.1 (s.2 s.1)).Rejects (assignment R f h u v)) = _
  rw [testRate_prod (S := Fin 6) (T := Pad R)
    (fun (i : Fin 6) (s : Pad R) => (query R i (s i)).Rejects (assignment R f h u v))]
  have hm (i : Fin 6) :
      testRate (fun s : Pad R => (query R i (s i)).Rejects (assignment R f h u v)) =
      testRate (fun s : Sample R i => (query R i s).Rejects (assignment R f h u v)) :=
    testRate_pi_eval (Sample R) i
      (fun s : Sample R i => (query R i s).Rejects (assignment R f h u v))
  change (𝔼 i, testRate (fun s : Pad R =>
    (query R i (s i)).Rejects (assignment R f h u v))) = _
  simp_rw [hm]
  rw [Fintype.expect_eq_sum_div_card]
  norm_num only [Fintype.card_fin, Fin.sum_univ_succ, Fin.reduceSucc,
    Finset.sum_empty, add_zero]
  congr 1
  simp only [query, FourQuery.Rejects, firstPos, secondPos, leftPos, rightPos,
    rejectionWeight, QuadraticSystem.rejectionWeight,
    linearityRate, multiplicationRate, QuadraticSystem.equationRate,
    boundaryRate, derivative, add_assoc]
  simp only [Function.comp_def]
  simp only [assignment, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  simp only [Bool.not_eq_true]
  simp
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply testRate_congr
    intro s
    exact decide_eq_false_iff_not
  · apply congrArg₂ (fun x y : ℝ => x + y)
    · apply testRate_congr
      intro s
      exact decide_eq_false_iff_not
    · apply congrArg₂ (fun x y : ℝ => x + y)
      · apply testRate_congr
        intro s
        exact decide_eq_false_iff_not
      · apply congrArg₂ (fun x y : ℝ => x + y)
        · apply testRate_congr
          intro s
          exact decide_eq_false_iff_not
        · rfl

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPQueries

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_AlphabetReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.testNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]

theorem testRate_eq_zero_iff {S : Type} [Fintype S] (p : S → Prop) :
    testRate p = 0 ↔ ∀ s, ¬ p s := by
  classical
  unfold testRate
  rw [Finset.expect_eq_zero_iff_of_nonneg (by intro s _; split_ifs <;> norm_num)]
  simp

namespace AlphabetReduction
variable (K)

variable {K}
variable (C : BinaryCSP V E (BitVector K))

omit [Fintype V] [Fintype E] in
theorem edge_rate (a : Position C → Bit) (e : E) :
    testRate (fun s : EdgeSample K => ((reduced C).query (e,s)).Rejects a) =
      LocalRelation.rejectionWeight (relation C e) (firstTable C a e) (secondTable C a e)
        (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) / 6 := by
  classical
  let R := relation C e
  let p := fun (i : Fin 6) (s : LocalRelation.Sample R i) =>
    (LocalRelation.query R i s).Rejects (a ∘ localMap C e)
  have hm (i : Fin 6) :
      testRate (fun s : UniversalPad K => p i (s (C.allowed e) i)) =
      testRate (fun s : LocalRelation.Pad R => p i (s i)) :=
    testRate_pi_eval (fun R : Relations K => LocalRelation.Pad (R : LocalRelation.Relation K))
      (C.allowed e) (fun s : LocalRelation.Pad R => p i (s i))
  change testRate (fun s : Fin 6 × UniversalPad K => p s.1 (s.2 (C.allowed e) s.1)) = _
  rw [testRate_prod (S := Fin 6) (T := UniversalPad K)
    (fun (i : Fin 6) (s : UniversalPad K) => p i (s (C.allowed e) i))]
  simp_rw [hm]
  rw [← testRate_prod (S := Fin 6) (T := LocalRelation.Pad R)
    (fun (i : Fin 6) (s : LocalRelation.Pad R) => p i (s i))]
  change testRate (fun s => (LocalRelation.packed R s).Rejects (a ∘ localMap C e)) = _
  rw [restriction]
  exact LocalRelation.packed_rate _ _ _ _ _

omit [Fintype V] in
theorem sound (a : Position C → Bit) :
    C.rejection (decoded C a) / 96 ≤ (reduced C).rejection a := by
  classical
  rw [FourCSP.rejection, testRate_prod (S := E) (T := EdgeSample K)
    (fun e s => ((reduced C).query (e,s)).Rejects a)]
  unfold BinaryCSP.rejection testRate
  rw [Finset.expect_div]
  apply Finset.expect_le_expect
  intro e _
  change (@ite ℝ ((decoded C a (C.left e), decoded C a (C.right e)) ∉ C.allowed e)
    (Classical.propDecidable _) 1 0) / 96 ≤ testRate (fun s : EdgeSample K =>
      ((reduced C).query (e,s)).Rejects a)
  rw [edge_rate]
  by_cases he : (decoded C a (C.left e), decoded C a (C.right e)) ∉ C.allowed e
  · simp only [ite_eq_left he]
    have hh := LocalRelation.sound_s53 (relation C e) (firstTable C a e) (secondTable C a e)
      (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) he
    linarith
  · simp only [ite_eq_right he]
    have hh := LocalRelation.rejectionWeight_nonneg (relation C e) (firstTable C a e)
      (secondTable C a e) (vertexTable C a (C.left e)) (vertexTable C a (C.right e))
    linarith

end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_CSPMix
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} [Fintype A] [DecidableEq A] (G : PortGraph V D)

omit [DecidableEq A] in
@[simp] lemma always_failure [Fintype V] [Fintype D] (a : V → A) :
    testRate ((always (A := A) G).Bad a)=0 := by
  exact (testRate_eq_zero_iff _).mpr (always_bad G a)

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortCSP.always_failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

theorem testRate_singleton {S : Type} [Fintype S] [DecidableEq S] (x : S) :
    testRate (fun s => s = x) = 1 / Fintype.card S := by
  classical
  rw [testRate_eq_count]
  have hf : univ.filter (fun s : S => s = x) = {x} := by
    ext s
    simp
  rw [hf]
  simp

theorem testRate_ge_atom {S : Type} [Fintype S] (p : S → Prop) (x : S) (hx : p x) :
    1 / (Fintype.card S : ℝ) ≤ testRate p := by
  classical
  rw [← testRate_singleton x]
  exact testRate_mono (by intro s hs; simpa only [hs] using hx)

namespace IncidenceReduction
variable {P T : Type} [Fintype T] (C : FourCSP P T)

omit [Fintype T] in
theorem bad_incidence (a : P ⊕ T → Label) (t : T)
    (ht : (C.query t).Rejects (decoded a)) :
    ∃ j : Fin 4, (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
      (reduced C).allowed (t,j) := by
  by_contra h
  push Not at h
  have hall (j : Fin 4) := (allowed_iff C (t,j) _ _).mp (h j)
  have ha : a (.inr t) = decoded a ∘ (C.query t).address := by
    funext j
    exact (hall j).2
  have hy := (hall 0).1
  exact ht (ha ▸ hy)

theorem sound (a : P ⊕ T → Label) :
    C.rejection (decoded a) / 4 ≤ (reduced C).rejection a := by
  classical
  rw [BinaryCSP.rejection, testRate_prod (S := T) (T := Fin 4)
    (fun t j => (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
      (reduced C).allowed (t,j))]
  unfold FourCSP.rejection testRate
  rw [Finset.expect_div]
  apply expect_le_expect
  intro t _
  change (@ite ℝ ((C.query t).Rejects (decoded a)) (Classical.propDecidable _) 1 0)/4 ≤
    testRate (fun j : Fin 4 => (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
      (reduced C).allowed (t,j))
  by_cases ht : (C.query t).Rejects (decoded a)
  · rw [ite_eq_left ht]
    obtain ⟨j,hj⟩ := bad_incidence C a t ht
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using testRate_ge_atom
      (fun j : Fin 4 => (a ((reduced C).left (t,j)), a ((reduced C).right (t,j))) ∉
        (reduced C).allowed (t,j)) j hj
  · rw [ite_eq_right ht, zero_div]
    exact testRate_nonneg _

end IncidenceReduction

namespace AlphabetReduction
variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))

omit [Fintype V] in
theorem binary_sound (a : Position C ⊕ Test (E := E) (K := K) → IncidenceReduction.Label) :
    C.rejection (decoded C (IncidenceReduction.decoded a)) / 384 ≤ (binary C).rejection a := by
  have h₁ := sound C (IncidenceReduction.decoded a)
  have h₂ := IncidenceReduction.sound (reduced C) a
  change _ ≤ (IncidenceReduction.reduced (reduced C)).rejection a
  linarith

end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPBinaryReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddedAlphabet
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddedAlphabet
namespace MetricKMedian.PCP.AlphabetReduction
open Finset
open scoped BigOperators Classical

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))
omit [Fintype V] in
lemma padded_sound (a : PaddedNode V E K → IncidenceReduction.Label) :
    C.rejection (decoded C (IncidenceReduction.decoded (a ∘ nodeEmbed C)))/384 ≤
      (paddedBinary C).rejection a := binary_sound C (a ∘ nodeEmbed C)
end MetricKMedian.PCP.AlphabetReduction

end Inline_PCPPaddedAlphabet

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BinaryReindex
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E V' E' A : Type} [DecidableEq A]
variable (C : BinaryCSP V E A) (ev : V ≃ V') (ee : E ≃ E')
omit [DecidableEq A]
lemma reindex_satisfies (a : V' → A) :
    (C.reindex ev ee).Satisfies a ↔ C.Satisfies (a ∘ ev) := by
  constructor
  · intro h e
    simpa only [reindex,Equiv.symm_apply_apply,Function.comp_def] using h (ee e)
  · intro h e
    exact h (ee.symm e)
lemma reindex_complete (a : V → A) (h : C.Satisfies a) :
    (C.reindex ev ee).Satisfies (a ∘ ev.symm) := by
  apply (C.reindex_satisfies ev ee _).mpr
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using h
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPBinaryReindex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawCSP
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.CloudCopies.honest_dart _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.FlexibleCloud.honest_dart _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawCSP
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

lemma csp_ext {V E A : Type} {C D : BinaryCSP V E A}
    (hl : C.left=D.left) (hr : C.right=D.right) (ha : C.allowed=D.allowed) : C=D := by
  cases C; cases D; simp_all
namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
variable {V E : Type} [Fintype V] [Fintype E]
omit [Fintype A] [DecidableEq A] [Fintype V] [Fintype E] in
lemma Represents.csp_eq {t : CSPTable A} {C : BinaryCSP V E A}
    (r : t.Represents C) (h : t.WellFormed) : t.csp h=C.reindex r.vertex r.edge := by
  cases C with
  | mk l rr aa =>
    apply csp_ext
    · funext i
      apply Fin.ext
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg Prod.fst hr
    · funext i
      apply Fin.ext
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg (fun x : CSPRow A => x.2.1) hr
    · funext i
      have hr := r.row (r.edge.symm i)
      simpa only [Equiv.apply_symm_apply,csp,BinaryCSP.reindex] using congrArg (fun x : CSPRow A => x.2.2) hr
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_TablePromises
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTablePromises
namespace MetricKMedian.PCP.Compiler.CSPTable
open scoped Classical

variable {A V E : Type} [Fintype A] [DecidableEq A] [Fintype V] [Fintype E]
variable {s : CSPTable A} {C : BinaryCSP V E A}
omit [Fintype A] [DecidableEq A] [Fintype V] [Fintype E] in
lemma Represents.satisfies (r : s.Represents C) (h : s.WellFormed) :
    (∃ a, (s.csp h).Satisfies a) ↔ ∃ a, C.Satisfies a := by
  rw [r.csp_eq h]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ r.vertex,(C.reindex_satisfies _ _ _).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ r.vertex.symm,C.reindex_complete _ _ _ ha⟩
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPTablePromises

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_FiniteConstraints
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteConstraints

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E A B : Type} [DecidableEq A] [Fintype B]
variable (C : BinaryCSP V E A) (decode : B → A)
lemma pullLabels_satisfies (a : V → B) :
    (C.pullLabels decode).Satisfies a ↔ C.Satisfies (decode ∘ a) := by
  simp only [Satisfies,pullLabels,mem_filter,mem_univ,true_and,Function.comp_def]
lemma pullLabels_complete (encode : A → B) (he : Function.LeftInverse decode encode)
    (a : V → A) (h : C.Satisfies a) : (C.pullLabels decode).Satisfies (encode ∘ a) := by
  apply (C.pullLabels_satisfies decode _).mpr
  intro e
  change (decode (encode (a (C.left e))), decode (encode (a (C.right e))))∈C.allowed e
  rw [he _,he _]
  exact h e
end BinaryCSP
end MetricKMedian.PCP

end Inline_PCPFiniteConstraints

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_InitialAlphabet
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInitialAlphabet

namespace MetricKMedian.PCP
open Function Finset
open scoped Classical

namespace BinaryCSP
variable {V E A : Type} [Fintype E] [DecidableEq A] (C : BinaryCSP V E A)
omit [DecidableEq A] in
lemma rejection_zero_iff (a : V → A) : C.rejection a=0 ↔ C.Satisfies a := by
  rw [rejection,testRate_eq_zero_iff]
  simp only [not_not,Satisfies]
end BinaryCSP
namespace InitialAlphabet
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
omit [Fintype A] [Nonempty A] in
lemma oneHot_injective : Injective (oneHot A) := by
  intro a b hab
  by_contra h
  have hh := congrFun hab a
  simp only [oneHot,ite_true,ite_eq_right h] at hh
  exact one_ne_zero hh
omit [Fintype A] in
lemma decode_oneHot : LeftInverse (decode A) (oneHot A) := leftInverse_invFun (oneHot_injective A)
variable {V E : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
omit [Fintype V] [Fintype E] in
lemma bits_iff : (∃ a, (bits A C).Satisfies a) ↔ ∃ a, C.Satisfies a := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨decode A ∘ a,(C.pullLabels_satisfies (decode A) a).mp ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨oneHot A ∘ a,C.pullLabels_complete (decode A) (oneHot A) (decode_oneHot A) a ha⟩
end InitialAlphabet
end MetricKMedian.PCP

end Inline_PCPInitialAlphabet

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_InitialTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInitialTable
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic InitialAlphabet
open scoped Classical

namespace InitialProgram
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
variable (s : CSPTable A) (h : s.WellFormed)
lemma correct : (∃ a, ((table A s).csp (valid A s h)).Satisfies a) ↔ ∃ a, (s.csp h).Satisfies a := by
  rw [(represents A s h).satisfies]
  have hb := (bitsRep A s h).satisfies (bits_valid A s h)
  rw [InitialAlphabet.bits_iff] at hb
  constructor
  · rintro ⟨a,ha⟩
    apply hb.mp
    let C := (bits A s).csp (bits_valid A s h)
    refine ⟨AlphabetReduction.decoded C (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed C)),?_⟩
    have hh := AlphabetReduction.padded_sound C a
    rw [(AlphabetReduction.paddedBinary C).rejection_zero_iff _ |>.mpr ha] at hh
    apply (C.rejection_zero_iff _).mp
    have hn := testRate_nonneg (fun e =>
      (AlphabetReduction.decoded C (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed C)) (C.left e),
       AlphabetReduction.decoded C (IncidenceReduction.decoded (a ∘ AlphabetReduction.nodeEmbed C)) (C.right e))∉C.allowed e)
    change 0≤C.rejection _ at hn
    linarith
  · intro ha
    obtain ⟨a,ha⟩ := hb.mpr ha
    exact AlphabetReduction.padded_complete_s53 _ a ha
end InitialProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPInitialTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookAmplify
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookAmplify
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM_1
lemma initial_correct_s53_oai (x : Word) : (∃ a, ((initial P p x).csp (initial_valid P p x)).Satisfies a) ↔
    ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true := by
  exact (InitialProgram.correct (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m))
    (table P p x) (wellFormed P p x)).trans (correct_s53 P p x)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53_oai := @OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53_oai
