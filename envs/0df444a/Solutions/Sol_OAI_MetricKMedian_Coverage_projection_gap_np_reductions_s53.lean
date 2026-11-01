-- Prove2me | solution 1 for OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:46:52.203033+00:00
-- url     : https://prove2.me/submissions/db825006-1b5c-448b-86d8-37712e023330

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K084
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_CookProgram_initial_correct_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_CookProgram_projection_complete_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_SeedProgram_output_sound_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_FlexibleAmplifier_sound_of_power_bound_s53
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
-- module Solutions.OAIQ053_KM.KMedian_Amplification_LabelTransport
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLabelTransport

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BinaryCSP
variable {V E A B : Type} [Fintype E] [DecidableEq A] [DecidableEq B]
variable (C : BinaryCSP V E A) (e : A ≃ B)

omit [DecidableEq A] [DecidableEq B] in
lemma mapLabels_rejection (a : V → B) :
    (C.mapLabels e).rejection a=C.rejection (e.symm ∘ a) := by
  apply testRate_congr
  intro t
  exact not_congr (mapLabels_allowed C e t _ _)
end BinaryCSP

end MetricKMedian.PCP

end Inline_PCPLabelTransport

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Amplifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier

theorem capLoss_pos : 0 < capLoss := by norm_num [capLoss]

end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifier

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
variable [Fintype E] [Fintype E']
lemma reindex_rejection (a : V' → A) :
    (C.reindex ev ee).rejection a=C.rejection (a ∘ ev) := by
  unfold rejection reindex
  exact testRate_equiv ee.symm (fun e => (a (ev (C.left e)),a (ev (C.right e))) ∉ C.allowed e)
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
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
omit [Fintype A] [DecidableEq A] [Fintype V] in
lemma Represents.rejection (r : s.Represents C) (h : s.WellFormed) (a : Fin s.1.length → A) :
    (s.csp h).rejection a=C.rejection (a ∘ r.vertex) := by
  rw [r.csp_eq h]
  exact BinaryCSP.reindex_rejection _ _ _ _
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPTablePromises

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierProgram
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

variable (s : CSPTable Label) (h : s.WellFormed) [Nonempty (Fin s.2.length)]
lemma gap (δ : ℝ) (hg : ∀ a, δ≤(s.csp h).rejection a) :
    ∀ a, min (2*δ) (1/(capLoss:ℝ)) ≤ ((next s).csp (next_wellFormed s h)).rejection a := by
  intro a
  let a' := a ∘ (nextRep s h).vertex
  let B := (bits s).csp (bits_wellFormed s h)
  let b := AlphabetReduction.decoded B (IncidenceReduction.decoded (a' ∘ AlphabetReduction.nodeEmbed B))
  have hb := AlphabetReduction.padded_sound B a'
  change B.rejection b/384≤_ at hb
  have hr := (nextRep s h).rejection (next_wellFormed s h) a
  change _=(AlphabetReduction.paddedBinary B).rejection a' at hr
  rw [← hr] at hb
  have hm := (bitsRep s h).rejection (bits_wellFormed s h) b
  have he := (FlexibleAmplifier.powered (C s h) (CloudOrder.cloudEmbed (C s h) (EO s))
    (padding s h)).mapLabels_rejection (Advice.bitsEquiv Degree (Fin 4) radius) (b ∘ (bitsRep s h).vertex)
  change B.rejection b=_ at hm
  have hhbits := hm.trans he
  rw [hhbits] at hb
  have hh := FlexibleAmplifier.sound_of_power_bound_s53 (C s h)
    (CloudOrder.cloudEmbed (C s h) (EO s)) (padding s h) _ _ hb
  exact (min_le_min_right _ (mul_le_mul_of_nonneg_left (hg _) (by norm_num))).trans hh
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierIteration
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierIteration
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

lemma normalize_eq {s : CSPTable Label} (h : s.WellFormed) : normalize s=s :=
  ite_eq_left ((CSPTable.check_iff s).mpr h)
lemma iterate_gap {s : CSPTable Label} (h : s.WellFormed) (δ : ℝ)
    (hg : ∀ a, δ≤(s.csp h).rejection a) (n : ℕ) :
    ∀ a, min (2^n*δ) (1/(capLoss:ℝ))≤((iterate n s).csp (iterate_valid h n)).rejection a := by
  have hc : 0≤1/(capLoss:ℝ) := by positivity
  induction n with
  | zero =>
    intro a
    change min (2^0*δ) (1/(capLoss:ℝ)) ≤ (s.csp h).rejection a
    rw [pow_zero,one_mul]
    exact (min_le_left _ _).trans (hg a)
  | succ n ih =>
    have hh := iterate_valid h n
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp hh.1
    intro a
    have hn := gap (iterate n s) hh _ ih a
    apply le_trans _ hn
    rw [pow_succ]
    simp only [min_def]
    split_ifs <;> nlinarith
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierIteration

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierCompiler
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic Polynomial
open scoped Classical

lemma generate_sound {s : CSPTable Label} (h : s.WellFormed)
    (hc : ¬∃ a, (s.csp h).Satisfies a) :
    ∀ a, 1/(capLoss:ℝ)≤((generate s).csp (generate_valid s)).rejection a := by
  have hi : ∀a, 1/((s.2.length:ℕ):ℝ)≤(s.csp h).rejection a := by
    intro a
    have he : ∃ e, (a ((s.csp h).left e),a ((s.csp h).right e)) ∉ (s.csp h).allowed e := by
      by_contra hh
      push Not at hh
      exact hc ⟨a,hh⟩
    obtain ⟨e,he⟩ := he
    simpa only [BinaryCSP.rejection,Fintype.card_fin] using
      testRate_ge_atom (fun e => (a ((s.csp h).left e),a ((s.csp h).right e)) ∉ (s.csp h).allowed e) e he
  let n := Nat.log 2 s.2.length+1
  have hn : s.2.length ≤ 2^n := Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega : 1<2) _)
  have hn' : (s.2.length:ℝ)≤2^n := by exact_mod_cast hn
  have he : 0<(s.2.length:ℝ) := Nat.cast_pos.mpr h.1
  have hl : (1:ℝ) ≤ capLoss := by norm_num [capLoss]
  have hh : 1/(capLoss:ℝ)≤2^n*(1/(s.2.length:ℝ)) := by
    have h1 : (1:ℝ)≤2^n/(s.2.length:ℝ) := (le_div_iff₀ he).mpr (by simpa using hn')
    have h2 : (1:ℝ)/(capLoss:ℝ)≤1 := (div_le_one (Nat.cast_pos.mpr capLoss_pos)).mpr hl
    simpa only [mul_one_div] using h2.trans h1
  have hx := generate_eq s
  rw [normalize_eq h] at hx
  suffices hg : ∀ (t : CSPTable Label) (ht : t.WellFormed),
      t=iterate n s → ∀ a, 1/(capLoss:ℝ)≤(t.csp ht).rejection a by
    exact hg (generate s) (generate_valid s) hx
  rintro t ht rfl
  simpa only [min_eq_right hh] using iterate_gap h _ hi n
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierCompiler

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
lemma amplified_sound (x : Word) (hx : ¬∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) :
    ∀ a, 1/(capLoss:ℝ)≤((amplified P p x).csp (amplified_valid P p x)).rejection a :=
  AmplifierProgram.generate_sound (initial_valid P p x) (mt (initial_correct_s53 P p x).mp hx)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Seed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace ProjectionSeed
open Amplifier

lemma gap_pos : 0<gap := by
  unfold gap
  have hc : (0:ℝ) < capLoss := Nat.cast_pos.mpr capLoss_pos
  have hg : (0:ℝ)<ExpanderFamily.growth := Nat.cast_pos.mpr (by have := ExpanderFamily.growth_gt_one; omega)
  positivity
lemma contraction_lt_one : contraction<1 := by
  change max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)<1
  apply max_lt
  · have h : (0:ℝ)<((gap/2)/4)^2 := sq_pos_of_pos (by have := gap_pos; positivity)
    nlinarith
  · norm_num

end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SemanticProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSemanticProjection

namespace MetricKMedian.PCP
open scoped Classical

namespace ProjectionSeed
open Amplifier

lemma repetition_exists (ε : ℝ) (hε : 0<ε) : ∃ n : ℕ, contraction^n≤ε^2 := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sq_pos_of_pos hε) contraction_lt_one
  exact ⟨n,hn.le⟩
end ProjectionSeed

open Complexity

end MetricKMedian.PCP

end Inline_PCPSemanticProjection

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_UniformProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUniformProjection
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_4_rbdc27d_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_4_rbdc27d_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_4_rbdc27d_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM_2_rbdc27d_1 : DecidableEq (Query P.tm.m) := Classical.decEq _
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instNonemptyFinLengthCSPRowLabelSndListUnitAmplified
lemma projection_poly (n : ℕ) : FinitePolyTime id Coverage.ProjectionInput.encode (projection P p n) :=
  ⟨(projectionProgram P p n).stock,(projectionProgram P p n).finite_work⟩
lemma projection_sound (n : ℕ) (x : Word)
    (hx : ¬∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true)
    (ε : ℝ) (hε : 0≤ε) (hn : ProjectionSeed.contraction^n≤ε^2) : (projection P p n x).Sound ε :=
  SeedProgram.output_sound_s53 _ _ n (amplified_sound P p x hx) ε hε hn
end MetricKMedian.PCP.Compiler.CookProgram
namespace MetricKMedian.Coverage
open Complexity PCP PCP.Compiler
open scoped Classical

theorem projection_gap_np_reductions_s53_oai : ProjectionGapNPReductions := by
  intro ε hε L hL
  obtain ⟨verify,p,⟨P,hfinite⟩,hverify⟩ := hL
  let (k : P.tm.K) : Finite (P.tm.Γ k) := hfinite k
  let (k : P.tm.K) : Fintype (P.tm.Γ k) := Fintype.ofFinite _
  have he : (0:ℝ)<(ε:ℝ) := Rat.cast_pos.mpr hε
  obtain ⟨n,hn⟩ := ProjectionSeed.repetition_exists (ε:ℝ) he
  refine ⟨SeedProgram.Width n,SeedProgram.LeftSize n,SeedProgram.RightSize n,
    CookProgram.projection P p n,CookProgram.projection_poly P p n,?_,?_⟩
  · intro x hx
    exact CookProgram.projection_complete_s53 P p n x ((hverify x).mp hx)
  · intro x hx
    apply CookProgram.projection_sound P p n x _ (ε:ℝ) he.le hn
    intro hc
    exact hx ((hverify x).mpr hc)
end MetricKMedian.Coverage

end Inline_PCPUniformProjection

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53_oai := @OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53_oai
