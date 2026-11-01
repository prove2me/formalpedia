-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:24:21.289358+00:00
-- url     : https://prove2.me/submissions/b6abcbc3-e353-4511-9b07-51627b285809

import Mathlib
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K042
import Theorems.Thm_OAI_MetricKMedian_PCP_ExpanderFamily_graph_contracts_s53

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem testRate_prod (p : S → T → Prop) :
    testRate (fun z : S × T => p z.1 z.2) = 𝔼 s, testRate (p s) := by
  classical
  unfold testRate
  rw [← univ_product_univ, expect_product]

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section FiniteEnergy
variable {S T : Type} [Fintype S] [Fintype T]

theorem energy_nonneg (f : S → ℝ) : 0 ≤ energy f :=
  expect_nonneg (fun _ _ => sq_nonneg _)

theorem pairing_sq_le (f g : S → ℝ) : pairing f g ^ 2 ≤ energy f * energy g :=
  expect_mul_sq_le_sq_mul_sq _ _ _

theorem energy_center [Nonempty S] (f : S → ℝ) :
    energy (fun s => f s - 𝔼 t, f t) = energy f - (𝔼 t, f t)^2 := by
  unfold energy
  simp_rw [sub_sq]
  rw [expect_add_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const]
  ring

theorem mean_center [Nonempty S] (f : S → ℝ) :
    (𝔼 s, (f s - 𝔼 t, f t)) = 0 := by
  rw [expect_sub_distrib, Fintype.expect_const, sub_self]

end FiniteEnergy

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

omit [Fintype V] in
theorem adjacency_const (a : ℝ) : G.adjacency (fun _ => a) = fun _ => a := by
  funext v
  exact Fintype.expect_const a

omit [Fintype V] [Nonempty D] in
theorem adjacency_sub (f g : V → ℝ) :
    G.adjacency (fun v => f v - g v) = fun v => G.adjacency f v - G.adjacency g v := by
  funext v
  exact expect_sub_distrib _ _ _

theorem adjacency_mean (f : V → ℝ) : (𝔼 v, G.adjacency f v) = 𝔼 v, f v := by
  change (𝔼 v, 𝔼 d, f (G.step v d)) = _
  rw [← expect_prod (fun p : V × D => f (G.step p.1 p.2))]
  have h := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.step p.1 p.2)) (fun p : V × D => f p.1)
    (fun _ => rfl)
  rw [h, expect_prod]
  simp only [Fintype.expect_const]

theorem propagate_mean (n : ℕ) (f : V → ℝ) :
    (𝔼 v, G.propagate n f v) = 𝔼 v, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, adjacency_mean, ih]

omit [Fintype V] in
theorem propagate_const (n : ℕ) (a : ℝ) : G.propagate n (fun _ => a) = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, ih, adjacency_const]

omit [Fintype V] [Nonempty D] in
theorem propagate_sub (n : ℕ) (f g : V → ℝ) :
    G.propagate n (fun v => f v - g v) = fun v => G.propagate n f v - G.propagate n g v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, ih, adjacency_sub]; rfl

theorem centered_correlation [Nonempty V] (n : ℕ) (f : V → ℝ) :
    pairing (fun v => f v - 𝔼 w, f w) (G.propagate n (fun v => f v - 𝔼 w, f w)) =
      pairing f (G.propagate n f) - (𝔼 v, f v)^2 := by
  rw [G.propagate_sub, G.propagate_const]
  unfold pairing
  have h : ∀ v, (f v - 𝔼 w, f w) * (G.propagate n f v - 𝔼 w, f w) =
      f v * G.propagate n f v - (𝔼 w, f w) * G.propagate n f v -
      f v * (𝔼 w, f w) + (𝔼 w, f w)^2 := by intro v; ring
  simp_rw [h]
  rw [expect_add_distrib, expect_sub_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const, propagate_mean]
  ring

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_CSPMix
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
variable {V D S A : Type} [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} {H : PortGraph V S}
variable (C : PortCSP G A) (K : PortCSP H A)

variable [Fintype V] [Fintype D] [Nonempty D] [Fintype S] [Nonempty S]

omit [Fintype A] [DecidableEq A] in
lemma blend_failure (a : V → A) : testRate ((C.blend K).Bad a) =
    (testRate (C.Bad a)+2*testRate (K.Bad a))/3 := by
  have hp := testRate_congr (fun p : V × PortGraph.BlendPort (D := D) (S := S) =>
    C.blend_bad K a p.1 p.2.1 p.2.2.1 p.2.2.2)
  rw [hp]
  unfold testRate
  rw [expect_prod]
  simp_rw [expect_prod]
  have hv (v : V) :
      (𝔼 i : Fin 3, 𝔼 d : D, 𝔼 s : S,
        if (if i=0 then C.Bad a (v,d) else K.Bad a (v,s)) then (1:ℝ) else 0) =
      ((𝔼 d : D, if C.Bad a (v,d) then (1:ℝ) else 0)+
        2*(𝔼 s : S, if K.Bad a (v,s) then (1:ℝ) else 0))/3 := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Fintype.card_fin,Nat.cast_ofNat,Fin.sum_univ_succ,Fin.isValue,ite_true,
      Fin.succ_ne_zero,ite_false,Fintype.expect_const,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    ring
  simp_rw [hv]
  rw [← expect_div,expect_add_distrib,← mul_expect]
  congr 2
  · apply expect_congr rfl
    intro v _
    apply expect_congr rfl
    intro d _
    split_ifs <;> rfl
  · congr 1
    apply expect_congr rfl
    intro v _
    apply expect_congr rfl
    intro d _
    split_ifs <;> rfl

end PortCSP

end MetricKMedian.PCP

end Inline_PCPCSPMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_EqualityExpansion
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPEqualityExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

lemma correlation_half (hG : G.Contracts (1/2)) (f : V → ℝ) :
    pairing f (G.adjacency f) ≤ (energy f + (𝔼 v, f v)^2)/2 := by
  let g : V → ℝ := fun v => f v - 𝔼 w, f w
  have hg : (𝔼 v, g v)=0 := mean_center f
  have he := energy_nonneg g
  have h₁ := pairing_sq_le g (G.adjacency g)
  have h₂ := hG g hg
  have h₃ := mul_le_mul_of_nonneg_left h₂ he
  have h₄ : pairing g (G.adjacency g) ≤ energy g/2 := by
    nlinarith
  have hc := G.centered_correlation 1 f
  change pairing g (G.adjacency g) = pairing f (G.adjacency f) - (𝔼 v, f v)^2 at hc
  have hv := energy_center f
  change energy g = _ at hv
  linarith

variable [Fintype A] [Nonempty A] (a : V → A)

omit [Nonempty A] in
lemma labelMass_sum : ∑ b : A, labelMass a b = 1 := by
  classical
  unfold labelMass testRate
  rw [← expect_sum_comm]
  simp [eq_comm]

omit [Nonempty V] [Fintype A] [Nonempty A] in
lemma labelMass_nonneg (b : A) : 0 ≤ labelMass a b := testRate_nonneg _

omit [Nonempty V] in
lemma majorityLabel_max (b : A) : labelMass a b ≤ labelMass a (majorityLabel a) :=
  Classical.choose_spec (show ∃ b : A, ∀ c : A, labelMass a c ≤ labelMass a b from by
    obtain ⟨b,_,hb⟩ := exists_max_image univ (labelMass a) univ_nonempty
    exact ⟨b,fun c => hb c (mem_univ c)⟩) b

lemma label_collision_le_majority : ∑ b : A, (labelMass a b)^2 ≤ labelMass a (majorityLabel a) := by
  calc
    _ ≤ ∑ b : A, labelMass a b * labelMass a (majorityLabel a) :=
      sum_le_sum (fun b _ => by simpa [pow_two] using
        mul_le_mul_of_nonneg_left (majorityLabel_max a b) (labelMass_nonneg a b))
    _ = _ := by rw [← sum_mul,labelMass_sum,one_mul]

omit [Nonempty A] in
lemma label_pairing_sum :
    (∑ b : A, pairing (fun v => if a v=b then (1:ℝ) else 0)
      (G.adjacency (fun v => if a v=b then (1:ℝ) else 0))) =
      1 - G.equalityFailure a := by
  classical
  unfold pairing adjacency equalityFailure testRate
  simp_rw [mul_expect]
  rw [← expect_sum_comm]

  have hh : (𝔼 v, ∑ b : A, 𝔼 d, (if a v=b then (1:ℝ) else 0) *
      (if a (G.step v d)=b then (1:ℝ) else 0)) =
      𝔼 v, 𝔼 d, if a v=a (G.step v d) then (1:ℝ) else 0 := by
    apply expect_congr rfl
    intro v _
    rw [← expect_sum_comm]
    apply expect_congr rfl
    intro d _
    simp [eq_comm]
  rw [hh]
  rw [expect_prod]
  have hc := testRate_complement (fun z : V × D => a z.1=a (G.step z.1 z.2))
  rw [testRate_prod (fun v d => a v=a (G.step v d)),
    testRate_prod (fun v d => ¬a v=a (G.step v d))] at hc
  unfold testRate at hc
  linarith

theorem equality_cloud_sound (hG : G.Contracts (1/2)) :
    testRate (fun v => a v ≠ majorityLabel a) ≤ 2*G.equalityFailure a := by
  classical
  have hh := sum_le_sum (s := (univ : Finset A)) (fun b _ =>
    G.correlation_half hG (fun v => if a v=b then (1:ℝ) else 0))
  have he (b : A) : energy (fun v => if a v=b then (1:ℝ) else 0)=labelMass a b := by
    unfold energy labelMass testRate
    apply expect_congr rfl
    intro v _
    split_ifs <;> simp_all
  have hm (b : A) : (𝔼 v, if a v=b then (1:ℝ) else 0)=labelMass a b := by
    unfold labelMass testRate
    apply expect_congr rfl
    intro v _
    by_cases h : a v=b <;> simp [h]
  simp_rw [he,hm] at hh
  rw [label_pairing_sum, ← sum_div, sum_add_distrib,labelMass_sum] at hh
  have hc := label_collision_le_majority a
  have hn := testRate_complement (fun v => a v=majorityLabel a)
  change labelMass a (majorityLabel a) + testRate (fun v => a v ≠ majorityLabel a)=1 at hn
  linarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPEqualityExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudCopies
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.CloudCopies.honest_dart _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.FlexibleCloud.honest_dart _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudCopies

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)

variable [Fintype A] [Inhabited A] [DecidableEq A]

omit [Fintype V] [DecidableEq A] in
lemma decoded_active (a : Node C → A) (v : Active C) :
    decoded C a v.val=PortGraph.majorityLabel (fun w : Copy C v => a ⟨v,w⟩) := by
  simp [decoded,v.property]

omit [Fintype V] [DecidableEq A] in
theorem cloud_sound (a : Node C → A) (v : Active C) :
    testRate (fun w : Copy C v => a ⟨v,w⟩ ≠ decoded C a v.val) ≤
      2*(ExpanderFamily.graph (depth C v)).equalityFailure (fun w => a ⟨v,w⟩) := by
  rw [decoded_active]
  exact PortGraph.equality_cloud_sound _ (fun w => a ⟨v,w⟩) (ExpanderFamily.graph_contracts_s53 _)

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPCloudCopies

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_TestSum
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTestSum

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma testSum_mono {S : Type} [Fintype S] {p q : S → Prop} (h : ∀ s, p s → q s) :
    testSum p≤testSum q := by
  unfold testSum
  apply sum_le_sum
  intro s _
  by_cases hp : p s
  · simp [hp,h s hp]
  · simp only [ite_eq_right hp]; split_ifs <;> norm_num

lemma testSum_card_rate {S : Type} [Fintype S] [Nonempty S] (p : S → Prop) :
    testSum p=Fintype.card S*testRate p := by
  unfold testSum testRate
  rw [Fintype.expect_eq_sum_div_card]
  have hn : (Fintype.card S:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

lemma testSum_injection {S T : Type} [Fintype S] [Fintype T] (e : S ↪ T)
    {p : S → Prop} {q : T → Prop} (h : ∀ s, p s → q (e s)) : testSum p≤testSum q := by
  calc
    testSum p ≤ testSum (fun s => q (e s)) := testSum_mono h
    _ = ∑ t ∈ univ.map e, if q t then (1:ℝ) else 0 := by
      unfold testSum
      rw [sum_map]
    _ ≤ testSum q := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro t _ _
      split_ifs <;> norm_num

lemma testSum_sigma {S : Type} {T : S → Type} [Fintype S] [∀ s,Fintype (T s)]
    (p : ((s : S) × T s) → Prop) : testSum p=∑ s, testSum (fun t => p ⟨s,t⟩) := by
  exact Fintype.sum_sigma _

end MetricKMedian.PCP

end Inline_PCPTestSum

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularizationSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularizationSound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
  [Inhabited A] [Nonempty E]
variable (C : BinaryCSP V E A) (a : Node C → A)

omit [Nonempty E] in
lemma cloud_raw (v : Active C) :
    (Fintype.card ExpanderFamily.Degree : ℝ)*testSum (fun w : Copy C v => Disagrees C a ⟨v,w⟩) ≤
      2*testSum (fun p : Copy C v × ExpanderFamily.Degree =>
        (equalityCSP C).Bad a (⟨v,p.1⟩,p.2)) := by
  have h := cloud_sound C a v
  have he := testRate_congr (fun p : Copy C v × ExpanderFamily.Degree => equality_bad C a v p.1 p.2)
  rw [testSum_card_rate,testSum_card_rate,he]
  simp only [Fintype.card_prod,Nat.cast_mul]
  unfold PortGraph.equalityFailure at h
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤
    (Fintype.card ExpanderFamily.Degree:ℝ)*Fintype.card (Copy C v) by positivity)
  dsimp only [Disagrees]
  simp only [Fintype.card_prod,Nat.cast_mul] at hh
  nlinarith only [hh]

omit [Inhabited A] [Nonempty E] in
lemma equality_raw_partition :
    testSum ((equalityCSP C).Bad a) =
      ∑ v : Active C, testSum (fun p : Copy C v × ExpanderFamily.Degree =>
        (equalityCSP C).Bad a (⟨v,p.1⟩,p.2)) := by
  simp only [testSum,Fintype.sum_prod_type,Fintype.sum_sigma]

lemma total_disagreements :
    testSum (Disagrees C a) ≤
      2*(Fintype.card (Node C):ℝ)*testRate ((equalityCSP C).Bad a) := by
  have h := sum_le_sum (fun v (_ : v ∈ (univ : Finset (Active C))) => cloud_raw C a v)
  rw [← mul_sum,← mul_sum,← equality_raw_partition C a,← testSum_sigma] at h
  have he : testSum ((equalityCSP C).Bad a) =
      (Fintype.card (Node C):ℝ)*Fintype.card ExpanderFamily.Degree *
        testRate ((equalityCSP C).Bad a) := by
    rw [testSum_card_rate,Fintype.card_prod,Nat.cast_mul]
  rw [he] at h
  have hd : 0 < (Fintype.card ExpanderFamily.Degree:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hd).mp
  nlinarith only [h]

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationSound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleCloud
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleCloud

namespace MetricKMedian.PCP
open Finset CloudCopies
open scoped BigOperators Classical

namespace FlexibleCloud
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
variable (embed : ∀ v : Active C, Incident C v ↪ Copy C v)

variable [Fintype A] [DecidableEq A]

variable [Inhabited A] [Nonempty E] (a : Node C → A)

omit [Fintype V] [Nonempty E] in
lemma edge_bad_cases (e : E)
    (he : (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e) :
    (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),()) ∨
      Disagrees C a (dartEmbed C embed (e,false)) ∨ Disagrees C a (dartEmbed C embed (e,true)) := by
  by_contra h
  simp only [not_or] at h
  have hl : a (dartEmbed C embed (e,false))=decoded C a (C.left e) := by
    exact not_ne_iff.mp h.2.1
  have hr : a (dartEmbed C embed (e,true))=decoded C a (C.right e) := by
    exact not_ne_iff.mp h.2.2
  exact he (by
    have hh := h.1
    rw [matching_bad] at hh
    simpa only [not_not,hl,hr] using hh)

omit [Fintype V] [Nonempty E] in
lemma old_raw :
    testSum (fun e => (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e) ≤
      testSum (fun e => (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),())) +
        testSum (fun d : Dart (E := E) => Disagrees C a (dartEmbed C embed d)) := by
  unfold testSum
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro e _
  by_cases he : (decoded C a (C.left e),decoded C a (C.right e)) ∉ C.allowed e
  · obtain hm|hl|hr := edge_bad_cases C embed a e he
    · simp only [ite_eq_left he,ite_eq_left hm]; split_ifs <;> norm_num
    · simp only [ite_eq_left he,ite_eq_left hl]; split_ifs <;> norm_num
    · simp only [ite_eq_left he,ite_eq_left hr]; split_ifs <;> norm_num
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

omit [Fintype V] [Inhabited A] in
lemma matching_sum_bound :
    testSum (fun e => (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),())) ≤
      (Fintype.card (Node C):ℝ)*testRate ((matchingCSP C embed).Bad a) := by
  let e : E ↪ Node C × Unit :=
    { toFun e := (dartEmbed C embed (e,false),())
      inj' := by intro e f h; exact congrArg Prod.fst ((dartEmbed C embed).injective (congrArg Prod.fst h)) }
  have h := testSum_injection e (p := fun e => (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),()))
    (q := (matchingCSP C embed).Bad a) (fun _ h => h)
  simpa only [testSum_card_rate,Fintype.card_prod,Fintype.card_unit,mul_one] using h

omit [Fintype V] in
theorem regular_sound_s53_oai : C.rejection (decoded C a) ≤
    6*(ExpanderFamily.growth:ℝ)*testRate ((regularCSP C embed).Bad a) := by
  have hsum := old_raw C embed a
  have hmatch := matching_sum_bound C embed a
  have hmis := testSum_injection (dartEmbed C embed) (p := fun d => Disagrees C a (dartEmbed C embed d))
    (q := Disagrees C a) (fun _ h => h)
  have heq := total_disagreements C a
  have hblend := PortCSP.blend_failure (matchingCSP C embed) (equalityCSP C) a
  change testRate ((regularCSP C embed).Bad a)=_ at hblend
  rw [testSum_card_rate] at hsum
  change (Fintype.card E:ℝ)*C.rejection (decoded C a) ≤ _ at hsum
  have hraw : (Fintype.card E:ℝ)*C.rejection (decoded C a) ≤
      3*(Fintype.card (Node C):ℝ)*testRate ((regularCSP C embed).Bad a) := by
    nlinarith only [hsum,hmatch,hmis,heq,hblend]
  have hsize : (Fintype.card (Node C):ℝ) ≤
      2*(ExpanderFamily.growth:ℝ)*Fintype.card E := by
    exact_mod_cast node_card_upper C
  have hnon := testRate_nonneg ((regularCSP C embed).Bad a)
  have he : 0 < (Fintype.card E:ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ he).mp
  nlinarith only [hraw,mul_le_mul_of_nonneg_right hsize hnon]

end FlexibleCloud
end MetricKMedian.PCP

end Inline_PCPFlexibleCloud

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53_oai := @OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53_oai
