-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:40:41.9482+00:00
-- url     : https://prove2.me/submissions/a40d19c4-f5e4-4938-a2ae-1863de871336

import Mathlib
import Definitions.Def_OAIQ053K073
import Theorems.Thm_OAI_MetricKMedian_PCP_FlexibleCloud_regular_sound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
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

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_AlphabetReduction
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

end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_CSPMix
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Amplification_TestSum
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortCSP.always_failure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTestSum

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma testSum_card_rate {S : Type} [Fintype S] [Nonempty S] (p : S → Prop) :
    testSum p=Fintype.card S*testRate p := by
  unfold testSum testRate
  rw [Fintype.expect_eq_sum_div_card]
  have hn : (Fintype.card S:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

end MetricKMedian.PCP

end Inline_PCPTestSum

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddingSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.always_failure _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddingSound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma testSum_embedding {S T : Type} [Fintype S] [Fintype T] (e : S ↪ T)
    (p : S → Prop) (q : T → Prop) (hi : ∀ s, q (e s) ↔ p s)
    (ho : ∀ t, t ∉ Set.range e → ¬q t) : testSum q=testSum p := by
  calc
    testSum q = ∑ t ∈ univ.map e, if q t then (1:ℝ) else 0 := by
      symm
      apply sum_subset (subset_univ _)
      intro t _ ht
      have hn : t ∉ Set.range e := by
        rintro ⟨s,rfl⟩
        exact ht (mem_map.mpr ⟨s,mem_univ _,rfl⟩)
      exact ite_eq_right (ho t hn)
    _ = testSum p := by
      rw [sum_map]
      unfold testSum
      apply sum_congr rfl
      intro s _
      simp only [hi s]

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]
  [Fintype D] [Nonempty D] [DecidableEq W] [DecidableEq D] [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

omit [Nonempty V] [Fintype W] [Nonempty W] [Nonempty D] [DecidableEq A] in
lemma extend_bad_outside (a : W → A) (p : W × D) (hp : p.1 ∉ Set.range e) :
    ¬ (C.extend e).Bad a p := by
  change ¬ (_ ∉ C.extendedAllowed e p)
  rw [C.extendedAllowed_outside e p hp]
  simp

omit [DecidableEq A] in
lemma extend_failure_mass (a : W → A) :
    (Fintype.card W:ℝ)*testRate ((C.extend e).Bad a) =
      (Fintype.card V:ℝ)*testRate (C.Bad (a ∘ e)) := by
  have h := testSum_embedding (PortGraph.portEmbed e)
    (C.Bad (a ∘ e)) ((C.extend e).Bad a)
    (C.extend_bad_image e a)
    (fun p hp => C.extend_bad_outside e a p (fun hv => hp ((PortGraph.portEmbed_range e p).mpr hv)))
  rw [testSum_card_rate,testSum_card_rate,Fintype.card_prod,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul] at h
  have hd : (Fintype.card D:ℝ)≠0 := by positivity
  apply (mul_right_cancel₀ hd)
  nlinarith only [h]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPaddingSound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FlexibleRegularization
variable {V E A : Type} [Fintype V] [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

open GlobalRegularization

variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ Node C)

omit [Fintype V] in
theorem sound (a : Node C → A) : C.rejection (decoded C padEmbed a) ≤
    (18*(ExpanderFamily.growth:ℝ)^2)*testRate ((csp C cloudEmbed padEmbed).Bad a) := by
  have hr := FlexibleCloud.regular_sound_s53 C cloudEmbed (a ∘ padEmbed)
  have hp := (FlexibleCloud.regularCSP C cloudEmbed).extend_failure_mass padEmbed a
  have hm := PortCSP.blend_failure (padded C cloudEmbed padEmbed) (PortCSP.always (strong C)) a
  rw [PortCSP.always_failure, mul_zero,add_zero] at hm
  change testRate ((csp C cloudEmbed padEmbed).Bad a)=testRate ((padded C cloudEmbed padEmbed).Bad a)/3 at hm
  change (Fintype.card (Node C):ℝ)*testRate ((padded C cloudEmbed padEmbed).Bad a)=_ at hp
  have hs : (Fintype.card (Node C):ℝ) ≤
      (ExpanderFamily.growth:ℝ)*Fintype.card (CloudCopies.Node C) := by
    exact_mod_cast node_relative_upper C
  have hn := testRate_nonneg ((padded C cloudEmbed padEmbed).Bad a)
  have hv : 0 < (Fintype.card (CloudCopies.Node C):ℝ) := by positivity
  have hl : testRate ((FlexibleCloud.regularCSP C cloudEmbed).Bad (a ∘ padEmbed)) ≤
      (ExpanderFamily.growth:ℝ)*testRate ((padded C cloudEmbed padEmbed).Bad a) := by
    apply (mul_le_mul_iff_right₀ hv).mp
    nlinarith only [hp,mul_le_mul_of_nonneg_right hs hn]
  change C.rejection (CloudCopies.decoded C (a ∘ padEmbed)) ≤ _
  have hg : 0 ≤ (ExpanderFamily.growth:ℝ) := Nat.cast_nonneg _
  nlinarith only [hr,mul_le_mul_of_nonneg_left hl (mul_nonneg (by norm_num : (0:ℝ)≤6) hg),hm]

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedSound
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Amplifier ProjectionSeed CloudOrder
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
lemma rejection_s53_oai (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
    (a : GlobalRegularization.Node (CloudSpec.C t h)→Label) :
    gap≤testRate ((CloudSpec.regularCSP t h).Bad a) := by
  have h1 := hg (FlexibleRegularization.decoded (CloudSpec.C t h) (CloudSpec.padding t h) a)
  have h2 := FlexibleRegularization.sound (CloudSpec.C t h) (cloudEmbed _ (CloudSpec.EO t)) (CloudSpec.padding t h) a
  have hd : (0:ℝ)<18*(ExpanderFamily.growth:ℝ)^2 := by
    have hp : (0:ℝ)<ExpanderFamily.growth :=
      Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one ExpanderFamily.growth_gt_one)
    exact mul_pos (by norm_num) (sq_pos_of_pos hp)
  change (1/(capLoss:ℝ))/(18*(ExpanderFamily.growth:ℝ)^2)≤_
  apply (div_le_iff₀ hd).mpr
  rw [mul_comm]
  exact h1.trans h2
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53_oai := @OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53_oai
