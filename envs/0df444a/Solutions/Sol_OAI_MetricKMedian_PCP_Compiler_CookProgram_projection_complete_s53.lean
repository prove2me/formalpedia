-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:47:15.66118+00:00
-- url     : https://prove2.me/submissions/45e48c13-b34d-48e1-a058-db87e8693d23

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K084
import Theorems.Thm_OAI_MetricKMedian_PCP_AlphabetReduction_padded_complete_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_CookProgram_initial_correct_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringObjects
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D A : Type} {cap : ℕ} (G : PortGraph V D) [Inhabited A]

theorem honest_opinion (x : V → A) (n : ℕ) (hn : n ≤ cap) (v : V) (c : Fin n → D) :
    G.opinion (G.honest x : V → Advice D A cap) n v c = x v := by
  unfold opinion
  rw [Advice.get_le _ _ _ hn]
  change x (G.trace n ((Walk.ofWord (G := G) v c).vertex (Fin.last n))
    (Walk.ofWord (G := G) v c).reverse.port (Fin.last n)) = x v
  have hp := Walk.vertex_eq_trace (Walk.ofWord (G := G) v c).reverse
  have hs : (Walk.ofWord (G := G) v c).reverse.vertex 0 =
      (Walk.ofWord (G := G) v c).vertex (Fin.last n) := Walk.reverse_start _
  rw [← hs, ← hp, Walk.reverse_end]
  simp [Walk.ofWord]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPPoweringObjects

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

omit [Fintype E] [DecidableEq A] [DecidableEq B] in
lemma mapLabels_complete (a : V → A) (ha : C.Satisfies a) :
    (C.mapLabels e).Satisfies (e ∘ a) := by
  intro t
  apply (mapLabels_allowed C e t _ _).mpr
  simpa only [Function.comp_def,Equiv.symm_apply_apply,mapLabels] using ha t

end BinaryCSP

end MetricKMedian.PCP

end Inline_PCPLabelTransport

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PoweringConstruction
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPoweringConstruction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D}
lemma center_left_far (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (ofWord (G := G) (centerEquiv i j p).1.1 (centerEquiv i j p).1.2).vertex (Fin.last i) =
      p.vertex 0 := by
  simpa only [Equiv.symm_apply_apply] using (center_left_end (G := G) i j (centerEquiv i j p)).symm
lemma center_right_far (i j : ℕ) (p : G.Walk (i+(j+1))) :
    (ofWord (G := G) (G.step (centerEquiv i j p).1.1 (centerEquiv i j p).2.1)
      (centerEquiv i j p).2.2).vertex (Fin.last j) = p.vertex (Fin.last (i+(j+1))) := by
  simpa only [Equiv.symm_apply_apply] using (center_right_end (G := G) i j (centerEquiv i j p)).symm
end PortGraph.Walk

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}
open PortGraph

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma cutAccept_iff (a : V → Advice D A cap) (i j : ℕ) (p : G.Walk (i+(j+1))) :
    C.CutAccept i j p (a (p.vertex 0)) (a (p.vertex (Fin.last (i+(j+1))))) ↔
      (G.opinion a i (Walk.centerEquiv i j p).1.1 (Walk.centerEquiv i j p).1.2,
       G.opinion a j (G.step (Walk.centerEquiv i j p).1.1 (Walk.centerEquiv i j p).2.1)
          (Walk.centerEquiv i j p).2.2) ∈
        C.allowed ((Walk.centerEquiv i j p).1.1,(Walk.centerEquiv i j p).2.1) := by
  unfold CutAccept opinion
  rw [Walk.center_left_far,Walk.center_right_far]

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] [DecidableEq A] in
lemma honest_cut (x : V → A) (hx : C.Satisfies x) (i j : ℕ) (hi : i ≤ cap) (hj : j ≤ cap)
    (p : G.Walk (i+(j+1))) :
    C.CutAccept i j p ((G.honest x : V → Advice D A cap) (p.vertex 0))
      ((G.honest x : V → Advice D A cap) (p.vertex (Fin.last (i+(j+1))))) := by
  rw [cutAccept_iff, G.honest_opinion x i hi, G.honest_opinion x j hj]
  exact hx _ _

omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq A] in
theorem powered_complete (x : V → A) (hx : C.Satisfies x) (t : ℕ) :
    (C.powered (cap := cap) t).Satisfies (G.honest x) := by
  intro z
  rw [powered_allowed]
  intro i j h
  have hi : i.val ≤ cap := by omega
  have hj : j.val ≤ cap := by omega
  have hh := C.honest_cut x hx i.val j.val hi hj ((stoppedPath t z).cast h)
  simpa only [powered,Walk.cast_start,Walk.cast_end] using hh

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringConstruction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphExtend
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphExtend

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
  [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

omit [DecidableEq A] in
lemma extend_complete [Inhabited A] (a : V → A) (ha : C.Satisfies a) :
    ∃ b, (C.extend e).Satisfies b := by
  let b : W → A := fun w => if h : w ∈ Set.range e then a (e.toEquivRange.symm ⟨w,h⟩) else default
  have hb (v : V) : b (e v)=a v := by simp [b]
  refine ⟨b,?_⟩
  intro w d
  by_cases h : w ∈ Set.range e
  · obtain ⟨v,rfl⟩ := h
    change _ ∈ C.extendedAllowed e (e v,d)
    rw [G.extend_step_image,C.extendedAllowed_image e (v,d),hb,hb]
    exact ha v d
  · change _ ∈ C.extendedAllowed e (w,d)
    rw [C.extendedAllowed_outside e (w,d) h]
    exact mem_univ _

end PortCSP
end MetricKMedian.PCP

end Inline_PCPGraphExtend

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_CSPMix
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
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

omit [Fintype A] [DecidableEq A] in
lemma blend_complete (a : V → A) (hc : C.Satisfies a) (hk : K.Satisfies a) :
    (C.blend K).Satisfies a := by
  rintro v ⟨i,d,s⟩
  have hh : ¬ (C.blend K).Bad a (v,i,d,s) := by
    rw [blend_bad]
    by_cases hi : i=0
    · simpa only [hi,ite_true,Bad,not_not] using hc v d
    · simpa only [hi,ite_false,Bad,not_not] using hk v s
  exact not_not.mp hh

end PortCSP

end MetricKMedian.PCP

end Inline_PCPCSPMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularizationObjects
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.FlexibleCloud.honest_dart _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularizationObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
variable (C : BinaryCSP V E A)

lemma equality_complete (x : V → A) : (equalityCSP C).Satisfies (honest C x) := by
  rintro ⟨v,w⟩ d
  simp [equalityCSP,honest,equality_step]

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleCloud
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed_index _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true
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

omit [Fintype V] in
lemma matching_complete (x : V → A) (hx : C.Satisfies x) :
    (matchingCSP C embed).Satisfies (honest C x) := by
  intro n d
  by_cases hn : n ∈ Set.range (dartEmbed C embed)
  · obtain ⟨⟨e,b⟩,rfl⟩ := hn
    change _ ∈ (dartCSP C).extendedAllowed (dartEmbed C embed) (dartEmbed C embed (e,b),d)
    rw [PortCSP.extendedAllowed_image (dartCSP C) (dartEmbed C embed) ((e,b),d)]
    change (honest C x (dartEmbed C embed (e,b)),
      honest C x (((dartGraph (E := E)).extend (dartEmbed C embed)).step (dartEmbed C embed (e,b)) d)) ∈ _
    rw [PortGraph.extend_step_image]
    cases b <;> simpa [dartCSP,dartGraph,PortGraph.step,dartFlip,endpoint] using hx e
  · change _ ∈ (dartCSP C).extendedAllowed (dartEmbed C embed) (n,d)
    rw [PortCSP.extendedAllowed_outside _ _ (n,d) hn]
    exact mem_univ _

omit [Fintype V] in
lemma regular_complete (x : V → A) (hx : C.Satisfies x) :
    (regularCSP C embed).Satisfies (honest C x) :=
  PortCSP.blend_complete _ _ _ (matching_complete C embed x hx) (equality_complete C x)

end FlexibleCloud
end MetricKMedian.PCP

end Inline_PCPFlexibleCloud

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

omit [Fintype V] [Nonempty E] in
theorem complete (x : V → A) (hx : C.Satisfies x) : ∃ a, (csp C cloudEmbed padEmbed).Satisfies a := by
  obtain ⟨a,ha⟩ := (FlexibleCloud.regularCSP C cloudEmbed).extend_complete padEmbed
    (CloudCopies.honest C x) (FlexibleCloud.regular_complete C cloudEmbed x hx)
  exact ⟨a,PortCSP.blend_complete _ _ a ha (PortCSP.always_complete _ a)⟩

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerCompleteness
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPowerCompleteness
namespace MetricKMedian.PCP
open scoped Classical

namespace PortCSP
variable {V D K : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
variable [Fintype K] [DecidableEq K] {G : PortGraph V D}
variable (C : PortCSP G (BitVector K)) (t cap : ℕ)
variable [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)]
omit [Fintype V] [Nonempty V] [Nonempty D]
  [Fintype (Advice.BitIndex D K cap)] [DecidableEq (Advice.BitIndex D K cap)] in
lemma powered_bits_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, ((C.powered (cap := cap) t).mapLabels (Advice.bitsEquiv D K cap)).Satisfies a := by
  exact ⟨_,(C.powered (cap := cap) t).mapLabels_complete (Advice.bitsEquiv D K cap)
    (G.honest x) (C.powered_complete (cap := cap) x hx t)⟩
end PortCSP
end MetricKMedian.PCP

end Inline_PCPPowerCompleteness

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleComplete
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleComplete
namespace MetricKMedian.PCP.FlexibleAmplifier
open Amplifier
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
omit [Fintype V] [Nonempty E] in
lemma bits_complete (x : V → Label) (hx : C.Satisfies x) :
    ∃ a, (bits C cloudEmbed padEmbed).Satisfies a := by
  obtain ⟨b,hb⟩ := FlexibleRegularization.complete C cloudEmbed padEmbed x hx
  exact (FlexibleRegularization.csp C cloudEmbed padEmbed).powered_bits_complete steps radius b hb
end MetricKMedian.PCP.FlexibleAmplifier

end Inline_PCPFlexibleComplete

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
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
lemma complete (hc : ∃ a, (s.csp h).Satisfies a) :
    ∃ a, ((next s).csp (next_wellFormed s h)).Satisfies a := by
  obtain ⟨a,ha⟩ := hc
  have hbb := FlexibleAmplifier.bits_complete (C s h)
    (CloudOrder.cloudEmbed (C s h) (EO s)) (padding s h) a ha
  obtain ⟨c,hc⟩ := (bitsRep s h).satisfies (bits_wellFormed s h) |>.mpr hbb
  obtain ⟨d,hd⟩ := AlphabetReduction.padded_complete_s53 ((bits s).csp (bits_wellFormed s h)) c hc
  exact (nextRep s h).satisfies (next_wellFormed s h) |>.mpr ⟨d,hd⟩
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierIteration
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
lemma iterate_complete {s : CSPTable Label} (h : s.WellFormed)
    (hc : ∃ a, (s.csp h).Satisfies a) (n : ℕ) :
    ∃ a, ((iterate n s).csp (iterate_valid h n)).Satisfies a := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    have hh := iterate_valid h n
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp hh.1
    exact complete (iterate n s) hh ih
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierIteration

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierCompiler
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic Polynomial
open scoped Classical

lemma generate_complete {s : CSPTable Label} (h : s.WellFormed)
    (hc : ∃ a, (s.csp h).Satisfies a) : ∃ a, ((generate s).csp (generate_valid s)).Satisfies a := by
  have he := generate_eq s
  rw [normalize_eq h] at he
  suffices hh : ∀ (t : CSPTable Label) (ht : t.WellFormed),
      t=iterate (Nat.log 2 s.2.length+1) s → ∃ a, (t.csp ht).Satisfies a by
    exact hh (generate s) (generate_valid s) he
  rintro t ht rfl
  exact iterate_complete h hc _
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookAmplify
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
lemma amplified_complete (x : Word) (hx : ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) :
    ∃ a, ((amplified P p x).csp (amplified_valid P p x)).Satisfies a :=
  AmplifierProgram.generate_complete (initial_valid P p x) ((initial_correct_s53 P p x).mpr hx)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionInput

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {u v d s a b : ℕ}
variable (G : BiProjection (Fin u) (Fin v) (Fin d) (Fin s) (Fin a) (Fin b))

lemma input_perfect (hu : 0<u) (hv : 0<v) (hs : 0 < s) (ha : 0<a) (hb : 0<b)
    (hc : G.Consistent) (h : G.Perfect) : (G.input hu hv hs ha hb hc).Perfect := by
  obtain ⟨left,right,h⟩ := h
  refine ⟨left,right,?_⟩
  intro y i
  have hh := h (G.edge.symm (y,i)).1 (G.edge.symm (y,i)).2
  simpa only [Prod.eta,Equiv.apply_symm_apply,input,system] using hh

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionInput

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionReindex

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' : Type}
variable (G : BiProjection U V D S A B)
variable (eu : U ≃ U') (ev : V ≃ V') (ed : D ≃ D') (es : S ≃ S')
variable (ea : A ≃ A') (eb : B ≃ B')

lemma reindex_perfect (h : G.Perfect) : (G.reindex eu ev ed es ea eb).Perfect := by
  obtain ⟨a,b,h⟩ := h
  refine ⟨ea ∘ a ∘ eu.symm,eb ∘ b ∘ ev.symm,?_⟩
  intro u d
  simpa only [reindex,Function.comp_def,Equiv.symm_apply_apply,Equiv.trans_apply,
    Equiv.prodCongr_apply,Equiv.prodCongr_symm,Prod.map_apply,Prod.map] using congrArg eb (h (eu.symm u) (ed.symm d))
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionReindex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {nu : ℕ} (ue : U≃Fin nu) (vo : Ordered V) (so : Ordered S)
variable (ao : Ordered A) (bo : Ordered B)
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B] [Nonempty D] in
lemma input_perfect (hc : G.Consistent) (hy : G.Perfect) : (input G ue vo so ao bo hc).Perfect := by
  apply BiProjection.input_perfect
  exact G.reindex_perfect _ _ _ _ _ _ hy
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_CSPProjection
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPProjection

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D} [DecidableEq A]
variable (C : PortCSP G A)
variable (chosen : V × D → A × A) (hchosen : ∀ p, C.Legal p (chosen p))
omit [DecidableEq A]
lemma repair_fixed (p : V × D) (a : A × A) (h : C.Legal p a) : C.repair chosen p a=a := ite_eq_left h

lemma projection_complete (x : V → A) (hx : C.Satisfies x) : (C.projection chosen).Perfect := by
  refine ⟨fun p => (x p.1,x (G.rotate p).1),x,?_⟩
  intro p b
  have hl : C.Legal p (x p.1,x (G.rotate p).1) := ⟨hx p.1 p.2,by intro h; rw [h]⟩
  cases b <;> simp only [projection,PortGraph.incidence,PortGraph.incidenceEdge,
    Bool.false_eq_true,ite_false,ite_true,repair_fixed C chosen p _ hl] <;> rfl

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Promises
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Nested.inhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionPromises

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' : Type}
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')
lemma perfect_prod (hG : G.Perfect) (hH : H.Perfect) : (G.prod H).Perfect := by
  obtain ⟨a,b,hab⟩ := hG
  obtain ⟨a',b',hab'⟩ := hH
  refine ⟨fun p => (a p.1,a' p.2),fun p => (b p.1,b' p.2),?_⟩
  rintro ⟨u,u'⟩ ⟨d,d'⟩
  exact Prod.ext (hab u d) (hab' u' d')
lemma perfect_power (hG : G.Perfect) (n : ℕ) : (G.power n).Perfect := by
  induction n with
  | zero => exact ⟨fun _ => (),fun _ => (),fun _ _ => rfl⟩
  | succ n ih => exact G.perfect_prod (G.power n) hG ih
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionPromises

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

namespace BiProjection
variable (D S A B : Type) [Inhabited A] [Inhabited B]
lemma neutral_perfect : (neutral D S A B).Perfect :=
  ⟨fun _ => default,fun _ => default,fun _ _ => rfl⟩
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
lemma regular_complete (hc : ∃ a, (t.csp h).Satisfies a) :
    ∃ a, (CloudSpec.regularCSP t h).Satisfies a := by
  obtain ⟨a,ha⟩ := hc
  exact FlexibleRegularization.complete (CloudSpec.C t h) (cloudEmbed _ (CloudSpec.EO t)) (CloudSpec.padding t h) a ha
lemma allLegal_of_perfect (hc : ∃ a, (t.csp h).Satisfies a) : allLegal t=true := by
  obtain ⟨a,ha⟩ := regular_complete t h hc
  apply (allLegal_correct t h).mpr
  intro p
  apply Finset.nonempty_def.mpr
  refine ⟨(a p.1,a ((CloudSpec.regularGraph t h).rotate p).1),?_⟩
  apply (legal_correct t h p.1 p.2 _).mpr
  exact ⟨ha p.1 p.2,by intro he; rw [he]⟩
lemma good_perfect (hc : ∃ a, (t.csp h).Satisfies a) : (good t h).Perfect := by
  obtain ⟨a,ha⟩ := regular_complete t h hc
  exact BiProjection.perfect_prod _ _ ((CloudSpec.regularCSP t h).projection_complete _ a ha)
    (BiProjection.neutral_perfect _ _ _ _)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
lemma output_perfect (n : ℕ) (hc : ∃ a, (t.csp h).Satisfies a) : (output t h n).Perfect := by
  rw [output,dite_eq_left (allLegal_of_perfect t h hc)]
  apply input_perfect
  exact BiProjection.perfect_power _ (good_perfect t h hc) n
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

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
local instance instFintypeKTmBool_solutions_4_r658247_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_4_r658247_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_4_r658247_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM_2_r658247_1 : DecidableEq (Query P.tm.m) := Classical.decEq _
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instNonemptyFinLengthCSPRowLabelSndListUnitAmplified
lemma projection_complete_s53_oai (n : ℕ) (x : Word)
    (hx : ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) : (projection P p n x).Perfect :=
  SeedProgram.output_perfect _ _ n (amplified_complete P p x hx)
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPUniformProjection

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53_oai := @OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53_oai
