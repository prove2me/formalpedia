-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:25:34.803051+00:00
-- url     : https://prove2.me/submissions/afac4a0e-e4ba-46c8-b115-407d488bdef5

import Mathlib
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K042
import Theorems.Thm_OAI_MetricKMedian_PCP_GlobalRegularization_strong_contracts_s53

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

end FiniteEnergy

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

theorem adjacency_mean (f : V → ℝ) : (𝔼 v, G.adjacency f v) = 𝔼 v, f v := by
  change (𝔼 v, 𝔼 d, f (G.step v d)) = _
  rw [← expect_prod (fun p : V × D => f (G.step p.1 p.2))]
  have h := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.step p.1 p.2)) (fun p : V × D => f p.1)
    (fun _ => rfl)
  rw [h, expect_prod]
  simp only [Fintype.expect_const]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_L2
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPL2

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section
variable {S : Type} [Fintype S]

lemma l2_nonneg (f : S → ℝ) : 0 ≤ l2 f := Real.sqrt_nonneg _
lemma l2_sq (f : S → ℝ) : l2 f ^ 2=energy f := Real.sq_sqrt (energy_nonneg f)

lemma pairing_le_l2 (f g : S → ℝ) : pairing f g ≤ l2 f*l2 g := by
  have h := pairing_sq_le f g
  have hf := l2_sq f
  have hg := l2_sq g
  have hp := mul_nonneg (l2_nonneg f) (l2_nonneg g)
  rw [← hf,← hg,← mul_pow] at h
  nlinarith

lemma energy_add (f g : S → ℝ) :
    energy (fun x => f x+g x)=energy f+energy g+2*pairing f g := by
  unfold energy pairing
  have he (x : S) : (f x+g x)^2=f x^2+g x^2+2*(f x*g x) := by ring
  simp_rw [he]
  rw [expect_add_distrib,expect_add_distrib,← mul_expect]

lemma l2_add (f g : S → ℝ) : l2 (fun x => f x+g x) ≤ l2 f+l2 g := by
  have h := pairing_le_l2 f g
  have he := l2_sq (fun x => f x+g x)
  rw [energy_add,← l2_sq f,← l2_sq g] at he
  have hn := l2_nonneg (fun x => f x+g x)
  have hf := l2_nonneg f
  have hg := l2_nonneg g
  nlinarith

lemma l2_le_of_energy_le {a : ℝ} (ha : 0 ≤ a) (f g : S → ℝ)
    (h : energy f ≤ a^2*energy g) : l2 f ≤ a*l2 g := by
  rw [← l2_sq f,← l2_sq g,← mul_pow] at h
  have hp := mul_nonneg ha (l2_nonneg g)
  nlinarith [l2_nonneg f]

lemma mean_sq_le_energy [Nonempty S] (f : S → ℝ) : (𝔼 x, f x)^2 ≤ energy f := by
  have h := pairing_sq_le (fun _ : S => (1:ℝ)) f
  simpa [pairing,energy] using h

end

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D]
variable (G : PortGraph V D)

lemma energy_adjacency_le [Nonempty D] (f : V → ℝ) : energy (G.adjacency f) ≤ energy f := by
  unfold energy
  calc
    (𝔼 v, G.adjacency f v^2) ≤ 𝔼 v, 𝔼 d, f (G.step v d)^2 :=
      expect_le_expect (fun v _ => mean_sq_le_energy (fun d => f (G.step v d)))
    _ = _ := G.adjacency_mean (fun v => f v^2)

lemma l2_contracts {ρ : ℝ} (hρ : 0 ≤ ρ) (hG : G.Contracts ρ) (f : V → ℝ)
    (hf : (𝔼 v, f v)=0) : l2 (G.adjacency f) ≤ ρ*l2 f :=
  l2_le_of_energy_le hρ _ _ (hG f hf)

end PortGraph
end MetricKMedian.PCP

end Inline_PCPL2

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphMix
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma l2_scale {V : Type} [Fintype V] [Nonempty V] (f : V → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    l2 (fun v => c*f v)=c*l2 f := by
  have hh : energy (fun v => c*f v)=c^2*energy f := by
    unfold energy
    simp_rw [mul_pow]
    exact (mul_expect univ _ _).symm
  have h₁ := l2_sq (fun v => c*f v)
  have h₂ := l2_sq f
  have hn := l2_nonneg (fun v => c*f v)
  have hp := mul_nonneg hc (l2_nonneg f)
  rw [hh,← h₂,← mul_pow] at h₁
  nlinarith

namespace PortGraph
variable {V D S : Type}
variable (G : PortGraph V D) (H : PortGraph V S)

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype S] [Nonempty S]
omit [Fintype V] [Nonempty V] in
lemma blend_adjacency (f : V → ℝ) :
    (G.blend H).adjacency f = fun v => (G.adjacency f v+2*H.adjacency f v)/3 := by
  funext v
  unfold adjacency
  rw [expect_prod]
  simp_rw [expect_prod,blend_step]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_fin,Nat.cast_ofNat,Fin.sum_univ_succ]
  simp only [Fin.isValue,ite_true,Fin.succ_zero_eq_one,Fin.reduceEq,
    ite_false,Fintype.expect_const,Finset.sum_empty,Finset.univ_eq_empty,add_zero,Fin.succ_ne_zero]
  ring

theorem blend_contracts {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hG : G.Contracts ρ) (hH : H.Contracts σ) :
    (G.blend H).Contracts ((ρ+2*σ)/3) := by
  intro f hf
  have hg := G.l2_contracts hρ hG f hf
  have hh := H.l2_contracts hσ hH f hf
  have hs := l2_add (G.adjacency f) (fun v => 2*H.adjacency f v)
  rw [l2_scale _ 2 (by norm_num)] at hs
  have he : l2 ((G.blend H).adjacency f) =
      (1/3)*l2 (fun v => G.adjacency f v+2*H.adjacency f v) := by
    rw [blend_adjacency]
    have hr : (fun v => (G.adjacency f v+2*H.adjacency f v)/3)=
        (fun v => (1/3)*(G.adjacency f v+2*H.adjacency f v)) := by funext v; ring
    rw [hr,l2_scale _ (1/3) (by norm_num)]
  have hl : l2 ((G.blend H).adjacency f) ≤ ((ρ+2*σ)/3)*l2 f := by
    rw [he]
    calc
      _ ≤ (1/3)*(l2 (G.adjacency f)+2*l2 (H.adjacency f)) := by linarith
      _ ≤ (1/3)*(ρ*l2 f+2*(σ*l2 f)) := by linarith
      _ = _ := by ring
  have hp : 0 ≤ ((ρ+2*σ)/3)*l2 f := mul_nonneg (by positivity) (l2_nonneg f)
  have hq : 0 ≤ l2 ((G.blend H).adjacency f) := l2_nonneg _
  have hsq := sq_le_sq₀ hq hp
  rw [← l2_sq,← l2_sq,← mul_pow]
  exact hsq.mpr hl

omit [Nonempty V] in
lemma contracts_one : G.Contracts 1 := by
  intro f _
  simpa using G.energy_adjacency_le f

lemma blend_half (hH : H.Contracts (1/16)) : (G.blend H).Contracts (1/2) := by
  have hh := G.blend_contracts H (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1/16)
    G.contracts_one hH
  intro f hf
  have h := hh f hf
  have hn := energy_nonneg f
  norm_num at h ⊢
  nlinarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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

omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
theorem contracts_s53_oai : (graph C cloudEmbed padEmbed).Contracts (1/2) :=
  PortGraph.blend_half _ _ (strong_contracts_s53 C)

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53_oai := @OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53_oai
