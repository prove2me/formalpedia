-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:26:20.57798+00:00
-- url     : https://prove2.me/submissions/860003e4-2f53-44b2-82f6-6e676916c229

import Mathlib
import Definitions.Def_OAIQ053K043

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
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

end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Operator
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

omit [Fintype A] [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma source_expect (f : U × D → ℝ) :
    (𝔼 v, 𝔼 s, f (G.source v s))=𝔼 u, 𝔼 d, f (u,d) := by
  rw [← expect_prod (fun p : V × S => f (G.source p.1 p.2)),← expect_prod f]
  exact Fintype.expect_equiv G.edge.symm _ _ (fun _ => rfl)

omit [Fintype A] [Fintype B] [Nonempty U] [Nonempty V] [Nonempty S] in
lemma average_mean (f : U → ℝ) : (𝔼 v, G.average f v)=𝔼 u, f u := by
  unfold average
  rw [G.source_expect (fun p : U × D => f p.1)]
  simp only [Fintype.expect_const]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_IncidenceOperator
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPIncidenceOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma expect_bool (f : Bool → ℝ) : (𝔼 b, f b)=(f false+f true)/2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Fintype.sum_bool,Fintype.card_bool,Nat.cast_ofNat]
  ring

namespace PortGraph
variable {V D A B : Type} (G : PortGraph V D)

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma incidence_average (π : (V × D) × Bool → A → B) (h : V × D → ℝ) :
    (G.incidence π).average h=G.down h := by
  funext v
  unfold BiProjection.average down
  rw [expect_prod]
  apply expect_congr rfl
  intro d _
  rw [expect_bool]
  rfl

omit [Nonempty V] [Nonempty D] in
lemma down_mean (h : V × D → ℝ) : (𝔼 v, G.down h v)=𝔼 p, h p := by
  have he := (G.incidence (fun (_ : (V × D) × Bool) (_ : Unit) => ())).average_mean h
  rwa [G.incidence_average] at he

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma down_sub (h k : V × D → ℝ) : G.down (fun p => h p-k p)=fun v => G.down h v-G.down k v := by
  funext v
  unfold down
  rw [← expect_sub_distrib]
  apply expect_congr rfl
  intro d _
  ring
omit [Fintype V] [Nonempty V] in
lemma down_const (c : ℝ) : G.down (fun _ => c)=fun _ => c := by
  funext v
  simp only [down,show (c+c)/2=c by ring,Fintype.expect_const]

omit [Nonempty V] [Nonempty D] in
lemma down_up_adjoint (f : V × D → ℝ) (g : V → ℝ) :
    pairing (G.down f) g=pairing f (G.up g) := by
  have hr := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.rotate p)*g p.1)
    (fun p : V × D => f p*g (G.rotate p).1)
    (by intro p; rw [G.involutive])
  unfold pairing down up
  simp only [expect_mul]
  rw [← expect_prod (fun p : V × D => ((f p+f (G.rotate p))/2)*g p.1)]
  have he (p : V × D) : ((f p+f (G.rotate p))/2)*g p.1=
      (f p*g p.1+f (G.rotate p)*g p.1)/2 := by ring
  have hf (p : V × D) : f p*((g p.1+g (G.rotate p).1)/2)=
      (f p*g p.1+f p*g (G.rotate p).1)/2 := by ring
  simp_rw [he,hf]
  rw [← expect_div,← expect_div,expect_add_distrib,expect_add_distrib,hr]

omit [Nonempty V] in
lemma up_energy (g : V → ℝ) :
    energy (G.up g)=(energy g+pairing g (G.adjacency g))/2 := by
  have hr : (𝔼 p : V × D, g (G.rotate p).1^2)=energy g := by
    rw [Fintype.expect_equiv G.rotate _ (fun p : V × D => g p.1^2) (fun _ => rfl),expect_prod]
    simp only [Fintype.expect_const,energy]
  have he (p : V × D) : ((g p.1+g (G.rotate p).1)/2)^2=
      (g p.1^2+g (G.rotate p).1^2+2*(g p.1*g (G.rotate p).1))/4 := by ring
  change (𝔼 p : V × D, ((g p.1+g (G.rotate p).1)/2)^2)=_
  simp_rw [he]
  rw [← expect_div,expect_add_distrib,expect_add_distrib,← mul_expect,hr]
  have hf : (𝔼 p : V × D, g p.1^2)=energy g := by
    rw [expect_prod]; simp only [Fintype.expect_const,energy]
  rw [hf]
  have hg : (𝔼 p : V × D, g p.1*g (G.rotate p).1)=pairing g (G.adjacency g) := by
    unfold pairing adjacency
    rw [expect_prod]
    simp_rw [mul_expect]
    rfl
  rw [hg]
  ring
end PortGraph
end MetricKMedian.PCP

end Inline_PCPIncidenceOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_IncidenceExpansion
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPIncidenceExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortGraph
variable {V D A B : Type} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
variable (G : PortGraph V D)

omit [Nonempty V] [Nonempty D] in
lemma half_pairing (hG : G.Contracts (1/2)) (g : V → ℝ) (hg : (𝔼 v, g v)=0) :
    pairing g (G.adjacency g) ≤ energy g/2 := by
  have hg0 := energy_nonneg g
  have h := (pairing_sq_le g (G.adjacency g)).trans
    (mul_le_mul_of_nonneg_left (hG g hg) hg0)
  nlinarith only [h,hg0]

omit [Nonempty V] in
lemma up_energy_centered (hG : G.Contracts (1/2)) (g : V → ℝ) (hg : (𝔼 v, g v)=0) :
    energy (G.up g) ≤ (3/4)*energy g := by
  rw [G.up_energy]
  linarith only [G.half_pairing hG g hg]

omit [Nonempty V] in
lemma down_energy_centered (hG : G.Contracts (1/2)) (f : V × D → ℝ)
    (hf : (𝔼 p, f p)=0) : energy (G.down f) ≤ (3/4)*energy f := by
  have hm : (𝔼 v, G.down f v)=0 := (G.down_mean f).trans hf
  have h := pairing_sq_le f (G.up (G.down f))
  rw [← G.down_up_adjoint] at h
  have he : pairing (G.down f) (G.down f)=energy (G.down f) := by
    simp only [pairing,energy,pow_two]
  rw [he] at h
  have hu := mul_le_mul_of_nonneg_left (G.up_energy_centered hG (G.down f) hm) (energy_nonneg f)
  have hd := energy_nonneg (G.down f)
  have hn := energy_nonneg f
  rcases eq_or_lt_of_le hd with hh|hh
  · rw [← hh]; positivity
  · nlinarith only [h,hu,hh]

lemma incidence_expands (hG : G.Contracts (1/2)) (π : (V × D) × Bool → A → B) :
    (G.incidence π).Expands (1/4) := by
  intro f
  rw [G.incidence_average]
  have h := G.down_energy_centered hG (fun p => f p-𝔼 q, f q) (mean_center f)
  rw [G.down_sub,G.down_const] at h
  have he : (fun v => G.down f v-𝔼 p, f p) =
      (fun v => G.down f v-𝔼 w, G.down f w) := by rw [G.down_mean]
  rw [he,energy_center,energy_center,G.down_mean] at h
  linarith only [h]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPIncidenceExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_CSPProjection
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

variable [Fintype V] [Fintype D] [Fintype A] [Nonempty V] [Nonempty D] [Nonempty A]
omit [Fintype A] [Nonempty A]

lemma projection_expands_s53_oai (hG : G.Contracts (1/2)) : (C.projection chosen).Expands (1/4) :=
  G.incidence_expands hG _
end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53_oai := @OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53_oai
