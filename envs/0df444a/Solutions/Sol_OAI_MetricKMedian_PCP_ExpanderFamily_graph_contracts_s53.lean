-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:17:17.421398+00:00
-- url     : https://prove2.me/submissions/82898505-663e-4206-ae7d-1c70fc415a15

import Mathlib
import Definitions.Def_OAIQ053K023
import Definitions.Def_OAIQ053K024
import Definitions.Def_OAIQ053K026

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SpectralWalk
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step
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

end FiniteEnergy

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

omit [Fintype V] in
theorem adjacency_const (a : ℝ) : G.adjacency (fun _ => a) = fun _ => a := by
  funext v
  exact Fintype.expect_const a

theorem adjacency_mean (f : V → ℝ) : (𝔼 v, G.adjacency f v) = 𝔼 v, f v := by
  change (𝔼 v, 𝔼 d, f (G.step v d)) = _
  rw [← expect_prod (fun p : V × D => f (G.step p.1 p.2))]
  have h := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.step p.1 p.2)) (fun p : V × D => f p.1)
    (fun _ => rfl)
  rw [h, expect_prod]
  simp only [Fintype.expect_const]

omit [Nonempty D] in
theorem adjacency_selfAdjoint (f g : V → ℝ) :
    pairing f (G.adjacency g) = pairing (G.adjacency f) g := by
  unfold pairing adjacency
  simp_rw [mul_expect, expect_mul]
  rw [← expect_prod (fun p : V × D => f p.1 * g (G.step p.1 p.2)),
    ← expect_prod (fun p : V × D => f (G.step p.1 p.2) * g p.1)]
  apply Fintype.expect_equiv G.rotate
  intro p
  change f p.1 * g (G.step p.1 p.2) =
    f (G.step (G.step p.1 p.2) (G.back p.1 p.2)) * g (G.step p.1 p.2)
  rw [step_back]

theorem propagate_mean (n : ℕ) (f : V → ℝ) :
    (𝔼 v, G.propagate n f v) = 𝔼 v, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, adjacency_mean, ih]

theorem propagate_contract {ρ : ℝ} (hG : G.Contracts ρ) (n : ℕ)
    (f : V → ℝ) (hf : (𝔼 v, f v) = 0) :
    energy (G.propagate n f) ≤ ρ^(2*n) * energy f := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      energy (G.propagate (n+1) f) ≤ ρ^2 * energy (G.propagate n f) :=
        hG _ ((G.propagate_mean n f).trans hf)
      _ ≤ ρ^2 * (ρ^(2*n) * energy f) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ρ^(2*(n+1)) * energy f := by rw [show 2*(n+1)=2+2*n by omega, pow_add]; ring

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Walsh
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPWalsh

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
lemma sign_add (b c : Bit) : sign (b+c)=sign b*sign c := by
  rcases bit_cases b with rfl | rfl <;> rcases bit_cases c with rfl | rfl <;> simp [CharTwo.add_self_eq_zero, sign]

variable {I : Type} [Fintype I]
lemma character_comm (b x : BitVector I) : character b x=character x b := by
  unfold character dot
  simp_rw [mul_comm]
lemma character_add (b x y : BitVector I) : character b (x+y)=character b x*character b y := by
  unfold character
  rw [dot_add_right, sign_add]
lemma character_add_left (a b x : BitVector I) :
    character (a+b) x=character a x*character b x := by
  unfold character
  rw [dot_add_left,sign_add]

variable [DecidableEq I]

lemma orthogonal (a b : BitVector I) :
    (𝔼 x, character a x * character b x) = if a=b then 1 else 0 := by
  simp_rw [← character_add_left]
  rw [character_mean]
  congr 1
  rw [add_eq_zero_iff_eq_neg]
  have hb : -b=b := funext (fun i => CharTwo.neg_eq (b i))
  rw [hb]

lemma dual_orthogonal (x y : BitVector I) :
    (𝔼 b, character b x * character b y) = if x=y then 1 else 0 := by
  simp_rw [character_comm (x := x),character_comm (x := y)]
  exact orthogonal x y

lemma inversion (f : BitVector I → ℝ) (x : BitVector I) :
    (∑ b, coefficient f b * character b x) = f x := by
  classical
  unfold coefficient pairing
  simp_rw [expect_mul]
  rw [← expect_sum_comm]
  have he (y : BitVector I) :
      (∑ b, f y * character b y * character b x) =
        f y * ((Fintype.card (BitVector I):ℝ) * if y=x then 1 else 0) := by
    simp_rw [mul_assoc]
    rw [← mul_sum]
    congr 1
    have hh := dual_orthogonal y x
    rw [Fintype.expect_eq_sum_div_card] at hh
    have hn : (Fintype.card (BitVector I):ℝ) ≠ 0 := by positivity
    exact (div_eq_iff hn).mp hh |>.trans (mul_comm _ _)
  simp_rw [he]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [mul_ite,mul_one,mul_zero]
  rw [sum_ite_eq' univ x (fun y => f y * (Fintype.card (BitVector I):ℝ))]
  simp only [mem_univ,ite_true]
  have hn : (Fintype.card (BitVector I):ℝ) ≠ 0 := by positivity
  exact mul_div_cancel_right₀ _ hn

theorem parseval (f : BitVector I → ℝ) : energy f=∑ b, coefficient f b ^ 2 := by
  unfold energy
  calc
    (𝔼 x, f x^2) = 𝔼 x, f x * ∑ b, coefficient f b * character b x := by
      apply expect_congr rfl
      intro x _
      rw [inversion]
      ring
    _ = ∑ b, 𝔼 x, coefficient f b * (f x * character b x) := by
      simp_rw [mul_sum, show ∀ x b, f x*(coefficient f b*character b x)=
        coefficient f b*(f x*character b x) by intros; ring]
      rw [expect_sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro b _
      rw [← mul_expect]
      change coefficient f b*coefficient f b=coefficient f b^2
      ring

end Walsh
end MetricKMedian.PCP

end Inline_PCPWalsh

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Cayley
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCayley

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
variable {I D : Type} [Fintype I] [DecidableEq I]

variable [Fintype D] [Nonempty D]

omit [DecidableEq I] [Nonempty D] in
lemma adjacency_character (g : D → BitVector I) (b : BitVector I) :
    (cayley g).adjacency (character b) = fun v => character b v * bias g b := by
  funext v
  unfold PortGraph.adjacency
  simp_rw [cayley_step,character_add]
  rw [← mul_expect]
  rfl

omit [Nonempty D] in
lemma coefficient_adjacency (g : D → BitVector I) (f : BitVector I → ℝ) (b : BitVector I) :
    coefficient ((cayley g).adjacency f) b=coefficient f b*bias g b := by
  unfold coefficient
  rw [← PortGraph.adjacency_selfAdjoint,adjacency_character]
  unfold pairing
  simp_rw [← mul_assoc]
  rw [← expect_mul]

omit [Nonempty D] in
theorem cayley_contracts (g : D → BitVector I) (ρ : ℝ)
    (hbias : ∀ b, b≠0 → |bias g b| ≤ ρ) : (cayley g).Contracts ρ := by
  intro f hf
  rw [parseval,parseval,mul_sum]
  apply sum_le_sum
  intro b _
  rw [coefficient_adjacency]
  by_cases hb : b=0
  · subst b
    rw [coefficient_zero,hf]
    simp
  · have h := hbias b hb
    have hr : 0 ≤ ρ := (abs_nonneg _).trans h
    have hs : bias g b ^ 2 ≤ ρ^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (bias g b)) h 2
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (coefficient f b))]

end Walsh
end MetricKMedian.PCP

end Inline_PCPCayley

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphProducts
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphProducts

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type}

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma square_adjacency (G : PortGraph V D) (f : V → ℝ) :
    G.square.adjacency f=G.adjacency (G.adjacency f) := by
  funext v
  unfold adjacency
  simp_rw [square_step]
  exact expect_prod _

omit [Nonempty V] in
theorem square_contracts (G : PortGraph V D) {ρ : ℝ} (h : G.Contracts ρ) :
    G.square.Contracts (ρ^2) := by
  intro f hf
  rw [square_adjacency]
  have hh := G.propagate_contract h 2 f hf
  simpa only [propagate_succ,propagate_zero,show 2*2=4 by decide,← pow_mul] using hh

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

variable [Fintype S] [Nonempty S]

omit [Nonempty S] in
lemma zigzag_adjacency (G : PortGraph V D) (H : PortGraph D S) (f : V × D → ℝ) :
    (G.zigzag H).adjacency f=cloud H (permute G (cloud H f)) := by
  funext p
  unfold adjacency cloud permute
  simp_rw [zigzag_step]
  rw [expect_prod]
  rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphProducts

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_L2
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

lemma l2_mono (f g : S → ℝ) (h : energy f ≤ energy g) : l2 f ≤ l2 g :=
  Real.sqrt_le_sqrt h

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
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Cloud
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloud

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type} [Fintype V] [Fintype D] [Nonempty D]
  [Fintype S] [Nonempty S]

lemma lift_energy (f : V → ℝ) : energy (lift (D := D) f)=energy f := by
  unfold energy lift
  rw [expect_prod]
  simp only [Fintype.expect_const]

lemma lift_l2 (f : V → ℝ) : l2 (lift (D := D) f)=l2 f := by unfold l2; rw [lift_energy]

omit [Nonempty D] in
lemma average_mean (f : V × D → ℝ) : (𝔼 v, average f v) = 𝔼 p, f p :=
  (expect_prod f).symm

lemma average_energy (f : V × D → ℝ) : energy (average f) ≤ energy f := by
  unfold energy
  rw [expect_prod]
  apply expect_le_expect
  intro v _
  exact mean_sq_le_energy (fun d => f (v,d))

omit [Fintype V] in
lemma residual_mean (f : V × D → ℝ) (v : V) : (𝔼 d, residual f (v,d))=0 := by
  simp only [residual,lift,average]
  rw [expect_sub_distrib,Fintype.expect_const]
  ring

lemma residual_energy (f : V × D → ℝ) : energy (residual f)=energy f-energy (average f) := by
  unfold energy
  rw [expect_prod]
  have he (v : V) : (𝔼 d, residual f (v,d)^2)= (𝔼 d, f (v,d)^2)-(average f v)^2 :=
    energy_center (fun d => f (v,d))
  simp_rw [he]
  rw [expect_sub_distrib,← expect_prod (fun p : V × D => f p^2)]

lemma residual_energy_le (f : V × D → ℝ) : energy (residual f) ≤ energy f := by
  rw [residual_energy]
  linarith [energy_nonneg (average f)]

lemma average_l2 (f : V × D → ℝ) : l2 (average f) ≤ l2 f :=
  Real.sqrt_le_sqrt (average_energy f)
lemma residual_l2 (f : V × D → ℝ) : l2 (residual f) ≤ l2 f :=
  l2_mono _ _ (residual_energy_le f)

omit [Fintype V] [Nonempty D] in
lemma decompose (f : V × D → ℝ) : (fun p => lift (average f) p+residual f p)=f := by
  funext p
  unfold residual
  ring

omit [Fintype V] [Fintype D] [Nonempty D] [Nonempty S] in
lemma cloud_add (H : PortGraph D S) (f g : V × D → ℝ) :
    cloud H (fun p => f p+g p)=fun p => cloud H f p+cloud H g p := by
  funext p
  unfold cloud adjacency
  rw [expect_add_distrib]

omit [Fintype V] [Fintype D] [Nonempty D] in
lemma cloud_lift (H : PortGraph D S) (f : V → ℝ) : cloud H (lift f)=lift f := by
  funext p
  change (𝔼 _s : S, f p.1)=f p.1
  exact Fintype.expect_const _

omit [Fintype V] [Nonempty D] in
lemma cloud_decompose (H : PortGraph D S) (f : V × D → ℝ) :
    cloud H f=fun p => lift (average f) p+cloud H (residual f) p := by
  calc
    _ = cloud H (fun p => lift (average f) p+residual f p) := congrArg (cloud H) (decompose f).symm
    _ = _ := by rw [cloud_add,cloud_lift]

omit [Nonempty S] in
lemma cloud_residual_energy (H : PortGraph D S) {ρ : ℝ} (hH : H.Contracts ρ)
    (f : V × D → ℝ) : energy (cloud H (residual f)) ≤ ρ^2*energy (residual f) := by
  unfold energy
  rw [expect_prod,expect_prod,mul_expect]
  apply expect_le_expect
  intro v _
  exact hH (fun d => residual f (v,d)) (residual_mean f v)

omit [Nonempty S] in
lemma cloud_residual_l2 (H : PortGraph D S) {ρ : ℝ} (hρ : 0 ≤ ρ) (hH : H.Contracts ρ)
    (f : V × D → ℝ) : l2 (cloud H (residual f)) ≤ ρ*l2 (residual f) :=
  l2_le_of_energy_le hρ _ _ (cloud_residual_energy H hH f)

omit [Nonempty D] in
lemma cloud_energy_le (H : PortGraph D S) (f : V × D → ℝ) : energy (cloud H f) ≤ energy f := by
  unfold energy
  rw [expect_prod,expect_prod]
  apply expect_le_expect
  intro v _
  exact H.energy_adjacency_le (fun d => f (v,d))

omit [Nonempty D] in
lemma cloud_l2_le (H : PortGraph D S) (f : V × D → ℝ) : l2 (cloud H f) ≤ l2 f :=
  l2_mono _ _ (cloud_energy_le H f)

omit [Fintype V] [Fintype D] [Nonempty D] in
lemma permute_add (G : PortGraph V D) (f g : V × D → ℝ) :
    permute G (fun p => f p+g p)=fun p => permute G f p+permute G g p := rfl

omit [Nonempty D] in
lemma permute_energy (G : PortGraph V D) (f : V × D → ℝ) : energy (permute G f)=energy f := by
  unfold energy permute
  exact Fintype.expect_equiv G.rotate _ _ (fun _ => rfl)

omit [Nonempty D] in
lemma permute_l2 (G : PortGraph V D) (f : V × D → ℝ) : l2 (permute G f)=l2 f := by
  unfold l2
  rw [permute_energy]

omit [Fintype V] [Nonempty D] in
lemma average_permute_lift (G : PortGraph V D) (f : V → ℝ) :
    average (permute G (lift f))=G.adjacency f := rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPCloud

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphRelabel

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

lemma energy_comp_equiv {V W : Type} [Fintype V] [Fintype W] (e : V ≃ W) (f : W → ℝ) :
    energy (f ∘ e)=energy f := by
  unfold energy
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

namespace PortGraph
variable {V D W E : Type}

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype W] [Nonempty W] [Fintype E] [Nonempty E]

omit [Fintype V] [Nonempty V] [Nonempty D] [Fintype W] [Nonempty W] [Nonempty E] in
lemma relabel_adjacency (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) (f : W → ℝ) :
    ((G.relabel e d).adjacency f) ∘ e=G.adjacency (f ∘ e) := by
  funext v
  unfold adjacency
  simp only [Function.comp_apply,relabel_step,Equiv.symm_apply_apply]
  exact (Fintype.expect_equiv d (fun s : D => f (e (G.step v s)))
    (fun s : E => f (e (G.step v (d.symm s)))) (by intro s; rw [Equiv.symm_apply_apply])).symm

omit [Nonempty V] [Nonempty D] [Nonempty W] [Nonempty E] in
theorem relabel_contracts (G : PortGraph V D) (e : V ≃ W) (d : D ≃ E) {ρ : ℝ}
    (hG : G.Contracts ρ) : (G.relabel e d).Contracts ρ := by
  intro f hf
  have hm : (𝔼 v, (f ∘ e) v)=0 :=
    (Fintype.expect_equiv e (f ∘ e) f (fun _ => rfl)).trans hf
  have h := hG (f ∘ e) hm
  rw [energy_comp_equiv e f] at h
  rw [← energy_comp_equiv e ((G.relabel e d).adjacency f),relabel_adjacency]
  exact h

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphRelabel

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_SmallBias
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSmallBias

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace Walsh
variable {I : Type} [Fintype I] [DecidableEq I]

theorem baseGraph_contracts : baseGraph.Contracts (1/10) :=
  cayley_contracts baseGenerators (1/10) (Classical.choose_spec exists_base_generators)

end Walsh
end MetricKMedian.PCP

end Inline_PCPSmallBias

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_Zigzag
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_left_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_right_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.center_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.concat_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.reverse_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_left _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_concat_right _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.segment_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPZigzag

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype S] [Nonempty S]

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma zigzag_decomposition (G : PortGraph V D) (H : PortGraph D S) (f : V × D → ℝ) :
    (G.zigzag H).adjacency f = fun p =>
      lift (G.adjacency (average f)) p +
      cloud H (residual (permute G (lift (average f)))) p +
      cloud H (permute G (cloud H (residual f))) p := by
  rw [zigzag_adjacency,cloud_decompose H f,permute_add,cloud_add]
  rw [cloud_decompose H (permute G (lift (average f))),average_permute_lift]

omit [Nonempty V] in
theorem zigzag_contracts (G : PortGraph V D) (H : PortGraph D S) {ρ σ : ℝ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hG : G.Contracts ρ) (hH : H.Contracts σ) :
    (G.zigzag H).Contracts (ρ+2*σ) := by
  intro f hf
  have hfmean : (𝔼 v, average f v)=0 := (average_mean f).trans hf
  have hfirst : l2 (lift (D := D) (G.adjacency (average f))) ≤ ρ*l2 f := by
    rw [lift_l2]
    exact (G.l2_contracts hρ hG _ hfmean).trans (mul_le_mul_of_nonneg_left (average_l2 f) hρ)
  have havg : l2 (permute G (lift (average f))) ≤ l2 f := by
    rw [permute_l2,lift_l2]
    exact average_l2 f
  have hsecond : l2 (cloud H (residual (permute G (lift (average f))))) ≤ σ*l2 f :=
    (cloud_residual_l2 H hσ hH _).trans (mul_le_mul_of_nonneg_left
      ((residual_l2 _).trans havg) hσ)
  have hthird : l2 (cloud H (permute G (cloud H (residual f)))) ≤ σ*l2 f := by
    calc
      _ ≤ l2 (permute G (cloud H (residual f))) := cloud_l2_le H _
      _ = l2 (cloud H (residual f)) := permute_l2 G _
      _ ≤ σ*l2 (residual f) := cloud_residual_l2 H hσ hH f
      _ ≤ σ*l2 f := mul_le_mul_of_nonneg_left (residual_l2 f) hσ
  have hout : l2 ((G.zigzag H).adjacency f) ≤ (ρ+2*σ)*l2 f := by
    rw [zigzag_decomposition]
    have h1 := l2_add
      (fun p => lift (G.adjacency (average f)) p+
        cloud H (residual (permute G (lift (average f)))) p)
      (cloud H (permute G (cloud H (residual f))))
    have h2 := l2_add (lift (D := D) (G.adjacency (average f)))
      (cloud H (residual (permute G (lift (average f)))))
    linarith
  have hsq := pow_le_pow_left₀ (l2_nonneg ((G.zigzag H).adjacency f)) hout 2
  simpa only [mul_pow,l2_sq] using hsq

omit [Nonempty V] in
theorem square_zigzag_half (G : PortGraph V D) (H : PortGraph (D × D) S)
    (hG : G.Contracts (1/2)) (hH : H.Contracts (1/10)) :
    (G.square.zigzag H).Contracts (1/2) := by
  have h := zigzag_contracts G.square H (by positivity : (0:ℝ) ≤ (1/2)^2)
    (by norm_num : (0:ℝ) ≤ 1/10) (square_contracts G hG) hH
  intro f hf
  have hh := h f hf
  have hn := energy_nonneg f
  norm_num at hh
  nlinarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPZigzag

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderFamily
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderFamily

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace ExpanderFamily

lemma base_contracts : base.Contracts (1/10) :=
  Walsh.baseGraph.relabel_contracts baseVertexEquiv (Equiv.refl SmallPort) Walsh.baseGraph_contracts

lemma graph_contracts_s53_oai : ∀ n, (graph n).Contracts (1/2) := by
  intro n
  induction n with
  | zero =>
    let : Subsingleton (Vertex 0) := inferInstanceAs (Subsingleton Unit)
    intro f hf
    have he : f=fun _ => 0 := by
      funext v
      have hc : (𝔼 w, f w)=f v := by
        have hh : f=fun _ => f v := funext (fun w => congrArg f (Subsingleton.elim w v))
        rw [hh,Fintype.expect_const]
      exact hc.symm.trans hf
    rw [he,PortGraph.adjacency_const]
    simp [energy]
  | succ n ih => exact PortGraph.square_zigzag_half (graph n) base ih base_contracts

end ExpanderFamily
end MetricKMedian.PCP

end Inline_PCPExpanderFamily

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53_oai := @OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53_oai
