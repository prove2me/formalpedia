-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:44:43.646767+00:00
-- url     : https://prove2.me/submissions/0d48d1c0-629e-4633-bec9-755032e334aa

import Mathlib
import Definitions.Def_OAIQ053K083
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_SeedProgram_good_bound_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_ProjectionSeed_bad_bound_s53

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

theorem testRate_eq_count (p : S → Prop) [DecidablePred p] :
    testRate p = ((univ.filter p).card : ℝ) / Fintype.card S := by
  classical
  rw [testRate, Fintype.expect_eq_sum_div_card]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  apply sum_congr rfl
  intro s _
  split_ifs <;> rfl

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

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

theorem pairing_sq_le (f g : S → ℝ) : pairing f g ^ 2 ≤ energy f * energy g :=
  expect_mul_sq_le_sq_mul_sq _ _ _

end FiniteEnergy

end MetricKMedian.PCP

end Inline_PCPSpectralWalk

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

lemma mean_sq_le_energy [Nonempty S] (f : S → ℝ) : (𝔼 x, f x)^2 ≤ energy f := by
  have h := pairing_sq_le (fun _ : S => (1:ℝ)) f
  simpa [pairing,energy] using h

end

end MetricKMedian.PCP

end Inline_PCPL2

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Operator
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionOperator

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace ProjectionMass
variable {A B : Type} [Fintype A] [Fintype B]

lemma push_total (π : A → B) (f : A → ℝ) : ∑ b, push π f b=∑ a, f a := by
  unfold push
  rw [sum_comm]
  simp

omit [Fintype B] in
lemma push_nonneg (π : A → B) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (b : B) :
    0 ≤ push π f b := sum_nonneg (fun a _ => by split_ifs; exact hf a; exact le_rfl)

omit [Fintype B] in
lemma push_abs (π : A → B) (f : A → ℝ) (b : B) :
    |push π f b| ≤ push π (fun a => |f a|) b := by
  unfold push
  calc
    _ ≤ ∑ a, |if π a=b then f a else 0| := abs_sum_le_sum_abs _ _
    _ = _ := by apply sum_congr rfl; intro a _; split_ifs <;> simp

lemma push_sq_sum (π : A → B) (f : A → ℝ) :
    ∑ b, push π f b^2 ≤ (∑ a, |f a|)^2 := by
  calc
    _ ≤ ∑ b, push π (fun a => |f a|) b^2 := by
      apply sum_le_sum
      intro b _
      have h := push_abs π f b
      have hn := push_nonneg π (fun a => |f a|) (fun _ => abs_nonneg _) b
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (push π f b)) hn).mpr h
    _ ≤ (∑ b, push π (fun a => |f a|) b)^2 :=
      sum_sq_le_sq_sum_of_nonneg (fun b _ => push_nonneg π _ (fun _ => abs_nonneg _) b)
    _ = _ := by rw [push_total]
end ProjectionMass

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

omit [Fintype U] [Fintype V] [Fintype D] [Fintype T] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_nonneg (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) :
    ∀ v b t, 0 ≤ G.push f v b t := by
  intro v b t
  exact expect_nonneg (fun s _ => ProjectionMass.push_nonneg _ _ (fun a => hf _ a _) _)

omit [Nonempty U] [Nonempty V] in
lemma collision_le_abs_total (f : U → A → T → ℝ) :
    G.collision f ≤ MixedNorm.sq (fun u t => ∑ a, |f u a t|) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ 𝔼 v, ∑ b, ∑ t, 𝔼 s,
        (ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b)^2 := by
      apply expect_le_expect
      intro v _
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro t _
      exact mean_sq_le_energy _
    _ = 𝔼 v, 𝔼 s, ∑ t, ∑ b,
        (ProjectionMass.push (G.project (G.source v s)) (fun a => f (G.source v s).1 a t) b)^2 := by
      simp_rw [← expect_sum_comm]
      apply expect_congr rfl
      intro v _
      apply expect_congr rfl
      intro s _
      exact sum_comm
    _ ≤ 𝔼 v, 𝔼 s, ∑ t, (∑ a, |f (G.source v s).1 a t|)^2 := by
      apply expect_le_expect
      intro v _
      apply expect_le_expect
      intro s _
      exact sum_le_sum (fun t _ => ProjectionMass.push_sq_sum _ _)
    _ = _ := by
      rw [G.source_expect (fun p : U × D => ∑ t, (∑ a, |f p.1 a t|)^2)]
      simp only [Fintype.expect_const]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Product
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionProduct

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace ProjectionMass
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
omit [Fintype B] in
lemma push_sum (π : A → B) (f : I → A → ℝ) (b : B) :
    push π (fun a => ∑ i, f i a) b=∑ i, push π (f i) b := by
  unfold push
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  split_ifs <;> simp
end ProjectionMass

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' T I : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Fintype T] [Fintype I]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')

omit [Fintype U] [Fintype V] [Fintype D] [Fintype B] [Fintype T]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_sum (f : I → U → A → T → ℝ) (v : V) (b : B) (t : T) :
    G.push (fun u a t => ∑ i, f i u a t) v b t=∑ i, G.push (f i) v b t := by
  simp only [push,ProjectionMass.push_sum,expect_sum_comm]

omit [Fintype U] [Fintype V] [Fintype D] [Fintype B]
  [Fintype U'] [Fintype V'] [Fintype D'] [Fintype B'] [Fintype T]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
lemma prod_push (f : (U × U') → (A × A') → T → ℝ)
    (v : V) (v' : V') (b : B) (b' : B') (t : T) :
    (G.prod H).push f (v,v') (b,b') t =
      G.push (fun u a (_ : Unit) => H.push (fun u' a' t => f (u,u') (a,a') t) v' b' t) v b () := by
  unfold push ProjectionMass.push
  simp only [source,prod,Prod.mk.injEq,Fintype.sum_prod_type,expect_prod]
  dsimp only [Equiv.symm]
  apply expect_congr rfl
  intro s _
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : G.project (G.edge.symm (v,s)) a=b
  · simp [h]
    rfl
  · simp [h]

omit [Fintype U] [Fintype A] [Fintype U'] [Fintype V'] [Fintype D'] [Fintype B']
  [Fintype T] [Nonempty U] [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
lemma partialPush_nonneg (f : (U × U') → (A × A') → T → ℝ)
    (hf : ∀ u a t, 0 ≤ f u a t) : ∀ u a z, 0 ≤ H.partialPush f u a z := by
  intro u a z
  exact H.push_nonneg _ (fun u' a' t => hf _ _ _) _ _ _

omit [Fintype U] [Fintype U'] [Fintype V'] [Fintype D'] [Fintype B'] [Fintype T]
  [Nonempty U] [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] in
lemma partialPush_total (f : (U × U') → (A × A') → T → ℝ) (u : U) (z : V' × (B' × T)) :
    (∑ a, H.partialPush f u a z)=
      H.push (fun u' a' t => ∑ a, f (u,u') (a,a') t) z.1 z.2.1 z.2.2 := by
  exact (H.push_sum (fun a u' a' t => f (u,u') (a,a') t) _ _ _).symm

omit [Fintype U] [Fintype D] [Fintype U'] [Fintype D']
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty U'] [Nonempty D'] [Nonempty S'] in
lemma prod_collision (f : (U × U') → (A × A') → T → ℝ) :
    (G.prod H).collision f * Fintype.card V'=G.collision (H.partialPush f) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type,expect_prod]
  simp_rw [G.prod_push H]
  rw [expect_mul]
  apply expect_congr rfl
  intro v _
  rw [Fintype.expect_eq_sum_div_card,div_mul_cancel₀ _ (show (Fintype.card V' : ℝ) ≠ 0 by positivity)]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro v' _
  apply sum_congr rfl
  intro b' _
  apply sum_congr rfl
  intro t _
  rfl

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionProduct

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionExpansion

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
variable {U T : Type} [Fintype U] [Nonempty U] [Fintype T]

lemma sq_le_uniform (f : U → T → ℝ) (M : ℝ) (h : ∀ u, ∑ t, f u t^2≤M) : sq f≤M := by
  unfold sq
  exact (expect_le_expect (fun u _ => h u)).trans_eq (Fintype.expect_const M)
end MixedNorm

end MetricKMedian.PCP

end Inline_PCPProjectionExpansion

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Rounding
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BiProjection.prod_source _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRounding

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

omit [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
  [Nonempty A] [Nonempty B] in
lemma fractional_score_reindex (f : U → A → ℝ) (b : V → B) :
    (𝔼 v, G.scalarPush f v (b v)) =
      𝔼 u, ∑ a, f u a*(𝔼 d, if G.project (u,d) a=b (G.edge (u,d)).1 then (1:ℝ) else 0) := by
  have he (v : V) (s : S) : (G.edge (G.source v s)).1=v := by
    simp only [source,Equiv.apply_symm_apply]
  unfold scalarPush push ProjectionMass.push
  calc
    _ = 𝔼 v, 𝔼 s, ∑ a, if G.project (G.source v s) a=
        b (G.edge (G.source v s)).1 then f (G.source v s).1 a else 0 := by
      simp_rw [he]
    _ = 𝔼 u, 𝔼 d, ∑ a, if G.project (u,d) a=b (G.edge (u,d)).1 then f u a else 0 :=
      G.source_expect (fun p => ∑ a, if G.project p a=b (G.edge p).1 then f p.1 a else 0)
    _ = _ := by
      simp_rw [expect_sum_comm,mul_expect]
      apply sum_congr rfl
      intro a _
      apply expect_congr rfl
      intro u _
      apply expect_congr rfl
      intro d _
      split_ifs <;> simp

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRounding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Bound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BiProjection.prod_source
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace MixedNorm
lemma selected_le {V T : Type} [Fintype V] [Fintype T] [Nonempty V]
    (f : V → T → ℝ) (g : V → T) : energy (fun v => f v (g v)) ≤ sq f := by
  unfold energy sq
  apply expect_le_expect
  intro v _
  exact single_le_sum (fun t _ => _root_.sq_nonneg (f v t)) (mem_univ (g v))
end MixedNorm

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

omit [Nonempty V] [Nonempty A] [Nonempty B] in
lemma collisionBound_one : G.CollisionBound 1 := by
  intro T _ f hf M hM hm
  have hh := G.collision_le_abs_total f
  simp only [abs_of_nonneg (hf _ _ _)] at hh
  simpa only [one_mul] using hh.trans (MixedNorm.sq_le_uniform _ M hm)

omit [Fintype V] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma score_nonneg (a : U → A) (b : V → B) : 0 ≤ G.score a b := by
  unfold score
  exact expect_nonneg (fun _ _ => expect_nonneg (fun _ _ => by split_ifs <;> norm_num))

omit [Fintype U] [Fintype A] [Nonempty U] [Nonempty A] in
lemma pointLabel_nonneg (a : U → A) : ∀ u c t, 0 ≤ pointLabel a u c t := by
  intros
  unfold pointLabel
  split_ifs <;> norm_num

omit [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D]
  [Nonempty S] [Nonempty A] [Nonempty B] in
lemma score_eq_push (a : U → A) (b : V → B) :
    G.score a b=(𝔼 v, G.push (pointLabel a) v (b v) ()) := by
  have hh := G.fractional_score_reindex (fun u c => pointLabel a u c ()) b
  simp only [pointLabel] at hh
  simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true] at hh
  exact hh.symm

omit [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma score_sq_le_collision (a : U → A) (b : V → B) :
    G.score a b^2≤G.collision (pointLabel a) := by
  rw [G.score_eq_push]
  calc
    _ ≤ energy (fun v => G.push (pointLabel a) v (b v) ()) := mean_sq_le_energy _
    _ ≤ G.collision (pointLabel a) :=
      MixedNorm.selected_le (fun v (p : B × Unit) => G.push (pointLabel a) v p.1 p.2)
        (fun v => (b v,()))

omit [Nonempty U] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma sound_of_collisionBound (r ε : ℝ) (hr : G.CollisionBound r) (hε : 0 ≤ ε)
    (he : r≤ε^2) : G.Sound ε := by
  intro a b
  have hp := hr Unit (pointLabel a) (pointLabel_nonneg a) 1 (by norm_num) (by
    intro u
    simp [pointLabel])
  have hq := (G.score_sq_le_collision a b).trans hp
  simp only [mul_one] at hq
  nlinarith [G.score_nonneg a b]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tensor
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionTensor

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B']
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')

omit [Fintype U] [Fintype U'] [Fintype D'] [Nonempty U] [Nonempty A]
  [Nonempty U'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma partialPush_budget (r M : ℝ) (hr : H.CollisionBound r)
    (f : (U × U') → (A × A') → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t)
    (hM : 0 ≤ M) (hm : ∀ u, ∑ t, (∑ a, f u a t)^2≤M) (u : U) :
    (∑ z, (∑ a, H.partialPush f u a z)^2) ≤ (Fintype.card V':ℝ)*(r*M) := by
  let g : U' → A' → T → ℝ := fun u' a' t => ∑ a, f (u,u') (a,a') t
  have hg : ∀ u' a' t, 0 ≤ g u' a' t := fun u' a' t => sum_nonneg (fun a _ => hf _ _ _)
  have hgM : ∀ u', ∑ t, (∑ a', g u' a' t)^2≤M := by
    intro u'
    have hh := hm (u,u')
    simp only [Fintype.sum_prod_type] at hh
    change (∑ t, (∑ a', ∑ a, f (u,u') (a,a') t)^2)≤M
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro t _
    congr 1
    exact sum_comm
  have h := hr T g hg M hM hgM
  have he : (∑ z, (∑ a, H.partialPush f u a z)^2) =
      (Fintype.card V':ℝ)*H.collision g := by
    simp_rw [H.partialPush_total]
    unfold collision MixedNorm.sq
    rw [Fintype.expect_eq_sum_div_card,mul_div_cancel₀ _ (show (Fintype.card V':ℝ) ≠ 0 by positivity)]
    simp only [Fintype.sum_prod_type,g]
  rw [he]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

omit [Fintype U] [Fintype D] [Fintype U'] [Fintype D']
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
  [Nonempty U'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma collisionBound_prod (r s : ℝ) (_hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hr : G.CollisionBound r) (hs : H.CollisionBound s) :
    (G.prod H).CollisionBound (r*s) := by
  intro T _ f hf M hM hm
  have h := hr (V' × (B' × T)) (H.partialPush f) (H.partialPush_nonneg f hf)
    ((Fintype.card V':ℝ)*(s*M)) (by positivity) (H.partialPush_budget s M hs f hf hM hm)
  rw [← G.prod_collision H f] at h
  apply (mul_le_mul_iff_left₀ (show 0 < (Fintype.card V':ℝ) by positivity)).mp
  nlinarith only [h]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionTensor

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Repeat
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Nested.inhabited _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRepeat

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}

variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty D]
  [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionBound_power (r : ℝ) (hr0 : 0 ≤ r) (hr : G.CollisionBound r) (n : ℕ) :
    (G.power n).CollisionBound (r^n) := by
  induction n with
  | zero => exact trivial.collisionBound_one
  | succ n ih =>
    rw [pow_succ']
    change (G.prod (G.power n)).CollisionBound (r*r^n)
    exact G.collisionBound_prod (G.power n) r (r^n) hr0 (pow_nonneg hr0 _) hr ih

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRepeat

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Input
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

variable [Nonempty (Fin u)] [Nonempty (Fin v)] [Nonempty (Fin d)] [Nonempty (Fin s)]
  [Nonempty (Fin a)] [Nonempty (Fin b)]
omit [Nonempty (Fin u)] [Nonempty (Fin v)] [Nonempty (Fin d)]
  [Nonempty (Fin s)] [Nonempty (Fin a)] [Nonempty (Fin b)] in
lemma system_score (left : Fin u → Fin a) (right : Fin v → Fin b) :
    ((G.system.satisfied left right).card : ℝ)/(v*s)=G.score left right := by
  have he := testRate_equiv G.edge.symm (fun p =>
    G.project p (left p.1)=right (G.edge p).1)
  simp only [Equiv.apply_symm_apply] at he
  have hl : testRate (fun p : Fin v × Fin s =>
      G.project (G.edge.symm p) (left (G.edge.symm p).1)=right p.1)=
      ((G.system.satisfied left right).card : ℝ)/(v*s) := by
    rw [testRate_eq_count]
    simp only [Coverage.ProjectionSystem.satisfied,system,Fintype.card_prod,
      Fintype.card_fin,Nat.cast_mul,Prod.eta]
    congr 2
  rw [hl] at he
  simpa only [testRate,expect_prod,score] using he
omit [Nonempty (Fin u)] [Nonempty (Fin v)] [Nonempty (Fin d)]
  [Nonempty (Fin s)] [Nonempty (Fin a)] [Nonempty (Fin b)] in
lemma input_sound (hu : 0<u) (hv : 0<v) (hs : 0 < s) (ha : 0<a) (hb : 0<b)
    (hc : G.Consistent) {ε : ℝ} (h : G.Sound ε) : (G.input hu hv hs ha hb hc).Sound ε := by
  intro left right
  have hh := h left right
  rw [← G.system_score left right] at hh
  have hp : (0:ℝ)<v*s := mul_pos (Nat.cast_pos.mpr hv) (Nat.cast_pos.mpr hs)
  have hh' := (div_le_iff₀ hp).mp hh
  simpa only [input,mul_assoc] using hh'
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

variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable [Fintype U'] [Fintype V'] [Fintype D'] [Fintype S'] [Fintype A'] [Fintype B']
variable [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B']
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
  [Fintype V'] [Fintype S'] [Fintype A'] [Fintype B']
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma reindex_score (a : U' → A') (b : V' → B') :
    (G.reindex eu ev ed es ea eb).score a b=G.score (ea.symm ∘ a ∘ eu) (eb.symm ∘ b ∘ ev) := by
  unfold score
  rw [← Fintype.expect_equiv eu (fun u => 𝔼 d : D', if
    (G.reindex eu ev ed es ea eb).project (eu u,d) (a (eu u))=
      b ((G.reindex eu ev ed es ea eb).edge (eu u,d)).1 then (1:ℝ) else 0) _ (fun _ => rfl)]
  apply expect_congr rfl
  intro u _
  rw [← Fintype.expect_equiv ed (fun d => if
    (G.reindex eu ev ed es ea eb).project (eu u,ed d) (a (eu u))=
      b ((G.reindex eu ev ed es ea eb).edge (eu u,ed d)).1 then (1:ℝ) else 0) _ (fun _ => rfl)]
  apply expect_congr rfl
  intro d _
  simp only [reindex,Equiv.prodCongr_symm,Equiv.prodCongr_apply,Equiv.symm_apply_apply,
    Equiv.trans_apply,Function.comp_def,← Equiv.eq_symm_apply,Prod.map]
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
  [Fintype V'] [Fintype S'] [Fintype A'] [Fintype B']
  [Nonempty U'] [Nonempty V'] [Nonempty D'] [Nonempty S'] [Nonempty A'] [Nonempty B'] in
lemma reindex_sound {δ : ℝ} (h : G.Sound δ) : (G.reindex eu ev ed es ea eb).Sound δ := by
  intro a b
  rw [G.reindex_score eu ev ed es ea eb a b]
  exact h _ _
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionReindex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Tables
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
lemma input_sound (hc : G.Consistent) (ε : ℝ) (hn : G.Sound ε) : (input G ue vo so ao bo hc).Sound ε := by
  let : Nonempty (Fin nu) := Fin.pos_iff_nonempty.mp (nu_pos ue)
  let : Nonempty (Fin vo.entries.length) := Fin.pos_iff_nonempty.mp (order_pos vo)
  let : Nonempty (Fin so.entries.length) := Fin.pos_iff_nonempty.mp (order_pos so)
  let : Nonempty (Fin ao.entries.length) := Fin.pos_iff_nonempty.mp (order_pos ao)
  let : Nonempty (Fin bo.entries.length) := Fin.pos_iff_nonempty.mp (order_pos bo)
  apply BiProjection.input_sound
  exact G.reindex_sound _ _ _ _ _ _ hn
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

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

lemma contraction_nonneg : 0 ≤ contraction := le_trans (by norm_num : (0:ℝ)≤1-1/1024) (le_max_right _ _)
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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
lemma output_sound_s53_oai (n : ℕ) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
    (ε : ℝ) (hε : 0≤ε) (hn : ProjectionSeed.contraction^n≤ε^2) : (output t h n).Sound ε := by
  unfold output
  split_ifs with hl
  · apply input_sound
    exact BiProjection.sound_of_collisionBound _ _ ε
      (BiProjection.collisionBound_power _ ProjectionSeed.contraction ProjectionSeed.contraction_nonneg
        (good_bound_s53 t h hl hg) n) hε hn
  · apply input_sound
    exact BiProjection.sound_of_collisionBound _ _ ε
      (BiProjection.collisionBound_power _ ProjectionSeed.contraction ProjectionSeed.contraction_nonneg
        ProjectionSeed.bad_bound_s53 n) hε hn
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53_oai := @OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53_oai
