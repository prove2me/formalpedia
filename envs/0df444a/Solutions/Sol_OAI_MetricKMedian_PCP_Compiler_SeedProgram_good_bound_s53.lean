-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:42:31.999964+00:00
-- url     : https://prove2.me/submissions/15406448-1e44-4dcc-a769-454618752871

import Mathlib
import Definitions.Def_OAIQ053K083
import Theorems.Thm_OAI_MetricKMedian_PCP_BiProjection_collisionBound_of_expansion_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_SeedProgram_rejection_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_FlexibleRegularization_contracts_s53
import Theorems.Thm_OAI_MetricKMedian_PCP_PortCSP_projection_expands_s53

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
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
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

end MetricKMedian.PCP

end Inline_PCPBinaryReduction

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
-- module Solutions.OAIQ053_KM.KMedian_Projection_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

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

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

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
-- module Solutions.OAIQ053_KM.KMedian_Projection_CSPProjection
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_bad _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_bad _root_.OAI.MetricKMedian.PCP.PortCSP.always_complete _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step
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

include hchosen in
lemma reject_incidence (x : V → A) (a : V × D → A × A) (p : V × D) (hp : C.Bad x p) :
    ∃ b : Bool, (C.projection chosen).project (p,b) (a p) ≠
      x ((C.projection chosen).edge (p,b)).1 := by
  by_contra h
  push Not at h
  have h0 : (C.repair chosen p (a p)).1=x p.1 := h false
  have h1 : (C.repair chosen p (a p)).2=x (G.rotate p).1 := h true
  have hm := (C.repair_legal chosen hchosen p (a p)).1
  have he : C.repair chosen p (a p)=(x p.1,x (G.rotate p).1) := Prod.ext h0 h1
  rw [he] at hm
  exact hp hm

variable [Fintype V] [Fintype D] [Fintype A] [Nonempty V] [Nonempty D] [Nonempty A]
omit [Fintype A] [Nonempty A]
include hchosen in
lemma projection_sound (δ : ℝ) (hδ : ∀ x : V → A, δ≤testRate (C.Bad x)) :
    (C.projection chosen).Sound (1-δ/2) := by
  intro a x
  let R : (V × D) → Bool → Prop := fun p b => (C.projection chosen).project (p,b) (a p) ≠
      x ((C.projection chosen).edge (p,b)).1
  have hp (p : V × D) : (@ite ℝ (C.Bad x p) (Classical.propDecidable _) 1 0)/2 ≤ testRate (R p) := by
    split_ifs with h
    · obtain ⟨b,hb⟩ := C.reject_incidence chosen hchosen x a p h
      simpa only [Fintype.card_bool,Nat.cast_ofNat] using testRate_ge_atom (R p) b hb
    · exact (by simpa using testRate_nonneg (R p))
  have hav := expect_le_expect (s := (univ : Finset (V × D))) (fun p _ => hp p)
  rw [← expect_div] at hav
  have he : (C.projection chosen).score a x + (𝔼 p, testRate (R p))=1 := by
    unfold BiProjection.score
    rw [← expect_add_distrib]
    calc
      _ = 𝔼 _p : V × D, (1:ℝ) := by
        apply expect_congr rfl
        intro p _
        simpa only [testRate,R] using testRate_complement (fun b : Bool =>
          (C.projection chosen).project (p,b) (a p)=x ((C.projection chosen).edge (p,b)).1)
      _ = 1 := Fintype.expect_const 1
  have hav' : testRate (C.Bad x)/2≤𝔼 p, testRate (R p) := by
    simpa only [testRate] using hav
  linarith only [hδ x,hav',he]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

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
variable {U V : Type} {D S A B : Type}
  [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D]
  [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionBound_mono (G : BiProjection U V D S A B) {r s : ℝ}
    (h : G.CollisionBound r) (hrs : r ≤ s) : G.CollisionBound s := by
  intro T _ f hf M hM hm
  exact (h T f hf M hM hm).trans (mul_le_mul_of_nonneg_right hrs hM)
end BiProjection
namespace ProjectionSeed
open Amplifier

lemma gap_pos : 0<gap := by
  unfold gap
  have hc : (0:ℝ) < capLoss := Nat.cast_pos.mpr capLoss_pos
  have hg : (0:ℝ)<ExpanderFamily.growth := Nat.cast_pos.mpr (by have := ExpanderFamily.growth_gt_one; omega)
  positivity
lemma gap_le_one : gap≤1 := by
  have hc : (1:ℝ) ≤ capLoss := by exact_mod_cast capLoss_pos
  have hg : (1:ℝ)≤ExpanderFamily.growth := by exact_mod_cast ExpanderFamily.growth_gt_one.le
  have hd : (1:ℝ)≤18*(ExpanderFamily.growth:ℝ)^2 := by nlinarith [sq_nonneg ((ExpanderFamily.growth:ℝ)-1)]
  exact (div_le_self (by positivity) hd).trans ((div_le_one (by positivity)).mpr hc)
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedSound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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
lemma good_bound_s53_oai (hl : allLegal t=true) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a) :
    (good t h).CollisionBound contraction := by
  have hs := (CloudSpec.regularCSP t h).projection_sound _ (chosen_legal t h hl) gap (rejection_s53 t h hg)
  have he := (CloudSpec.regularCSP t h).projection_expands_s53 (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2)
    (FlexibleRegularization.contracts_s53 (CloudSpec.C t h) (cloudEmbed _ (CloudSpec.EO t)) (CloudSpec.padding t h))
  have hh := (projection t h).collisionBound_of_expansion_s53 (1-gap/2) (1/4)
    (by have := gap_le_one; linarith) (by have := gap_pos; linarith) (by norm_num) (by norm_num) hs he
  have ht := BiProjection.collisionBound_prod _ (BiProjection.neutral Bool Bool Bool Bool)
    (1-(1/4:ℝ)*((1-(1-gap/2))/4)^2) 1 (by have := gap_le_one; have := gap_pos; nlinarith)
    (by norm_num) hh (BiProjection.collisionBound_one _)
  apply BiProjection.collisionBound_mono _ ht
  rw [mul_one]
  change _ ≤ max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)
  apply le_trans _ (le_max_left _ _)
  exact le_of_eq (by ring)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53_oai := @OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53_oai
