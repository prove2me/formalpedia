-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:16:31.591527+00:00
-- url     : https://prove2.me/submissions/cdd84caf-34e8-4e5b-929f-1c1e44774410

import Mathlib
import Definitions.Def_OAIQ053K024

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Operator
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

omit [Fintype U] [Fintype V] [Fintype D] [Fintype T]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma push_total (f : U → A → T → ℝ) (v : V) (t : T) :
    (∑ b, G.push f v b t)=G.average (fun u => ∑ a, f u a t) v := by
  unfold push average
  rw [← expect_sum_comm]
  simp only [ProjectionMass.push_total]

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionOperator

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Rounding
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BiProjection.prod_source
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

omit [Fintype U] [Fintype V] [Fintype D] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B] in
lemma scalarPush_nonneg (f : U → A → ℝ) (hf : ∀ u a, 0 ≤ f u a) (v : V) (b : B) :
    0 ≤ G.scalarPush f v b := G.push_nonneg _ (fun u a _ => hf u a) v b ()

omit [Fintype U] [Fintype V] [Fintype D]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty A] [Nonempty B] in
lemma scalarPush_total (f : U → A → ℝ) (H : ℝ) (hf : ∀ u, ∑ a, f u a=H) (v : V) :
    ∑ b, G.scalarPush f v b=H := by
  unfold scalarPush
  rw [G.push_total]
  simp only [average,hf,Fintype.expect_const]

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

omit [Fintype B] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty B] in
lemma fractional_score_le (s : ℝ) (hs : G.Sound s) (f : U → A → ℝ)
    (hf : ∀ u a, 0 ≤ f u a) (H : ℝ) (hH : 0 ≤ H) (ht : ∀ u, ∑ a, f u a=H)
    (b : V → B) : (𝔼 v, G.scalarPush f v (b v)) ≤ H*s := by
  let c : U → A → ℝ := fun u a => 𝔼 d,
    if G.project (u,d) a=b (G.edge (u,d)).1 then 1 else 0
  have hm (u : U) : ∃ a, ∀ z, c u z ≤ c u a := by
    obtain ⟨a,_,ha⟩ := univ.exists_max_image (c u) univ_nonempty
    exact ⟨a,fun z => ha z (mem_univ _)⟩
  choose a ha using hm
  rw [fractional_score_reindex]
  change (𝔼 u, ∑ z, f u z*c u z) ≤ _
  calc
    _ ≤ 𝔼 u, ∑ z, f u z*c u (a u) := by
      apply expect_le_expect
      intro u _
      exact sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (ha u z) (hf u z))
    _ = H*G.score a b := by
      simp only [← sum_mul,ht,← mul_expect]
      rfl
    _ ≤ H*s := mul_le_mul_of_nonneg_left (hs a b) hH

omit [Nonempty U] [Nonempty V] [Nonempty D] in
lemma scalar_collision_sound (s : ℝ) (hs : G.Sound s) (f : U → A → ℝ)
    (hf : ∀ u a, 0 ≤ f u a) (H : ℝ) (hH : 0 ≤ H) (ht : ∀ u, ∑ a, f u a=H) :
    (𝔼 v, ∑ b, (G.scalarPush f v b)^2) ≤ s*H^2 := by
  have hm (v : V) : ∃ b, ∀ c, G.scalarPush f v c ≤ G.scalarPush f v b := by
    obtain ⟨b,_,hb⟩ := univ.exists_max_image (G.scalarPush f v) univ_nonempty
    exact ⟨b,fun c => hb c (mem_univ _)⟩
  choose b hb using hm
  calc
    _ ≤ 𝔼 v, ∑ c, G.scalarPush f v c*G.scalarPush f v (b v) := by
      apply expect_le_expect
      intro v _
      apply sum_le_sum
      intro c _
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hb v c) (G.scalarPush_nonneg f hf v c)
    _ = H*(𝔼 v, G.scalarPush f v (b v)) := by
      simp only [← sum_mul,G.scalarPush_total f H ht,← mul_expect]
    _ ≤ H*(H*s) := mul_le_mul_of_nonneg_left (G.fractional_score_le s hs f hf H hH ht b) hH
    _ = _ := by ring

omit [Nonempty U] [Nonempty V] [Nonempty D] in
lemma collision_sound_s53_oai {T : Type} [Fintype T] (s : ℝ) (hs : G.Sound s)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t)
    (H : T → ℝ) (hH : ∀ t, 0 ≤ H t) (ht : ∀ u t, ∑ a, f u a t=H t) :
    G.collision f ≤ s * ∑ t, H t^2 := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ t, 𝔼 v, ∑ b, (G.scalarPush (fun u a => f u a t) v b)^2 := by
      rw [← expect_sum_comm]
      apply expect_congr rfl
      intro v _
      exact sum_comm
    _ ≤ ∑ t, s*H t^2 := sum_le_sum (fun t _ => G.scalar_collision_sound s hs _
      (fun u a => hf u a t) (H t) (hH t) (fun u => ht u t))
    _ = _ := (mul_sum _ _ _).symm

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRounding

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53_oai := @OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53_oai
