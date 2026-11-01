-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.BiProjection.variance_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:17:16.20844+00:00
-- url     : https://prove2.me/submissions/932fdc7f-b25b-479f-9b78-f32745260647

import Mathlib
import Definitions.Def_OAIQ053K024

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

theorem energy_center [Nonempty S] (f : S → ℝ) :
    energy (fun s => f s - 𝔼 t, f t) = energy f - (𝔼 t, f t)^2 := by
  unfold energy
  simp_rw [sub_sq]
  rw [expect_add_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const]
  ring

end FiniteEnergy

end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Operator
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
omit [Nonempty U] in
lemma sq_coordinates (f : U → T → ℝ) : sq f=∑ t, energy (fun u => f u t) := by
  unfold sq energy
  exact expect_sum_comm _ _ _

lemma sq_center (f : U → T → ℝ) :
    sq (fun u t => f u t-𝔼 v, f v t)=sq f-∑ t, (𝔼 u, f u t)^2 := by
  rw [sq_coordinates,sq_coordinates]
  simp_rw [energy_center]
  rw [sum_sub_distrib]

lemma sq_le_uniform (f : U → T → ℝ) (M : ℝ) (h : ∀ u, ∑ t, f u t^2≤M) : sq f≤M := by
  unfold sq
  exact (expect_le_expect (fun u _ => h u)).trans_eq (Fintype.expect_const M)
end MixedNorm

namespace BiProjection
variable {U V D S A B T : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B] [Fintype T]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S]
variable (G : BiProjection U V D S A B)

omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma collision_le_average (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) :
    G.collision f ≤ MixedNorm.sq (fun v t => G.average (fun u => ∑ a, f u a t) v) := by
  unfold collision MixedNorm.sq
  simp only [Fintype.sum_prod_type]
  apply expect_le_expect
  intro v _
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  have h := sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset B))
    (fun b _ => G.push_nonneg f hf v b t)
  rwa [G.push_total] at h

omit [Fintype D] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma collision_variance (γ : ℝ) (hG : G.Expands γ)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) :
    G.collision f ≤ MixedNorm.sq (fun u t => ∑ a, f u a t)-
      γ*MixedNorm.sq (fun u t => (∑ a, f u a t)-(𝔼 v, ∑ a, f v a t)) := by
  have h := sum_le_sum (fun t (_ : t ∈ (univ : Finset T)) => hG (fun u => ∑ a, f u a t))
  have hfirst := G.collision_le_average f hf
  rw [MixedNorm.sq_coordinates] at hfirst
  rw [sum_add_distrib,← mul_sum,← mul_sum] at h
  rw [MixedNorm.sq_center,MixedNorm.sq_coordinates]
  nlinarith only [hfirst,h]

omit [Fintype D] [Nonempty V] [Nonempty D] [Nonempty S] in
lemma variance_bound_s53_oai (γ : ℝ) (hG : G.Expands γ)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t) (M : ℝ)
    (hm : ∀ u, ∑ t, (∑ a, f u a t)^2 ≤ M^2) :
    γ*MixedNorm.sq (fun u t => (∑ a, f u a t)-(𝔼 v, ∑ a, f v a t)) ≤
      M^2-G.collision f := by
  have h := G.collision_variance γ hG f hf
  have hh := MixedNorm.sq_le_uniform (fun u t => ∑ a, f u a t) (M^2) hm
  linarith

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionExpansion

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.BiProjection.variance_bound_s53_oai := @OAI.MetricKMedian.PCP.BiProjection.variance_bound_s53_oai
