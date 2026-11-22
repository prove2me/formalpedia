-- Prove2me | solution 1 for MajorityDepthThree.Exact.lift_coverage
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:53:58.734404+00:00
-- url     : https://prove2.me/submissions/53fd4ed2-e2f9-417a-9e74-ce31b2eab28d

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact.LiftProof

open scoped BigOperators
noncomputable section
variable {α : Type} [DecidableEq α] {V : Finset α}

theorem restore (ρ : Restriction V) {S : Finset α} (h : ρ.pos ⊆ S) :
    (S \ ρ.pos) ∪ ρ.pos = S := Finset.sdiff_union_of_subset h

theorem residual_inj (ρ : Restriction V) {S T : Finset α}
    (hS : StronglyConsistent ρ S) (hT : StronglyConsistent ρ T)
    (he : S \ ρ.pos = T \ ρ.pos) : S = T := by
  rw [← restore ρ hS.1, ← restore ρ hT.1, he]

theorem residual_mem (A : Family α) (ρ : Restriction V) {T : Finset α}
    (hT : T ∈ residual A ρ) :
    T ∪ ρ.pos ∈ A ∧ StronglyConsistent ρ (T ∪ ρ.pos) ∧ Disjoint T ρ.pos := by
  classical
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨hSA, hSC⟩ := Finset.mem_filter.mp hS
  rw [restore ρ hSC.1]
  exact ⟨hSA, hSC, Finset.sdiff_disjoint⟩

theorem lift_sum (A : Family α) (ρ : Restriction V) (f : Weight α)
    (h : Finset α → ℝ) :
    (∑ S ∈ A, liftWeight ρ f S * h S) =
      ∑ T ∈ residual A ρ, f T * h (T ∪ ρ.pos) := by
  classical
  calc
    (∑ S ∈ A, liftWeight ρ f S * h S) =
        ∑ S ∈ A.filter (StronglyConsistent ρ), f (S \ ρ.pos) * h S := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hc : StronglyConsistent ρ S <;> simp [liftWeight, hc]
    _ = ∑ T ∈ residual A ρ, f T * h (T ∪ ρ.pos) := by
      apply Finset.sum_bij (fun S _ => S \ ρ.pos)
      · intro S hS
        exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
      · intro S hS T hT he
        exact residual_inj ρ (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2 he
      · intro T hT
        obtain ⟨S, hS, he⟩ := Finset.mem_image.mp hT
        exact ⟨S, hS, he⟩
      · intro S hS
        rw [restore ρ (Finset.mem_filter.mp hS).2.1]

theorem lift_cost_proof (V : Finset α) (A : Family α)
    (hA : ∀ S ∈ A, S ⊆ V) (ρ : Restriction V)
    (f : Weight α) (hf : ∀ S ∈ residual A ρ, 0 ≤ f S) :
    cost A r (liftWeight ρ f) = r ^ ρ.pos.card * cost (residual A ρ) r f := by
  classical
  rw [cost, lift_sum, cost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.card_union_of_disjoint (residual_mem A ρ hT).2.2, pow_add]
  ring

theorem residual_disjoint (A : Family α) (ρ : Restriction V) {T : Finset α}
    (hT : T ∈ residual A ρ) : Disjoint T ρ.support := by
  have hm := residual_mem A ρ hT
  apply Finset.disjoint_left.mpr
  intro x hx hxs
  rcases Finset.mem_union.mp hxs with hpos | hneg
  · exact Finset.disjoint_left.mp hm.2.2 hx hpos
  · exact Finset.disjoint_left.mp hm.2.1.2.1 (Finset.mem_union_left _ hx) hneg

theorem subset_residual_iff (A : Family α) (ρ : Restriction V) {T S : Finset α}
    (hT : T ∈ residual A ρ) (hS : ρ.pos ⊆ S) :
    T ∪ ρ.pos ⊆ S ↔ T ⊆ S \ ρ.support := by
  constructor
  · intro h x hx
    exact Finset.mem_sdiff.mpr ⟨h (Finset.mem_union_left _ hx),
      fun hs => Finset.disjoint_left.mp (residual_disjoint A ρ hT) hx hs⟩
  · intro h x hx
    rcases Finset.mem_union.mp hx with ht | hp
    · exact (Finset.mem_sdiff.mp (h ht)).1
    · exact hS hp

theorem card_partition (ρ : Restriction V) {S : Finset α} (hS : ρ.pos ⊆ S) :
    S.card = (S \ ρ.support).card + ρ.pos.card + (S ∩ ρ.neg).card := by
  have he : S ∩ ρ.support = ρ.pos ∪ (S ∩ ρ.neg) := by
    ext x
    simp only [Finset.mem_inter, Restriction.support, Finset.mem_union]
    constructor
    · rintro ⟨hs, hp | hn⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hs, hn⟩
    · rintro (hp | ⟨hs, hn⟩)
      · exact ⟨hS hp, Or.inl hp⟩
      · exact ⟨hs, Or.inr hn⟩
  have hd : Disjoint ρ.pos (S ∩ ρ.neg) :=
    ρ.disjoint.mono_right Finset.inter_subset_right
  have hc := Finset.card_sdiff_add_card_inter S ρ.support
  rw [he, Finset.card_union_of_disjoint hd] at hc
  omega

theorem contribution_lift (A : Family α) (ρ : Restriction V) (f : Weight α)
    (t : ℝ) {S : Finset α} (hS : ρ.pos ⊆ S) :
    contribution A t (liftWeight ρ f) S =
      t ^ (S ∩ ρ.neg).card * contribution (residual A ρ) t f (S \ ρ.support) := by
  classical
  have heq (C : Family α) (w : Weight α) (U : Finset α) :
      contribution C t w U =
        ∑ T ∈ C, w T * (if T ⊆ U then t ^ (U.card - T.card) else 0) := by
    rw [contribution, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp
  rw [heq, lift_sum, heq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases ht : T ⊆ S \ ρ.support
  · have hu : T ∪ ρ.pos ⊆ S := (subset_residual_iff A ρ hT hS).mpr ht
    rw [if_pos hu, if_pos ht,
      Finset.card_union_of_disjoint (residual_mem A ρ hT).2.2]
    have hcard : S.card - (T.card + ρ.pos.card) =
        (S ∩ ρ.neg).card + ((S \ ρ.support).card - T.card) := by
      have hle := Finset.card_le_card ht
      have hc := card_partition ρ hS
      omega
    rw [hcard, pow_add]
    ring
  · have hu : ¬ T ∪ ρ.pos ⊆ S := fun h => ht ((subset_residual_iff A ρ hT hS).mp h)
    simp [ht, hu]

theorem q_nonneg : 0 ≤ q := by unfold q p; positivity

theorem lift_coverage_proof (V : Finset α) (A : Family α)
    (hA : ∀ S ∈ A, S ⊆ V) (ρ : Restriction V) (f : Weight α)
    (hf : CoverFeasible (residual A ρ) q f) (S : Finset α)
    (hS : S ∈ A) (hc : Compatible A ρ S) :
    q ^ (S ∩ ρ.neg).card ≤ contribution A q (liftWeight ρ f) S := by
  rw [contribution_lift A ρ f q hc.1]
  simpa using mul_le_mul_of_nonneg_left (hf.2 _ hc.2)
    (pow_nonneg q_nonneg _)

end
end MajorityDepthThree.Exact.LiftProof


open MajorityDepthThree.Exact
theorem solution {α : Type} [DecidableEq α] (V : Finset α)
    (A : Family α) (hA : ∀ S ∈ A, S ⊆ V) (ρ : Restriction V)
    (f : Weight α) (hf : CoverFeasible (residual A ρ) q f)
    (S : Finset α) (hS : S ∈ A) (hc : Compatible A ρ S) :
    q ^ (S ∩ ρ.neg).card ≤ contribution A q (liftWeight ρ f) S :=
  MajorityDepthThree.Exact.LiftProof.lift_coverage_proof V A hA ρ f hf S hS hc

#print axioms solution
