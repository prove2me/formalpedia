-- Prove2me | solution 1 for MajorityDepthThree.Exact.combine_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:58:08.267898+00:00
-- url     : https://prove2.me/submissions/aca3fee0-9b34-472b-9441-d80fce45746b

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits


-- Source: Solutions/Trail677Lift.lean

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


-- Source: Solutions/Trail677Combine.lean

set_option autoImplicit false

namespace MajorityDepthThree.Exact.CombineProof

open scoped BigOperators Classical
noncomputable section
variable {α : Type} [DecidableEq α] {V : Finset α}

theorem p_pos : 0 < p := by unfold p; positivity
theorem r_nonneg : 0 ≤ r := by unfold r; exact div_nonneg p_pos.le (by norm_num)

theorem lift_nonneg (A : Family α) (ρ : Restriction V) (f : Weight α)
    (hf : ∀ T ∈ residual A ρ, 0 ≤ f T) {S : Finset α} (hS : S ∈ A) :
    0 ≤ liftWeight ρ f S := by
  classical
  unfold liftWeight
  split_ifs with h
  · exact hf _ (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, h⟩, rfl⟩)
  · exact le_rfl

theorem contribution_nonneg (A : Family α) (f : Weight α)
    (hf : ∀ T ∈ A, 0 ≤ f T) (S : Finset α) : 0 ≤ contribution A q f S := by
  classical
  exact Finset.sum_nonneg fun T hT => mul_nonneg (hf T (Finset.mem_filter.mp hT).1)
    (pow_nonneg LiftProof.q_nonneg _)

theorem contribution_combined (A : Family α) {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff : Fin k → ℝ) (f : Fin k → Weight α) (S : Finset α) :
    contribution A q (combinedWeight ρ coeff f) S =
      ∑ i, coeff i * contribution A q (liftWeight (ρ i) (f i)) S := by
  classical
  simp only [contribution, combinedWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem combined_feasible (V : Finset α) (A : Family α)
    (hA : ∀ S ∈ A, S ⊆ V) {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff : Fin k → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (hc : ∀ S ∈ A, 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
      coeff i * q ^ (S ∩ (ρ i).neg).card)
    (f : Fin k → Weight α) (hf : ∀ i, CoverFeasible (residual A (ρ i)) q (f i)) :
    CoverFeasible A q (combinedWeight ρ coeff f) := by
  classical
  constructor
  · intro S hS
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hcoeff i)
      (lift_nonneg A (ρ i) (f i) (hf i).1 hS)
  · intro S hS
    rw [contribution_combined]
    calc
      1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
          coeff i * q ^ (S ∩ (ρ i).neg).card := hc S hS
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
          coeff i * contribution A q (liftWeight (ρ i) (f i)) S := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (LiftProof.lift_coverage_proof V A hA (ρ i) (f i) (hf i) S hS
            (Finset.mem_filter.mp hi).2) (hcoeff i)
      _ ≤ ∑ i, coeff i * contribution A q (liftWeight (ρ i) (f i)) S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg (hcoeff i)
          (contribution_nonneg A _ (fun T hT => lift_nonneg A (ρ i) (f i) (hf i).1 hT) S)

theorem cost_combined (V : Finset α) (A : Family α)
    (hA : ∀ S ∈ A, S ⊆ V) {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff : Fin k → ℝ) (f : Fin k → Weight α)
    (hf : ∀ i, CoverFeasible (residual A (ρ i)) q (f i)) :
    cost A r (combinedWeight ρ coeff f) =
      ∑ i, coeff i * r ^ (ρ i).pos.card * cost (residual A (ρ i)) r (f i) := by
  classical
  simp only [cost, combinedWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change _ = coeff i * r ^ (ρ i).pos.card * cost (residual A (ρ i)) r (f i)
  rw [mul_assoc, ← LiftProof.lift_cost_proof V A hA (ρ i) (f i) (hf i).1]
  rw [cost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem default_feasible (A : Family α) : CoverFeasible A q (fun _ => 1) := by
  classical
  refine ⟨fun _ _ => zero_le_one, ?_⟩
  intro S hS
  have hm : S ∈ A.filter (fun T => T ⊆ S) := Finset.mem_filter.mpr ⟨hS, Finset.Subset.refl _⟩
  calc
    1 = (1 : ℝ) * q ^ (S.card - S.card) := by simp
    _ ≤ contribution A q (fun _ => 1) S := by
      change 1 * q ^ (S.card - S.card) ≤
        ∑ T ∈ A.filter (fun T => T ⊆ S), 1 * q ^ (S.card - T.card)
      exact Finset.single_le_sum (f := fun T => (1 : ℝ) * q ^ (S.card - T.card))
        (fun T _ => mul_nonneg zero_le_one (pow_nonneg LiftProof.q_nonneg _)) hm

theorem cost_nonneg (A : Family α) (f : Weight α) (hf : CoverFeasible A q f) :
    0 ≤ cost A r f :=
  Finset.sum_nonneg fun T hT => mul_nonneg (hf.1 T hT) (pow_nonneg r_nonneg _)

theorem cost_values_nonempty (A : Family α) :
    {v : ℝ | ∃ f : Weight α, CoverFeasible A q f ∧ cost A r f = v}.Nonempty :=
  ⟨_, (fun _ => 1), default_feasible A, rfl⟩

theorem cost_values_bddBelow (A : Family α) :
    BddBelow {v : ℝ | ∃ f : Weight α, CoverFeasible A q f ∧ cost A r f = v} := by
  refine ⟨0, ?_⟩
  rintro v ⟨f, hf, rfl⟩
  exact cost_nonneg A f hf

theorem coverValue_le_cost (A : Family α) (f : Weight α) (hf : CoverFeasible A q f) :
    coverValue A r q ≤ cost A r f :=
  csInf_le (cost_values_bddBelow A) ⟨f, hf, rfl⟩

theorem exists_near_cover (A : Family α) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Weight α, CoverFeasible A q f ∧ cost A r f < coverValue A r q + ε := by
  obtain ⟨v, ⟨f, hf, rfl⟩, hv⟩ := Real.lt_sInf_add_pos (cost_values_nonempty A) hε
  exact ⟨f, hf, hv⟩

theorem coverValue_combined_le (V : Finset α) (A : Family α)
    (hA : ∀ S ∈ A, S ⊆ V) {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff : Fin k → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (hc : ∀ S ∈ A, 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
      coeff i * q ^ (S ∩ (ρ i).neg).card) :
    coverValue A r q ≤ ∑ i, coeff i * r ^ (ρ i).pos.card * coverValue (residual A (ρ i)) r q := by
  classical
  let a : Fin k → ℝ := fun i => coeff i * r ^ (ρ i).pos.card
  have ha : ∀ i, 0 ≤ a i := fun i => mul_nonneg (hcoeff i) (pow_nonneg r_nonneg _)
  have hsum : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / ((∑ i, a i) + 1)
  have hden : 0 < (∑ i, a i) + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  choose f hf hf_cost using fun i : Fin k => exists_near_cover (residual A (ρ i)) hδ
  have hfeasible := combined_feasible V A hA ρ coeff hcoeff hc f hf
  calc
    coverValue A r q ≤ cost A r (combinedWeight ρ coeff f) := coverValue_le_cost _ _ hfeasible
    _ = ∑ i, a i * cost (residual A (ρ i)) r (f i) := cost_combined V A hA ρ coeff f hf
    _ ≤ ∑ i, a i * (coverValue (residual A (ρ i)) r q + δ) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf_cost i).le (ha i)
    _ = (∑ i, a i * coverValue (residual A (ρ i)) r q) + δ * ∑ i, a i := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    _ ≤ (∑ i, coeff i * r ^ (ρ i).pos.card * coverValue (residual A (ρ i)) r q) + ε := by
      have hid : δ * ((∑ i, a i) + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
      change (∑ i, a i * coverValue (residual A (ρ i)) r q) + δ * ∑ i, a i ≤
        (∑ i, a i * coverValue (residual A (ρ i)) r q) + ε
      nlinarith

theorem restriction_card (ρ : Restriction V) : ρ.support.card = ρ.pos.card + ρ.neg.card :=
  Finset.card_union_of_disjoint ρ.disjoint

theorem restriction_card_le (ρ : Restriction V) : ρ.support.card ≤ V.card :=
  Finset.card_le_card (Finset.union_subset ρ.pos_sub ρ.neg_sub)

theorem normalize_factor (ρ : Restriction V) :
    r ^ ρ.pos.card / p ^ ρ.support.card =
      (2 : ℝ) ^ (-(ρ.pos.card : ℤ)) * q ^ ρ.neg.card := by
  rw [restriction_card, r, q, div_pow, div_pow, pow_add, zpow_neg, zpow_natCast]
  field_simp [ne_of_gt p_pos]
  simp

theorem normalize_power (ρ : Restriction V) (c w : ℝ) :
    (c * r ^ ρ.pos.card * (w * p ^ (V.card - ρ.support.card))) / p ^ V.card =
      c * w * r ^ ρ.pos.card / p ^ ρ.support.card := by
  have hc := Nat.sub_add_cancel (restriction_card_le ρ)
  conv_lhs => arg 2; rw [← hc, pow_add]
  field_simp [ne_of_gt p_pos]
  <;> ring

theorem normalized_bound (V : Finset α) (A : Family α)
    (hA : ∀ S ∈ A, S ⊆ V) {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff : Fin k → ℝ) (hcoeff : ∀ i, 0 ≤ coeff i)
    (hc : ∀ S ∈ A, 1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
      coeff i * q ^ (S ∩ (ρ i).neg).card)
    (omega : Fin k → ℝ)
    (hw : ∀ i, coverValue (residual A (ρ i)) r q ≤
      omega i * p ^ (V.card - (ρ i).support.card)) :
    coverValue A r q / p ^ V.card ≤
      ∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card := by
  calc
    coverValue A r q / p ^ V.card ≤
        (∑ i, coeff i * r ^ (ρ i).pos.card * coverValue (residual A (ρ i)) r q) / p ^ V.card :=
      div_le_div_of_nonneg_right (coverValue_combined_le V A hA ρ coeff hcoeff hc)
        (pow_nonneg p_pos.le _)
    _ ≤ (∑ i, coeff i * r ^ (ρ i).pos.card *
        (omega i * p ^ (V.card - (ρ i).support.card))) / p ^ V.card := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg p_pos.le _)
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hw i)
        (mul_nonneg (hcoeff i) (pow_nonneg r_nonneg _))
    _ = ∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => normalize_power (ρ i) (coeff i) (omega i)

theorem normalized_identity {k : ℕ} (ρ : Fin k → Restriction V)
    (coeff omega : Fin k → ℝ) :
    (∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card) =
      ∑ i, coeff i * omega i * (2 : ℝ) ^ (-((ρ i).pos.card : ℤ)) * q ^ (ρ i).neg.card := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc, normalize_factor]
  ring

theorem combine_restrictions_proof {α : Type} [DecidableEq α] (V : Finset α)
    (A : Family α) (hA : ∀ S ∈ A, S ⊆ V) (k : ℕ)
    (ρ : Fin k → Restriction V) (coeff : Fin k → ℝ)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hc : ∀ S ∈ A,
      1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
        coeff i * q ^ (S ∩ (ρ i).neg).card)
    (f : Fin k → Weight α) (hf : ∀ i, CoverFeasible (residual A (ρ i)) q (f i)) :
    CoverFeasible A q (combinedWeight ρ coeff f) ∧
    cost A r (combinedWeight ρ coeff f) =
      ∑ i, coeff i * r ^ (ρ i).pos.card * cost (residual A (ρ i)) r (f i) ∧
    ∀ omega : Fin k → ℝ,
      (∀ i, coverValue (residual A (ρ i)) r q ≤ omega i * p ^ (V.card - (ρ i).support.card)) →
      coverValue A r q / p ^ V.card ≤
        ∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card ∧
      (∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card) =
        ∑ i, coeff i * omega i * (2 : ℝ) ^ (-((ρ i).pos.card : ℤ)) * q ^ (ρ i).neg.card := by
  exact ⟨combined_feasible V A hA ρ coeff hcoeff hc f hf,
    cost_combined V A hA ρ coeff f hf,
    fun omega hw => ⟨normalized_bound V A hA ρ coeff hcoeff hc omega hw,
      normalized_identity ρ coeff omega⟩⟩

end
end MajorityDepthThree.Exact.CombineProof



open MajorityDepthThree.Exact
open scoped Classical
theorem solution {α : Type} [DecidableEq α] (V : Finset α)
    (A : Family α) (hA : ∀ S ∈ A, S ⊆ V) (k : ℕ)
    (ρ : Fin k → Restriction V) (coeff : Fin k → ℝ)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (hc : ∀ S ∈ A,
      1 ≤ ∑ i ∈ Finset.univ.filter (fun i => Compatible A (ρ i) S),
        coeff i * q ^ (S ∩ (ρ i).neg).card)
    (f : Fin k → Weight α) (hf : ∀ i, CoverFeasible (residual A (ρ i)) q (f i)) :
    CoverFeasible A q (combinedWeight ρ coeff f) ∧
    cost A r (combinedWeight ρ coeff f) =
      ∑ i, coeff i * r ^ (ρ i).pos.card * cost (residual A (ρ i)) r (f i) ∧
    ∀ omega : Fin k → ℝ,
      (∀ i, coverValue (residual A (ρ i)) r q ≤ omega i * p ^ (V.card - (ρ i).support.card)) →
      coverValue A r q / p ^ V.card ≤
        ∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card ∧
      (∑ i, coeff i * omega i * r ^ (ρ i).pos.card / p ^ (ρ i).support.card) =
        ∑ i, coeff i * omega i * (2 : ℝ) ^ (-((ρ i).pos.card : ℤ)) * q ^ (ρ i).neg.card :=
  MajorityDepthThree.Exact.CombineProof.combine_restrictions_proof V A hA k ρ coeff hcoeff hc f hf

#print axioms solution
#print axioms MajorityDepthThree.Exact.CombineProof.coverValue_combined_le
