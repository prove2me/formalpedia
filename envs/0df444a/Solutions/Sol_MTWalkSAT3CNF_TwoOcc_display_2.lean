-- Prove2me | solution 1 for MTWalkSAT3CNF.TwoOcc.display_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T14:18:31.946992+00:00
-- url     : https://prove2.me/submissions/6ad19d38-15be-4d95-b659-2330bf2b1651

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Potential

set_option autoImplicit false

open MTWalkSAT3CNF.TwoOcc

namespace D2Aux

lemma gen {m : ℕ} (P Q : Fin m → Prop) [DecidablePred P] [DecidablePred Q]
    (cw : Fin m → ℝ) (K : Fin m → Finset (Fin m))
    (hnn : ∀ r, 0 ≤ cw r) (hle : ∀ r, cw r ≤ (K r).card)
    (hex : ∀ r, ¬ (P r ∧ Q r))
    (huniq : ∀ v r1 r2, (P r1 ∨ Q r1) → (P r2 ∨ Q r2) → v ∈ K r1 → v ∈ K r2 → r1 = r2) :
    0 ≤ (∑ r, if P r then cw r else 0) + (1 / 4 : ℝ) * ∑ r, (if Q r then cw r else 0) ∧
    (∑ r, if P r then cw r else 0) + (1 / 4 : ℝ) * ∑ r, (if Q r then cw r else 0) ≤ m := by
  have hP : ∀ r, 0 ≤ (if P r then cw r else 0) := fun r => by
    split_ifs
    · exact hnn r
    · exact le_refl 0
  have hQ : ∀ r, 0 ≤ (if Q r then cw r else 0) := fun r => by
    split_ifs
    · exact hnn r
    · exact le_refl 0
  have s1 := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => hP r)
  have s2 := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => hQ r)
  refine ⟨by linarith, ?_⟩
  have hterm : ∀ r, (if P r then cw r else 0) + (if Q r then cw r else 0)
      ≤ ∑ v, (if v ∈ K r ∧ (P r ∨ Q r) then (1 : ℝ) else 0) := by
    intro r
    by_cases hpq : P r ∨ Q r
    · have hc : ∑ v, (if v ∈ K r ∧ (P r ∨ Q r) then (1 : ℝ) else 0) = (K r).card := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 2
        ext v
        simp [hpq]
      rw [hc]
      rcases hpq with hp | hq
      · rw [if_pos hp, if_neg (fun hq => hex r ⟨hp, hq⟩)]
        linarith [hle r]
      · rw [if_neg (fun hp => hex r ⟨hp, hq⟩), if_pos hq]
        linarith [hle r]
    · rw [if_neg (fun h => hpq (Or.inl h)), if_neg (fun h => hpq (Or.inr h)), add_zero]
      exact Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hterm r)
  rw [Finset.sum_comm] at hsum
  have hinner : ∀ v, ∑ r, (if v ∈ K r ∧ (P r ∨ Q r) then (1 : ℝ) else 0) ≤ 1 := by
    intro v
    by_cases hex' : ∃ r0, v ∈ K r0 ∧ (P r0 ∨ Q r0)
    · obtain ⟨r0, h0⟩ := hex'
      rw [Finset.sum_eq_single r0]
      · exact (if_pos h0).le
      · intro r _ hr
        rw [if_neg]
        intro h
        exact hr (huniq v r r0 h.2 h0.2 h.1 h0.1)
      · intro h
        exact absurd (Finset.mem_univ r0) h
    · rw [Finset.sum_eq_zero (fun r _ => if_neg (fun h => hex' ⟨r, h⟩))]
      norm_num
  have htot := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hinner v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at htot
  rw [Finset.sum_add_distrib] at hsum
  linarith

end D2Aux

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ} (F : Formula V m)
    (hΔ : MaxOccLeTwo F) (hopp : OppositeSign F) (σ : V → Bool) :
    0 ≤ potential F σ ∧ potential F σ ≤ m := by
  classical
  have cw_nn : ∀ r, 0 ≤ compWeight F σ r := by
    intro r
    unfold compWeight distWeight
    exact Finset.sum_nonneg (fun v _ => pow_nonneg (by norm_num) _)
  have cw_le : ∀ r, compWeight F σ r ≤ ((comp F σ r).card : ℝ) := by
    intro r
    unfold compWeight distWeight
    calc ∑ v ∈ comp F σ r, (1 / 2 : ℝ) ^ (outsideGraph F σ).dist r v
        ≤ ∑ v ∈ comp F σ r, (1 : ℝ) :=
          Finset.sum_le_sum (fun v _ => pow_le_one₀ (by norm_num) (by norm_num))
      _ = _ := by simp
  have mem_comp : ∀ r v, v ∈ comp F σ r ↔ ¬ InA F σ r ∧ (outsideGraph F σ).Reachable r v := by
    intro r v
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
  have notA : ∀ r, numTrue σ (F r) = 0 → ¬ InA F σ r := by
    intro r h hA
    unfold InA at hA
    omega
  have self_mem : ∀ r, ¬ InA F σ r → r ∈ comp F σ r := fun r h =>
    (mem_comp r r).mpr ⟨h, SimpleGraph.Reachable.refl r⟩
  have same_comp : ∀ r1 r2 v, v ∈ comp F σ r1 → v ∈ comp F σ r2 →
      comp F σ r1 = comp F σ r2 := by
    intro r1 r2 v h1 h2
    rw [mem_comp] at h1 h2
    have h12 : (outsideGraph F σ).Reachable r1 r2 := h1.2.trans h2.2.symm
    ext x
    rw [mem_comp, mem_comp]
    constructor
    · rintro ⟨_, hx⟩
      exact ⟨h2.1, h12.symm.trans hx⟩
    · rintro ⟨_, hx⟩
      exact ⟨h1.1, h12.trans hx⟩
  unfold potential
  refine D2Aux.gen _ _ (compWeight F σ) (comp F σ) cw_nn cw_le ?_ ?_
  · rintro r ⟨⟨_, hA⟩, ⟨_, hB, _⟩⟩
    obtain ⟨-, hu1, -⟩ := hA
    obtain ⟨-, hu0, -⟩ := hB
    omega
  · intro v r1 r2 h1 h2 hv1 hv2
    have hK := same_comp r1 r2 v hv1 hv2
    have hn1 : ¬ InA F σ r1 := by
      rcases h1 with h | h
      · exact notA r1 h.1
      · exact h.1
    have hn2 : ¬ InA F σ r2 := by
      rcases h2 with h | h
      · exact notA r2 h.1
      · exact h.1
    have m1 : r1 ∈ comp F σ r1 := self_mem r1 hn1
    have m2 : r2 ∈ comp F σ r1 := by
      rw [hK]
      exact self_mem r2 hn2
    rcases h1 with ⟨u1, d1⟩ | ⟨_, b1, p1, l1, bd1⟩ <;>
      rcases h2 with ⟨u2, d2⟩ | ⟨_, b2, p2, l2, bd2⟩
    · obtain ⟨-, hu, -⟩ := d1
      unfold unsatCount at hu
      exact Finset.card_le_one.mp hu.le r1
        (by simp only [Finset.mem_filter]; exact ⟨m1, u1⟩) r2
        (by simp only [Finset.mem_filter]; exact ⟨m2, u2⟩)
    · exfalso
      obtain ⟨-, hu, -⟩ := d1
      obtain ⟨-, hu', -⟩ := b2
      rw [hK] at hu
      omega
    · exfalso
      obtain ⟨-, hu, -⟩ := b1
      obtain ⟨-, hu', -⟩ := d2
      rw [hK] at hu
      omega
    · obtain ⟨-, -, hb⟩ := b1
      unfold trueBoundaryCount at hb
      have := Finset.card_le_one.mp hb.le (r1, p1)
        (by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
            exact ⟨m1, l1, bd1⟩) (r2, p2)
        (by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
            exact ⟨m2, l2, bd2⟩)
      exact congrArg Prod.fst this
