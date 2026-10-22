-- Prove2me | solution 1 for NetworkQuality.PotentialMax.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:16:30.342159+00:00
-- url     : https://prove2.me/submissions/def03e2c-bd73-48ef-b0c3-30a37989f471

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

set_option autoImplicit false
open NetworkQuality.PotentialMax Market

section NQ
variable {n : ℕ} (M : Market n)

lemma nq_u_in (i : Fin n) (B : Finset (Fin n)) (p q : ℝ) (h : i ∈ B) :
    M.u i B p q = M.v i * M.f B.card q - p := by
  unfold Market.u; rw [if_pos h]

lemma nq_u_out (i : Fin n) (B : Finset (Fin n)) (p q : ℝ) (h : i ∉ B) :
    M.u i B p q = 0 := by
  unfold Market.u; rw [if_neg h]

lemma nq_nash_iff (B : Finset (Fin n)) (p q : ℝ) :
    M.IsNash B p q ↔ (∀ i ∈ B, p ≤ M.v i * M.f B.card q) ∧
      (∀ i ∉ B, M.v i * M.f (B.card + 1) q ≤ p) := by
  unfold Market.IsNash
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h1 i hi
      rw [nq_u_out M i _ p q (Finset.notMem_erase i B), nq_u_in M i B p q hi] at this
      linarith
    · have := h2 i hi
      rw [nq_u_in M i _ p q (Finset.mem_insert_self i B), nq_u_out M i B p q hi,
        Finset.card_insert_of_notMem hi] at this
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [nq_u_out M i _ p q (Finset.notMem_erase i B), nq_u_in M i B p q hi]
      linarith [h1 i hi]
    · rw [nq_u_in M i _ p q (Finset.mem_insert_self i B), nq_u_out M i B p q hi,
        Finset.card_insert_of_notMem hi]
      linarith [h2 i hi]

lemma nq_exists_nonmember (B : Finset (Fin n)) (hB : B ≠ Finset.univ) :
    ∃ j ∉ B, j.val ≤ B.card := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∉ B := by
    by_contra h
    push_neg at h
    exact hB (Finset.eq_univ_iff_forall.mpr h)
  have h1 : B.card < j0.val := hcon j0 hj0
  have h2 : j0.val < n := j0.isLt
  have hle : (Finset.univ : Finset (Fin (B.card + 1))).card ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun k => (⟨k.val, by omega⟩ : Fin n)) ?_ ?_
    · intro k _
      by_contra hk
      have h3 : B.card < k.val := hcon ⟨k.val, by omega⟩ hk
      have h4 := k.isLt
      omega
    · intro a _ b _ hab
      exact Fin.ext (by simpa using hab)
  simp at hle

lemma nq_exists_member (B : Finset (Fin n)) (hB : B.Nonempty) :
    ∃ b ∈ B, B.card ≤ b.val + 1 := by
  refine ⟨B.max' hB, Finset.max'_mem B hB, ?_⟩
  have hsub : B ⊆ Finset.Iic (B.max' hB) := fun x hx => by
    simpa using Finset.le_max' B x hx
  have := Finset.card_le_card hsub
  simpa using this

end NQ

theorem solution {n : ℕ} (M : Market n) (hM : M.Standing) (q : ℝ) (hq : 0 ≤ q)
    (hs : M.StrongNE q) (p : ℝ) :
    (p < M.v ⟨0, hM.1⟩ * M.f 1 q →
      ∀ B : Finset (Fin n), M.IsNash B p q ↔ B = Finset.univ) ∧
    (M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q < p →
      ∀ B : Finset (Fin n), M.IsNash B p q ↔ B = ∅) ∧
    (M.v ⟨0, hM.1⟩ * M.f 1 q ≤ p → p ≤ M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q →
      ∀ B : Finset (Fin n), M.IsNash B p q ↔ (B = Finset.univ ∨ B = ∅)) := by
  have hv : ∀ i, 0 < M.v i := hM.2.1
  have hanti : Antitone M.v := hM.2.2.1
  have hf0 : ∀ k : ℕ, 1 ≤ k → 0 ≤ M.f k q := fun k hk => hM.2.2.2.1 k q hk hq
  have hfm : ∀ a b : ℕ, 1 ≤ a → a ≤ b → M.f a q ≤ M.f b q := fun a b ha hab =>
    hM.2.2.2.2.1 q hq (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (le_trans ha hab)) hab
  have hn1 : 1 ≤ n := hM.1
  set i0 : Fin n := ⟨0, hM.1⟩ with hi0
  set iN : Fin n := ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ with hiN
  have hgs : StrictMono (fun i : Fin n => M.v i * M.f (i.val + 1) q) := hs
  have hg0 : M.v i0 * M.f 1 q = M.v i0 * M.f (i0.val + 1) q := rfl
  have hgN : M.v iN * M.f n q = M.v iN * M.f (iN.val + 1) q := by
    show _ = M.v iN * M.f ((n - 1) + 1) q
    rw [Nat.sub_add_cancel hn1]
  have hlo : ∀ i : Fin n, M.v i0 * M.f 1 q ≤ M.v i * M.f (i.val + 1) q := by
    intro i
    rw [hg0]
    exact hgs.monotone (by simp [hi0, Fin.le_def])
  have hhi : ∀ i : Fin n, M.v i * M.f (i.val + 1) q ≤ M.v iN * M.f n q := by
    intro i
    rw [hgN]
    exact hgs.monotone (by simp only [hiN, Fin.le_def]; omega)
  have hup : ∀ i : Fin n, M.v i * M.f (i.val + 1) q ≤ M.v i * M.f n q := by
    intro i
    exact mul_le_mul_of_nonneg_left (hfm _ _ (by omega) (by have := i.isLt; omega)) (hv i).le
  have hdown : ∀ i : Fin n, M.v i * M.f 1 q ≤ M.v i * M.f (i.val + 1) q := by
    intro i
    exact mul_le_mul_of_nonneg_left (hfm _ _ le_rfl (by omega)) (hv i).le
  refine ⟨?_, ?_, ?_⟩
  · intro hp B
    rw [nq_nash_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hne
      obtain ⟨j, hj, hjk⟩ := nq_exists_nonmember B hne
      have h3 := h2 j hj
      have hh : M.v j * M.f (j.val + 1) q ≤ M.v j * M.f (B.card + 1) q :=
        mul_le_mul_of_nonneg_left (hfm _ _ (by omega) (by omega)) (hv j).le
      linarith [hlo j]
    · rintro rfl
      refine ⟨fun i _ => ?_, fun i hi => absurd (Finset.mem_univ i) hi⟩
      rw [Finset.card_univ, Fintype.card_fin]
      linarith [hlo i, hup i]
  · intro hp B
    rw [nq_nash_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hne
      obtain ⟨b, hb, hbk⟩ := nq_exists_member B (Finset.nonempty_iff_ne_empty.mpr hne)
      have hk1 : 1 ≤ B.card := Finset.card_pos.mpr ⟨b, hb⟩
      have h3 := h1 b hb
      have hh : M.v b * M.f B.card q ≤ M.v b * M.f (b.val + 1) q :=
        mul_le_mul_of_nonneg_left (hfm _ _ hk1 hbk) (hv b).le
      linarith [hhi b]
    · rintro rfl
      refine ⟨fun i hi => absurd hi (Finset.notMem_empty i), fun i _ => ?_⟩
      rw [Finset.card_empty, zero_add]
      linarith [hdown i, hhi i]
  · intro hp1 hp2 B
    rw [nq_nash_iff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hB0 : B = ∅
      · exact Or.inr hB0
      by_cases hBu : B = Finset.univ
      · exact Or.inl hBu
      exfalso
      have hk1 : 1 ≤ B.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB0)
      have hkn : B.card < n := by
        have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hBu)
        simpa using this
      obtain ⟨j, hj, hjk⟩ := nq_exists_nonmember B hBu
      obtain ⟨b, hb, hbk⟩ := nq_exists_member B (Finset.nonempty_iff_ne_empty.mpr hB0)
      set ik : Fin n := ⟨B.card, hkn⟩ with hik
      set ik1 : Fin n := ⟨B.card - 1, by omega⟩ with hik1
      have hlt : ik1 < ik := by simp only [hik, hik1, Fin.lt_def]; omega
      have hs2 : M.v ik1 * M.f (ik1.val + 1) q < M.v ik * M.f (ik.val + 1) q := hgs hlt
      have e1 : M.f (ik1.val + 1) q = M.f B.card q := by
        show M.f ((B.card - 1) + 1) q = _
        rw [Nat.sub_add_cancel hk1]
      have e2 : M.f (ik.val + 1) q = M.f (B.card + 1) q := rfl
      rw [e1, e2] at hs2
      have a1 : M.v ik * M.f (B.card + 1) q ≤ M.v j * M.f (B.card + 1) q :=
        mul_le_mul_of_nonneg_right (hanti (by simp only [hik, Fin.le_def]; omega)) (hf0 _ (by omega))
      have a2 : M.v b * M.f B.card q ≤ M.v ik1 * M.f B.card q :=
        mul_le_mul_of_nonneg_right (hanti (by simp only [hik1, Fin.le_def]; omega)) (hf0 _ hk1)
      have a3 := h2 j hj
      have a4 := h1 b hb
      linarith
    · rintro (rfl | rfl)
      · refine ⟨fun i _ => ?_, fun i hi => absurd (Finset.mem_univ i) hi⟩
        rw [Finset.card_univ, Fintype.card_fin]
        have : M.v iN * M.f n q ≤ M.v i * M.f n q :=
          mul_le_mul_of_nonneg_right (hanti (by simp only [hiN, Fin.le_def]; omega)) (hf0 n hn1)
        linarith
      · refine ⟨fun i hi => absurd hi (Finset.notMem_empty i), fun i _ => ?_⟩
        rw [Finset.card_empty, zero_add]
        have : M.v i * M.f 1 q ≤ M.v i0 * M.f 1 q :=
          mul_le_mul_of_nonneg_right (hanti (by simp only [hi0, Fin.le_def]; omega)) (hf0 1 le_rfl)
        linarith
