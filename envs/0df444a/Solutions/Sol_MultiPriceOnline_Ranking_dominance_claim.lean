-- Prove2me | solution 1 for MultiPriceOnline.Ranking.dominance_claim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:25:32.536792+00:00
-- url     : https://prove2.me/submissions/d25158fe-c1e1-4dbe-bf8e-dca7ed89c4b7

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

open MultiPriceOnline.Ranking Finset

private lemma offer_some_spec {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ} {A : Finset (Fin n)} {c : Fin n}
    (ho : offer m r α sel t q W A = some c) :
    c ∈ A ∧ 0 < score m r α q W c ∧ ∀ x ∈ A, score m r α q W x ≤ score m r α q W c := by
  unfold offer at ho
  split_ifs at ho with hA hpos
  injection ho with heq
  subst heq
  have h := hsel t A hA (score m r α q W)
  exact ⟨h.1, hpos, h.2⟩

private lemma offer_none_spec {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ} {A : Finset (Fin n)}
    (ho : offer m r α sel t q W A = none) :
    ∀ x ∈ A, score m r α q W x ≤ 0 := by
  intro x hx
  have hA : A.Nonempty := ⟨x, hx⟩
  unfold offer at ho
  rw [dif_pos hA] at ho
  split_ifs at ho with hpos
  have h := (hsel t A hA (score m r α q W)).2 x hx
  linarith

private lemma offer_eq_none_of_subset {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ} {B C : Finset (Fin n)} (hBC : B ⊆ C)
    (hoC : offer m r α sel t q W C = none) :
    offer m r α sel t q W B = none := by
  have hle := offer_none_spec hsel hoC
  unfold offer
  split_ifs with hB hpos
  · have hb_in : sel t B hB (score m r α q W) ∈ B := (hsel t B hB (score m r α q W)).1
    have hle_b := hle _ (hBC hb_in)
    linarith
  · rfl
  · rfl

private lemma offer_eq_some_of_subset {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {p : Fin T → Fin n → ℕ → ℝ} {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {W : Fin n → ℝ} (hNT : NoTies m r α p W)
    {t : Fin T} {B C : Finset (Fin n)} (hBC : B ⊆ C) {c : Fin n}
    (hoC : offer m r α sel t (p t) W C = some c) (hcB : c ∈ B) :
    offer m r α sel t (p t) W B = some c := by
  have hc_spec := offer_some_spec hsel hoC
  have hB : B.Nonempty := ⟨c, hcB⟩
  set b := sel t B hB (score m r α (p t) W)
  have hb_spec := hsel t B hB (score m r α (p t) W)
  have hsc_cb : score m r α (p t) W c ≤ score m r α (p t) W b := hb_spec.2 c hcB
  have hsc_bc : score m r α (p t) W b ≤ score m r α (p t) W c := hc_spec.2.2 b (hBC hb_spec.1)
  have hpos_b : 0 < score m r α (p t) W b := lt_of_lt_of_le hc_spec.2.1 hsc_cb
  have h_eq : b = c := by
    by_contra hne
    have h_ne_sc := hNT t b c hne hpos_b
    exact h_ne_sc (le_antisymm hsc_bc hsc_cb)
  unfold offer
  rw [dif_pos hB, if_pos hpos_b]
  exact congrArg some h_eq

private lemma availBefore_erase_of_not_offered {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {p : Fin T → Fin n → ℕ → ℝ} {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {W : Fin n → ℝ} (hNT : NoTies m r α p W) (t : Fin T) (i : Fin n)
    (hnot : ∀ s : Fin T, s ≤ t → run2 m r α p sel univ W s ≠ some i) :
    ∀ s : ℕ, s ≤ t.val →
      i ∈ availBefore m r α p sel univ W s ∧
      availBefore m r α p sel (univ.erase i) W s = (availBefore m r α p sel univ W s).erase i := by
  intro s
  induction s with
  | zero =>
    intro _
    exact ⟨mem_univ i, rfl⟩
  | succ s ih =>
    intro hs1
    have hs_le : s ≤ t.val := Nat.le_of_succ_le hs1
    have hsT : s < T := lt_of_le_of_lt hs_le t.isLt
    obtain ⟨hiC, hBC⟩ := ih hs_le
    set t₀ : Fin T := ⟨s, hsT⟩
    have ht₀_le : t₀ ≤ t := Nat.le_of_succ_le hs1
    have hnot₀ : offer m r α sel t₀ (p t₀) W (availBefore m r α p sel univ W s) ≠ some i :=
      hnot t₀ ht₀_le
    set C := availBefore m r α p sel univ W s
    set B := availBefore m r α p sel (univ.erase i) W s
    have hBC_sub : B ⊆ C := hBC ▸ erase_subset i C
    unfold availBefore
    rw [dif_pos hsT, dif_pos hsT]
    change i ∈ (match offer m r α sel t₀ (p t₀) W C with | some j => C.erase j | none => C) ∧
      (match offer m r α sel t₀ (p t₀) W B with | some j => B.erase j | none => B) =
        (match offer m r α sel t₀ (p t₀) W C with | some j => C.erase j | none => C).erase i
    rcases hoC : offer m r α sel t₀ (p t₀) W C with _ | c
    · have hoB := offer_eq_none_of_subset hsel hBC_sub hoC
      rw [hoB]
      exact ⟨hiC, hBC⟩
    · have hci : c ≠ i := fun h => hnot₀ (by rw [hoC, h])
      have hcC : c ∈ C := (offer_some_spec hsel hoC).1
      have hcB : c ∈ B := by
        rw [hBC, mem_erase]
        exact ⟨hci, hcC⟩
      have hoB := offer_eq_some_of_subset hsel hNT hBC_sub hoC hcB
      rw [hoB]
      refine ⟨mem_erase.mpr ⟨hci.symm, hiC⟩, ?_⟩
      rw [hBC, erase_right_comm]

theorem solution {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (_hr : ∀ i, IsPriceSet (m i) (r i))
    (_hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (_hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (_hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1) (hNT : NoTies m r α p W)
    (t : Fin T) (i : Fin n) (_hj : 1 ≤ jt m (p t) i)
    (hcrit : Phi (m i) (r i) (α i) (W i) <
      MultiPriceOnline.Balance.pr (r i) (jt m (p t) i) - Zt m r α p sel (Finset.univ.erase i) W t) :
    ∃ s : Fin T, s ≤ t ∧ run2 m r α p sel Finset.univ W s = some i := by
  by_contra h_no
  have h_no' : ∀ s : Fin T, s ≤ t → run2 m r α p sel univ W s ≠ some i :=
    fun s hs h => h_no ⟨s, hs, h⟩
  obtain ⟨hiC, hBC⟩ := availBefore_erase_of_not_offered hsel hNT t i h_no' t.val le_rfl
  set C := availBefore m r α p sel univ W t.val
  set B := availBefore m r α p sel (univ.erase i) W t.val
  have hBC_sub : B ⊆ C := hBC ▸ erase_subset i C
  have hZ_lt : Zt m r α p sel (univ.erase i) W t < score m r α (p t) W i := by
    unfold score
    linarith
  have hZ_nonneg : 0 ≤ Zt m r α p sel (univ.erase i) W t := by
    unfold Zt run2
    change 0 ≤ match offer m r α sel t (p t) W B with | some j => score m r α (p t) W j | none => 0
    rcases hoB : offer m r α sel t (p t) W B with _ | b
    · exact le_rfl
    · exact le_of_lt (offer_some_spec hsel hoB).2.1
  have hsc_pos : 0 < score m r α (p t) W i := lt_of_le_of_lt hZ_nonneg hZ_lt
  have hnot_t : offer m r α sel t (p t) W C ≠ some i := h_no' t le_rfl
  rcases hoC : offer m r α sel t (p t) W C with _ | c
  · have hle0 := offer_none_spec hsel hoC i hiC
    linarith
  · have hc_spec := offer_some_spec hsel hoC
    have hci : c ≠ i := fun h => hnot_t (by rw [hoC, h])
    have hcB : c ∈ B := by
      rw [hBC, mem_erase]
      exact ⟨hci, hc_spec.1⟩
    have hoB := offer_eq_some_of_subset hsel hNT hBC_sub hoC hcB
    have hZ_eq : Zt m r α p sel (univ.erase i) W t = score m r α (p t) W c := by
      unfold Zt run2
      change (match offer m r α sel t (p t) W B with | some j => score m r α (p t) W j | none => 0) = _
      rw [hoB]
    have hsc_le : score m r α (p t) W i ≤ score m r α (p t) W c := hc_spec.2.2 i hiC
    linarith
