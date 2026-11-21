-- Prove2me | solution 1 for IsRandomnessNecessaryADA.Plain.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:31:00.743377+00:00
-- url     : https://prove2.me/submissions/512330d5-4ec0-42c5-831e-3c07a1bd5b05

import Definitions.Def_IsRandomnessNecessaryADA_Plain_Survivors

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L31

open IsRandomnessNecessaryADA.Plain

noncomputable def qT {N : ℕ} (T : Finset (Fin N)) : BooleanQuery (Fin N) :=
  fun x => decide (x ∈ T)

theorem mean_qT (N : ℕ) (hN : 0 < N) (T : Finset (Fin N)) :
    populationMean (uniformFin N hN) (liftQuery (qT T)) = (T.card : ℝ) / N := by
  classical
  have hp : ∀ x, ((uniformFin N hN) x).toReal = 1 / (N : ℝ) := by
    intro x
    unfold uniformFin
    simp [PMF.uniformOfFintype_apply]
  unfold populationMean
  simp only [hp]
  have : ∀ x : Fin N, (liftQuery (qT T) x).val = if x ∈ T then 1 else 0 := by
    intro x; simp [liftQuery, qT, bitValue]
  simp only [this]
  simp [Finset.sum_ite_mem, Finset.mul_sum]
  field_simp


theorem common_card {N n : ℕ} (H : Finset (Fin n → Fin N)) :
    (8 / 10 : ℝ) * H.card * (commonPoints H).card ≤ n * H.card := by
  classical
  set C := commonPoints H with hC
  have h1 : ∀ i ∈ C, (8 / 10 : ℝ) * H.card ≤ ((H.filter (fun s => ∃ t, s t = i)).card : ℝ) := by
    intro i hi
    simpa [hC, commonPoints] using hi
  have h2 : (C.card : ℝ) * ((8 / 10 : ℝ) * H.card) ≤
      ∑ i ∈ C, ((H.filter (fun s => ∃ t, s t = i)).card : ℝ) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ h1
  have h3 : ∑ i ∈ C, ((H.filter (fun s => ∃ t, s t = i)).card : ℝ) =
      ∑ s ∈ H, ((C.filter (fun i => ∃ t, s t = i)).card : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  have h4 : ∀ s ∈ H, ((C.filter (fun i => ∃ t, s t = i)).card : ℝ) ≤ n := by
    intro s _
    have : C.filter (fun i => ∃ t, s t = i) ⊆ Finset.univ.image s := by
      intro i hi
      obtain ⟨t, ht⟩ := (Finset.mem_filter.1 hi).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, ht⟩
    have h5 := (Finset.card_le_card this).trans (Finset.card_image_le (s := Finset.univ) (f := s))
    simp only [Finset.card_univ, Fintype.card_fin] at h5
    exact_mod_cast h5
  have h6 : ∑ s ∈ H, ((C.filter (fun i => ∃ t, s t = i)).card : ℝ) ≤ ∑ s ∈ H, (n : ℝ) :=
    Finset.sum_le_sum h4
  simp only [Finset.sum_const, nsmul_eq_mul] at h6
  nlinarith


theorem chain {α : Type} [DecidableEq α] (C : Finset α) (b : Finset α → Prop) (S : Finset α)
    (h0 : b C) (h1 : ¬ b (C ∪ S)) :
    ∃ S' z, S' ⊆ S ∧ z ∈ S ∧ z ∉ S' ∧ b (C ∪ S') ∧ ¬ b (C ∪ insert z S') := by
  induction S using Finset.induction_on with
  | empty => exact absurd (by simpa using h0) h1
  | insert z S'' hz ih =>
    by_cases hb : b (C ∪ S'')
    · exact ⟨S'', z, Finset.subset_insert _ _, Finset.mem_insert_self _ _, hz, hb, h1⟩
    · obtain ⟨S', z', hS', hz', hz'', hb1, hb2⟩ := ih hb
      exact ⟨S', z', hS'.trans (Finset.subset_insert _ _), Finset.mem_insert_of_mem hz', hz'', hb1, hb2⟩

end IsRandomnessNecessaryADA.Plain.Dev.L31

namespace IsRandomnessNecessaryADA.Plain

theorem chk_lemma_3_1 (n : ℕ) (hn : 0 < n)
    (m : Mechanism (Fin (20 * n)) n) (hm : IsNatural m)
    (T : Transcript (StatisticalQuery (Fin (20 * n))))
    (hT : (survivors m T).Nonempty) :
    ∃ q : BooleanQuery (Fin (20 * n)),
      SeparatesAccurate m T (uniformFin (20 * n) (by omega)) (liftQuery q) := by
  classical
  have hNpos : 0 < 20 * n := by omega
  set H := survivors m T with hH
  have hhpos : (0 : ℝ) < H.card := by exact_mod_cast hT.card_pos
  by_contra hns
  have hns' : ∀ q : BooleanQuery (Fin (20 * n)), ∃ a : ℝ,
      |a - populationMean (uniformFin (20 * n) hNpos) (liftQuery q)| ≤ 1 / 10 ∧
        (9 / 10 : ℝ) * H.card < (nextSurvivors m T (liftQuery q) a).card := by
    intro q
    by_contra hq
    push_neg at hq
    exact hns ⟨q, fun a ha => hq a ha⟩
  set C := commonPoints H with hC
  have hCcard : (C.card : ℝ) ≤ 5 / 4 * n := by
    have := Dev.L31.common_card H
    have h2 : (8 / 10 : ℝ) * (C.card : ℝ) ≤ n := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    linarith
  let b : Finset (Fin (20 * n)) → Prop := fun T' => ∃ a : ℝ, a ≤ 1 / 2 ∧
    |a - populationMean (uniformFin (20 * n) hNpos) (liftQuery (Dev.L31.qT T'))| ≤ 1 / 10 ∧
      (9 / 10 : ℝ) * H.card < (nextSurvivors m T (liftQuery (Dev.L31.qT T')) a).card
  have hN : (0 : ℝ) < ((20 * n : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hb0 : b C := by
    obtain ⟨a, ha, hbig⟩ := hns' (Dev.L31.qT C)
    refine ⟨a, ?_, ha, hbig⟩
    rw [Dev.L31.mean_qT] at ha
    have hmean : (C.card : ℝ) / ((20 * n : ℕ) : ℝ) ≤ 1 / 16 := by
      rw [div_le_iff₀ hN]; push_cast; nlinarith
    have := (abs_le.1 ha).2
    linarith
  have hb1 : ¬ b (C ∪ (Finset.univ \ C)) := by
    rintro ⟨a, ha1, ha, _⟩
    rw [Dev.L31.mean_qT] at ha
    have : C ∪ (Finset.univ \ C) = Finset.univ := by simp
    rw [this] at ha
    simp only [Finset.card_univ, Fintype.card_fin] at ha
    rw [div_self hN.ne'] at ha
    have := (abs_le.1 ha).1
    linarith
  obtain ⟨S', z, hS', hz, hzS', hbS, hnb⟩ := Dev.L31.chain C b (Finset.univ \ C) hb0 hb1
  have hzC : z ∉ C := (Finset.mem_sdiff.1 hz).2
  obtain ⟨a1, ha1, _, hbig1⟩ := hbS
  obtain ⟨a2, ha2, hbig2⟩ := hns' (Dev.L31.qT (C ∪ insert z S'))
  have ha2' : 1 / 2 < a2 := by
    by_contra hcon
    exact hnb ⟨a2, not_lt.1 hcon, ha2, hbig2⟩
  set W1 := nextSurvivors m T (liftQuery (Dev.L31.qT (C ∪ S'))) a1 with hW1
  set W2 := nextSurvivors m T (liftQuery (Dev.L31.qT (C ∪ insert z S'))) a2 with hW2
  have hW1H : W1 ⊆ H := fun s hs => (Finset.mem_filter.1 hs).1
  have hW2H : W2 ⊆ H := fun s hs => (Finset.mem_filter.1 hs).1
  have hsub : W1 ∩ W2 ⊆ H.filter (fun s => ∃ t, s t = z) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_inter.1 hs
    refine Finset.mem_filter.2 ⟨hW1H hs1, ?_⟩
    by_contra hcon
    push_neg at hcon
    have h1 : m s T (liftQuery (Dev.L31.qT (C ∪ S'))) = a1 := (Finset.mem_filter.1 hs1).2
    have h2 : m s T (liftQuery (Dev.L31.qT (C ∪ insert z S'))) = a2 := (Finset.mem_filter.1 hs2).2
    have h3 := hm s T (liftQuery (Dev.L31.qT (C ∪ S'))) (liftQuery (Dev.L31.qT (C ∪ insert z S')))
      (fun t => by
        have := hcon t
        simp [liftQuery, Dev.L31.qT, Finset.mem_union, Finset.mem_insert, this])
    linarith
  have hcard1 : ((W1 ∩ W2).card : ℝ) ≤ ((H.filter (fun s => ∃ t, s t = z)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hnc : ((H.filter (fun s => ∃ t, s t = z)).card : ℝ) < (8 / 10 : ℝ) * H.card := by
    by_contra hcon
    push_neg at hcon
    apply hzC
    simpa [hC, commonPoints] using hcon
  have hu : ((W1 ∪ W2).card : ℝ) ≤ H.card := by
    exact_mod_cast Finset.card_le_card (Finset.union_subset hW1H hW2H)
  have hi : ((W1 ∪ W2).card : ℝ) + (W1 ∩ W2).card = W1.card + W2.card := by
    exact_mod_cast Finset.card_union_add_card_inter W1 W2
  linarith

end IsRandomnessNecessaryADA.Plain
end

theorem solution : type_of% @IsRandomnessNecessaryADA.Plain.chk_lemma_3_1 := @IsRandomnessNecessaryADA.Plain.chk_lemma_3_1
