-- Prove2me | solution 1 for Graham1969.lpt_makespan_le
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T21:26:10.990165+00:00
-- url     : https://prove2.me/submissions/1b6eecb7-ffef-4a8d-b94d-97a002237667

import Mathlib

theorem solution (m n : ℕ) (hm : 0 < m) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsorted : Antitone p) (σ : Fin n → Fin m)
    (hLPT : ∀ i : Fin n, ∀ j : Fin m,
      ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = σ i), p k ≤
        ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = j), p k) :
    Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => σ k = j), p k) ≤
      (4 / 3 - 1 / (3 * (m : ℝ))) *
        Finset.univ.inf' ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
          (fun τ : Fin n → Fin m => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
            (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k)) := by
  have hτex := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Fin n → Fin m)))
    ⟨fun _ => ⟨0, hm⟩, Finset.mem_univ _⟩
    (fun τ : Fin n → Fin m => Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k))
  obtain ⟨τ, _, hτ⟩ := hτex
  have hjsex := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => σ k = j), p k)
  obtain ⟨js, _, hjs⟩ := hjsex
  rw [hτ, hjs]
  beta_reduce
  have hτle : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k ≤
      Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k) :=
    fun j => Finset.le_sup' (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k)
      (Finset.mem_univ j)
  generalize Finset.univ.sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      (fun j : Fin m => ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k) = O at hτle ⊢
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hO0 : 0 ≤ O := le_trans (Finset.sum_nonneg (fun k _ => hp k)) (hτle ⟨0, hm⟩)
  have hpO : ∀ k, p k ≤ O := by
    intro k
    refine le_trans ?_ (hτle (τ k))
    exact Finset.single_le_sum (f := p) (fun i _ => hp i)
      (Finset.mem_filter.2 ⟨Finset.mem_univ k, rfl⟩)
  have hT : ∑ k, p k ≤ m * O := by
    rw [← Finset.sum_fiberwise Finset.univ τ p]
    calc ∑ j, ∑ k ∈ Finset.univ.filter (fun k => τ k = j), p k ≤ ∑ _j : Fin m, O :=
          Finset.sum_le_sum (fun j _ => hτle j)
      _ = m * O := by simp
  have hc1 : (1 : ℝ) ≤ 4 / 3 - 1 / (3 * (m : ℝ)) := by
    have : 1 / (3 * (m : ℝ)) ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  by_cases hne : (Finset.univ.filter (fun k => σ k = js)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
    exact mul_nonneg (by linarith) hO0
  obtain ⟨i, hi⟩ : ∃ i, i = (Finset.univ.filter (fun k => σ k = js)).max' hne := ⟨_, rfl⟩
  have hiσ : σ i = js := by
    have := Finset.max'_mem _ hne
    rw [← hi] at this
    exact (Finset.mem_filter.1 this).2
  have hsplit : Finset.univ.filter (fun k => σ k = js) =
      insert i (Finset.univ.filter (fun k => k < i ∧ σ k = σ i)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      have : k ≤ i := by
        rw [hi]
        exact Finset.le_max' _ k (by simp [hk])
      rcases this.lt_or_eq with h | h
      · exact Or.inr ⟨h, hk.trans hiσ.symm⟩
      · exact Or.inl h
    · rintro (h | ⟨_, h⟩)
      · rw [h, hiσ]
      · rw [h, hiσ]
  rw [hsplit, Finset.sum_insert (by simp)]
  set S := ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = σ i), p k with hSdef
  have hS : (m : ℝ) * S ≤ ∑ k ∈ Finset.univ.filter (fun k => k < i), p k := by
    rw [← Finset.sum_fiberwise (Finset.univ.filter (fun k => k < i)) σ p]
    simp only [Finset.filter_filter]
    calc (m : ℝ) * S = ∑ _j : Fin m, S := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hLPT i j)
  have hlt : ∑ k ∈ Finset.univ.filter (fun k => k < i), p k + p i ≤ ∑ k, p k := by
    rw [add_comm, ← Finset.sum_insert (s := Finset.univ.filter (fun k => k < i)) (by simp)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hp k)
  by_cases hA : 3 * p i ≤ O
  · have h1 : (m : ℝ) * S + p i ≤ m * O := by linarith
    have key : 3 * m * (p i + S) ≤ (4 * m - 1) * O := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ m - 1)]
    have hm0 : (0 : ℝ) < m := by linarith
    have : (4 / 3 - 1 / (3 * (m : ℝ))) * O = (4 * m - 1) * O / (3 * m) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  push_neg at hA
  have hSle : S ≤ O - p i := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ j, O - p i < ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = j), p k :=
      fun j => lt_of_lt_of_le hcon (hLPT i j)
    set f : Fin n → ℝ := fun k => if O - p i < p k then 1 else 1 / 2 with hfdef
    have hf1 : ∀ k, f k ≤ 1 := by
      intro k; simp only [hfdef]; split_ifs <;> norm_num
    have hf2 : ∀ k, 1 / 2 ≤ f k := by
      intro k; simp only [hfdef]; split_ifs <;> norm_num
    have hlow : ∀ j, (1 : ℝ) ≤ ∑ k ∈ Finset.univ.filter (fun k => k < i ∧ σ k = j), f k := by
      intro j
      have hpos := hall j
      set s := Finset.univ.filter (fun k => k < i ∧ σ k = j) with hs
      rcases Nat.lt_or_ge s.card 2 with hc | hc
      · rcases Nat.lt_or_ge s.card 1 with hc1 | hc1
        · have : s = ∅ := Finset.card_eq_zero.1 (by omega)
          rw [this, Finset.sum_empty] at hpos
          linarith [hpO i]
        · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by omega : s.card = 1)
          rw [ha, Finset.sum_singleton] at hpos ⊢
          simp only [hfdef, if_pos hpos, le_refl]
      · have := Finset.card_nsmul_le_sum s f (1 / 2) (fun k _ => hf2 k)
        rw [nsmul_eq_mul] at this
        have : (2 : ℝ) ≤ s.card := by exact_mod_cast hc
        linarith
    have hup : ∀ j, ∑ k ∈ Finset.univ.filter (fun k => k ≤ i ∧ τ k = j), f k ≤ 1 := by
      intro j
      set t := Finset.univ.filter (fun k => k ≤ i ∧ τ k = j) with ht
      have htO : ∑ k ∈ t, p k ≤ O := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hp k)) (hτle j)
        intro k hk
        simp only [ht, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact hk.2
      have hge : ∀ k ∈ t, p i ≤ p k := fun k hk => hsorted (Finset.mem_filter.1 hk).2.1
      have hcard3 : t.card < 3 := by
        have := Finset.card_nsmul_le_sum t p (p i) hge
        rw [nsmul_eq_mul] at this
        by_contra h
        push_neg at h
        have h3 : (3 : ℝ) ≤ t.card := by exact_mod_cast h
        nlinarith [mul_le_mul_of_nonneg_right h3 (hp i)]
      rcases Nat.lt_or_ge t.card 2 with hc | hc
      · have := Finset.sum_le_card_nsmul t f 1 (fun k _ => hf1 k)
        rw [nsmul_eq_mul] at this
        have : (t.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : t.card ≤ 1)
        linarith
      · have hhalf : ∀ k ∈ t, f k = 1 / 2 := by
          intro k hk
          obtain ⟨k', hk', hne⟩ := Finset.exists_mem_ne (by omega : 1 < t.card) k
          have h2 : p k + p k' ≤ O := by
            have hsub : ({k, k'} : Finset (Fin n)) ⊆ t := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            have := Finset.sum_le_sum_of_subset_of_nonneg (f := p) hsub (fun x _ _ => hp x)
            rw [Finset.sum_pair hne.symm] at this
            linarith
          have : ¬ (O - p i < p k) := by
            have := hge k' hk'
            linarith
          simp only [hfdef, if_neg this]
        rw [Finset.sum_congr rfl hhalf, Finset.sum_const, nsmul_eq_mul]
        have : (t.card : ℝ) ≤ 2 := by exact_mod_cast (by omega : t.card ≤ 2)
        linarith
    have h1 : (m : ℝ) ≤ ∑ k ∈ Finset.univ.filter (fun k => k < i), f k := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (fun k => k < i)) σ f]
      simp only [Finset.filter_filter]
      calc (m : ℝ) = ∑ _j : Fin m, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun j _ => hlow j)
    have h2 : ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), f k ≤ m := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (fun k => k ≤ i)) τ f]
      simp only [Finset.filter_filter]
      calc _ ≤ ∑ _j : Fin m, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hup j)
        _ = m := by simp
    have h3 : ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), f k =
        f i + ∑ k ∈ Finset.univ.filter (fun k => k < i), f k := by
      rw [← Finset.sum_insert (by simp)]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      exact ⟨fun h => (h.lt_or_eq).elim Or.inr Or.inl, fun h => h.elim le_of_eq le_of_lt⟩
    linarith [hf2 i]
  have hO : p i + S ≤ O := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hc1 hO0]
