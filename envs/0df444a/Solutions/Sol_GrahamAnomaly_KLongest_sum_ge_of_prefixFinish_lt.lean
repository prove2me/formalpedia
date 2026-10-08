-- Prove2me | solution 1 for GrahamAnomaly.KLongest.sum_ge_of_prefixFinish_lt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:58:28.148123+00:00
-- url     : https://prove2.me/submissions/c300a5e8-6282-49ae-92c9-9e923c775e40

import Mathlib
import Definitions.Def_GrahamAnomaly_KLongest_Model



namespace GrahamAnomaly.KLongest

open WilliamsonShmoys

lemma kl_sum_load {r n : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r) (σ : Fin r → Fin n) (k : ℕ) :
    ∑ p, loadBefore μ L σ k p = ∑ j ∈ Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < k), μ j := by
  unfold loadBefore
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : (L.symm j : ℕ) < k <;> simp [h]

lemma kl_machine_sum {r n : ℕ} (μ : Fin r → ℝ) (τ : Fin r → Fin n) :
    ∑ p, machineLoad μ τ p = ∑ j, μ j := by
  unfold machineLoad
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Finset.sum_ite_eq]

lemma kl_makespan_ge_avg {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ) (τ : Fin r → Fin n) :
    (1 / (n : ℝ)) * ∑ j, μ j ≤ makespan μ τ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  unfold makespan
  rw [dif_pos h]
  have h1 : ∑ p, machineLoad μ τ p ≤ (Finset.univ : Finset (Fin n)).card • Finset.univ.sup' h (machineLoad μ τ) :=
    Finset.sum_le_card_nsmul _ _ _ (fun p _ => Finset.le_sup' (machineLoad μ τ) (Finset.mem_univ p))
  rw [kl_machine_sum] at h1
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [one_div, inv_mul_le_iff₀ hn']
  linarith

lemma kl_load_le {r n : ℕ} (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) (k : ℕ) (p : Fin n) : loadBefore μ L σ k p ≤ machineLoad μ σ p := by
  unfold loadBefore machineLoad
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum (fun j _ => ?_)
  by_cases h1 : (L.symm j : ℕ) < k <;> by_cases h2 : σ j = p <;> simp [h1, h2, (hμ j).le]

lemma kl_prefix_le {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j) (L : Fin r ≃ Fin r)
    (σ : Fin r → Fin n) (k : ℕ) : prefixFinish μ L σ k ≤ makespan μ σ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  unfold prefixFinish makespan
  rw [dif_pos h, dif_pos h]
  apply Finset.sup'_le
  intro p hp
  exact le_trans (kl_load_le μ hμ L σ k p) (Finset.le_sup' (machineLoad μ σ) hp)

lemma kl_exists_opt {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ) :
    ∃ τ : Fin r → Fin n, optFinish μ n = makespan μ τ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h : (Finset.univ : Finset (Fin r → Fin n)).Nonempty := Finset.univ_nonempty
  unfold optFinish
  rw [dif_pos h]
  obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_inf' h (makespan μ)
  exact ⟨τ, hτ⟩

lemma kl_opt_le {r n : ℕ} (μ : Fin r → ℝ) (σ : Fin r → Fin n) :
    optFinish μ n ≤ makespan μ σ := by
  have h : (Finset.univ : Finset (Fin r → Fin n)).Nonempty := ⟨σ, Finset.mem_univ _⟩
  unfold optFinish
  rw [dif_pos h]
  exact Finset.inf'_le _ (Finset.mem_univ σ)

lemma kl_le_opt {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ) (c : ℝ)
    (h : ∀ τ : Fin r → Fin n, c ≤ makespan μ τ) : c ≤ optFinish μ n := by
  obtain ⟨τ, hτ⟩ := kl_exists_opt hn μ
  rw [hτ]; exact h τ

lemma kl_sum_div_le {r n : ℕ} (hn : 0 < n) (μ : Fin r → ℝ) :
    (1 / (n : ℝ)) * ∑ j, μ j ≤ optFinish μ n :=
  kl_le_opt hn μ _ (fun τ => kl_makespan_ge_avg hn μ τ)

lemma kl_eq_opt {r n k : ℕ} (hn : 0 < n) (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hopt : ∀ τ : Fin r → Fin n, prefixFinish μ L σ k ≤ prefixFinish μ L τ k) :
    makespan μ σ = prefixFinish μ L σ k → makespan μ σ = optFinish μ n := by
  intro heq
  apply le_antisymm
  · rw [heq]
    exact kl_le_opt hn μ _ (fun τ => le_trans (hopt τ) (kl_prefix_le hn μ hμ L τ k))
  · exact kl_opt_le μ σ

lemma kl_alpha_le {r : ℕ} (μ : Fin r → ℝ) (L : Fin r ≃ Fin r) (k : ℕ) (j : Fin r)
    (hj : k ≤ (L.symm j : ℕ)) : μ j ≤ alphaStar μ L k := by
  have hne : (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).Nonempty :=
    ⟨j, by simp [hj]⟩
  unfold alphaStar
  rw [dif_pos hne]
  exact Finset.le_sup' μ (by simp [hj])

lemma kl_sum_ge {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ)
    (hgt : prefixFinish μ L σ k < makespan μ σ) :
    (n : ℝ) * (makespan μ σ - alphaStar μ L k) + alphaStar μ L k ≤ ∑ j, μ j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  have hM : makespan μ σ = Finset.univ.sup' h (machineLoad μ σ) := by
    unfold makespan; rw [dif_pos h]
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' h (machineLoad μ σ)
  rw [← hM] at hp
  set T : Finset (Fin r) := Finset.univ.filter (fun j => σ j = p) with hT
  have hmp : machineLoad μ σ p = ∑ j ∈ T, μ j := by
    unfold machineLoad; rw [hT, Finset.sum_filter]
  set T' : Finset (Fin r) := T.filter (fun j => k ≤ (L.symm j : ℕ)) with hT'
  have hne : T'.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have : machineLoad μ σ p ≤ loadBefore μ L σ k p := by
      rw [hmp]
      unfold loadBefore
      apply le_of_eq
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext j
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj
        refine ⟨?_, hj⟩
        by_contra hk
        exact (Finset.eq_empty_iff_forall_notMem.mp hcon j)
          (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, not_lt.mp hk⟩)
      · intro hj; exact hj.2
    have h2 : loadBefore μ L σ k p ≤ prefixFinish μ L σ k := by
      unfold prefixFinish; rw [dif_pos h]
      exact Finset.le_sup' (loadBefore μ L σ k) (Finset.mem_univ p)
    linarith
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image T' (fun j => (L.symm j : ℕ)) hne
  have hj0T : j0 ∈ T := (Finset.mem_filter.mp hj0).1
  have hj0k : k ≤ (L.symm j0 : ℕ) := (Finset.mem_filter.mp hj0).2
  have hj0p : σ j0 = p := by simpa [hT] using hj0T
  set q : ℕ := (L.symm j0 : ℕ) with hq
  -- all jobs on p have position ≤ q
  have hle : ∀ j ∈ T, (L.symm j : ℕ) ≤ q := by
    intro j hj
    by_cases hk : k ≤ (L.symm j : ℕ)
    · exact hmax j (Finset.mem_filter.mpr ⟨hj, hk⟩)
    · exact le_trans (not_le.mp hk).le hj0k
  have hload : loadBefore μ L σ q p = machineLoad μ σ p - μ j0 := by
    rw [hmp]
    unfold loadBefore
    have : Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < q ∧ σ j = p) = T.erase j0 := by
      ext j
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rintro rfl; exact lt_irrefl _ h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have := hle j (by simpa [hT] using h2)
        rcases this.lt_or_eq with h3 | h3
        · exact h3
        · exfalso; apply h1
          apply L.symm.injective
          exact Fin.ext h3
    rw [this, ← Finset.sum_erase_add T μ hj0T]
    ring
  have hmin : ∀ p' : Fin n, machineLoad μ σ p - μ j0 ≤ loadBefore μ L σ q p' := by
    intro p'
    rw [← hload, ← hj0p]
    exact hσ j0 p'
  have hsum := kl_sum_load μ L σ q
  have hsub : ∑ j ∈ Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < q), μ j + μ j0 ≤ ∑ j, μ j := by
    have hnot : j0 ∉ Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < q) := by simp [hq]
    rw [add_comm, ← Finset.sum_insert hnot]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => (hμ j).le)
  have hcard : (n : ℝ) * (machineLoad μ σ p - μ j0) ≤ ∑ p', loadBefore μ L σ q p' := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin n)) (fun p' => loadBefore μ L σ q p') _ (fun p' _ => hmin p')
    simpa using this
  have hα := kl_alpha_le μ L k j0 hj0k
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hp]
  have : ((n : ℝ) - 1) * μ j0 ≤ ((n : ℝ) - 1) * alphaStar μ L k :=
    mul_le_mul_of_nonneg_left hα (by linarith)
  nlinarith

lemma kl_opt_ge_sub {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ)
    (hgt : prefixFinish μ L σ k < makespan μ σ) :
    makespan μ σ - ((n : ℝ) - 1) / n * alphaStar μ L k ≤ optFinish μ n := by
  have h1 := kl_sum_ge hn μ hμ L σ hσ hgt
  have h2 := kl_sum_div_le hn μ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : makespan μ σ - ((n : ℝ) - 1) / n * alphaStar μ L k
      = (1 / (n : ℝ)) * ((n : ℝ) * (makespan μ σ - alphaStar μ L k) + alphaStar μ L k) := by
    field_simp
    ring
  rw [h3]
  refine le_trans ?_ h2
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

lemma kl_alpha_bound {r n k : ℕ} (hn : 0 < n) (hk : k ≤ r)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hkr : k < r) :
    (1 + ((k / n : ℕ) : ℝ)) * alphaStar μ L k ≤ optFinish μ n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).Nonempty :=
    ⟨L ⟨k, hkr⟩, by simp⟩
  have hαdef : alphaStar μ L k = (Finset.univ.filter (fun j : Fin r => k ≤ (L.symm j : ℕ))).sup' hne μ := by
    unfold alphaStar; rw [dif_pos hne]
  obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_sup' hne μ
  rw [← hαdef] at hj0eq
  have hj0k : k ≤ (L.symm j0 : ℕ) := (Finset.mem_filter.mp hj0).2
  have hfirst : ∀ i, (L.symm i : ℕ) < k → alphaStar μ L k ≤ μ i := by
    intro i hi; rw [hj0eq]; exact hlong i j0 hi hj0k
  set A : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < k) with hA
  have hAcard : A.card = k := by
    rw [hA]
    have := Finset.card_equiv L.symm (s := Finset.univ.filter (fun j : Fin r => (L.symm j : ℕ) < k))
      (t := Finset.univ.filter (fun i : Fin r => (i : ℕ) < k)) (by intro i; simp)
    rw [this, Fin.card_filter_val_lt]; omega
  have hj0A : j0 ∉ A := by simp [hA]; omega
  set S : Finset (Fin r) := insert j0 A with hS
  have hScard : S.card = k + 1 := by rw [hS, Finset.card_insert_of_notMem hj0A, hAcard]
  have hSα : ∀ j ∈ S, alphaStar μ L k ≤ μ j := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hj0eq.le
    · exact hfirst j (by simpa [hA] using hj)
  apply kl_le_opt hn μ
  intro τ
  have hlt : (Finset.univ : Finset (Fin n)).card * (k / n) < S.card := by
    rw [hScard, Finset.card_univ, Fintype.card_fin]
    have := Nat.mul_div_le k n
    omega
  obtain ⟨y, _, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := S) (t := Finset.univ) (f := τ) (fun a _ => Finset.mem_univ _) hlt
  have hα0 : 0 ≤ alphaStar μ L k := by
    rw [hj0eq]; exact (hμ j0).le
  have hml : machineLoad μ τ y = ∑ j ∈ Finset.univ.filter (fun j => τ j = y), μ j := by
    unfold machineLoad; rw [Finset.sum_filter]
  have h1 : ∑ j ∈ S.filter (fun j => τ j = y), μ j ≤ machineLoad μ τ y := by
    rw [hml]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj; simp only [Finset.mem_filter] at hj ⊢; exact ⟨Finset.mem_univ _, hj.2⟩
    · intro j _ _; exact (hμ j).le
  have h2 : (S.filter (fun j => τ j = y)).card • alphaStar μ L k ≤ ∑ j ∈ S.filter (fun j => τ j = y), μ j :=
    Finset.card_nsmul_le_sum _ _ _ (fun j hj => hSα j (Finset.mem_filter.mp hj).1)
  rw [nsmul_eq_mul] at h2
  have h3 : (1 + ((k / n : ℕ) : ℝ)) ≤ ((S.filter (fun j => τ j = y)).card : ℝ) := by
    have : k / n + 1 ≤ (S.filter (fun j => τ j = y)).card := hy
    have : ((k / n + 1 : ℕ) : ℝ) ≤ ((S.filter (fun j => τ j = y)).card : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  have h4 : machineLoad μ τ y ≤ makespan μ τ := by
    have h : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
    unfold makespan; rw [dif_pos h]
    exact Finset.le_sup' (machineLoad μ τ) (Finset.mem_univ y)
  have h5 := mul_le_mul_of_nonneg_right h3 hα0
  linarith

lemma kl_main {r n k : ℕ} (hr : 0 < r) (hn : 0 < n) (hk : k ≤ r)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hlong : ∀ i j, (L.symm i : ℕ) < k → k ≤ (L.symm j : ℕ) → μ j ≤ μ i)
    (hσ : IsListAssignment μ L σ)
    (hopt : ∀ τ : Fin r → Fin n, prefixFinish μ L σ k ≤ prefixFinish μ L τ k) :
    makespan μ σ / optFinish μ n ≤ 1 + (1 - 1 / (n : ℝ)) / (1 + ((k / n : ℕ) : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn']; exact hn1
  have hf : (0 : ℝ) < 1 + ((k / n : ℕ) : ℝ) := by positivity
  have hrpos : (0 : ℝ) < ∑ j, μ j := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact Finset.sum_pos (fun j _ => hμ j) Finset.univ_nonempty
  have hoptpos : 0 < optFinish μ n := lt_of_lt_of_le (by positivity) (kl_sum_div_le hn μ)
  have hle := kl_prefix_le hn μ hμ L σ k
  rcases hle.lt_or_eq with hgt | heq
  · have hkr : k < r := by
      rcases hk.lt_or_eq with h | h
      · exact h
      · exfalso
        subst h
        have : prefixFinish μ L σ k = makespan μ σ := by
          have hh : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
          apply le_antisymm hle
          unfold prefixFinish makespan
          rw [dif_pos hh, dif_pos hh]
          apply Finset.sup'_le
          intro p hp
          refine le_trans ?_ (Finset.le_sup' (loadBefore μ L σ k) hp)
          apply le_of_eq
          unfold loadBefore machineLoad
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have := (L.symm j).isLt
          by_cases h2 : σ j = p <;> simp [h2, this]
        linarith
    have h1 := kl_opt_ge_sub hn μ hμ L σ hσ hgt
    have h2 := kl_alpha_bound hn hk μ hμ L hlong hkr
    set α := alphaStar μ L k
    set f : ℝ := 1 + ((k / n : ℕ) : ℝ)
    set O := optFinish μ n
    set M := makespan μ σ
    have hc : (0 : ℝ) ≤ ((n : ℝ) - 1) / n := by
      apply div_nonneg <;> linarith
    have h3 : ((n : ℝ) - 1) / n * α ≤ ((n : ℝ) - 1) / n * (O / f) := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [le_div_iff₀ hf]; linarith
    have h4 : (1 - 1 / (n : ℝ)) = ((n : ℝ) - 1) / n := by field_simp
    rw [h4, div_le_iff₀ hoptpos]
    have h5 : M ≤ O + ((n : ℝ) - 1) / n * (O / f) := by linarith
    calc M ≤ O + ((n : ℝ) - 1) / n * (O / f) := h5
      _ = (1 + ((n : ℝ) - 1) / n / f) * O := by ring
  · have := kl_eq_opt hn μ hμ L σ hopt heq.symm
    rw [this, div_self hoptpos.ne']
    have : 0 ≤ (1 - 1 / (n : ℝ)) / (1 + ((k / n : ℕ) : ℝ)) := div_nonneg hnn hf.le
    linarith

end GrahamAnomaly.KLongest

open GrahamAnomaly.KLongest


theorem solution {r n k : ℕ} (hn : 0 < n)
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (L : Fin r ≃ Fin r) (σ : Fin r → Fin n)
    (hσ : IsListAssignment μ L σ) (hkr : k < r)
    (hgt : prefixFinish μ L σ k < WilliamsonShmoys.makespan μ σ) :
    (n : ℝ) * (WilliamsonShmoys.makespan μ σ - alphaStar μ L k) +
      alphaStar μ L k ≤ ∑ j, μ j := by
  exact kl_sum_ge hn μ hμ L σ hσ hgt
