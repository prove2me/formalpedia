-- Prove2me | solution 1 for LeightonRao.ShortPaths.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T21:42:54.924997+00:00
-- url     : https://prove2.me/submissions/c17c2df1-50fa-47df-bb4b-8831c9f181b7

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting



namespace LeightonRao.ShortPaths

variable {V : Type} [Fintype V] [DecidableEq V]

lemma l21_distL_anti (N : Network V) (d : V → V → ℝ) {B B' : ℝ} (h : B ≤ B') (u v : V) :
    distL N d B' u v ≤ distL N d B u v := by
  unfold distL
  exact le_iInf₂ fun p hp => iInf₂_le p (hp.trans h)

lemma l21_distFromL_anti (N : Network V) (d : V → V → ℝ) {B B' : ℝ} (h : B ≤ B')
    (T : Finset V) (u : V) :
    distFromL N d B' T u ≤ distFromL N d B T u := by
  unfold distFromL
  exact le_iInf₂ fun t ht => (iInf₂_le t ht).trans (l21_distL_anti N d h t u)

lemma l21_distFromL_mem (N : Network V) (d : V → V → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (T : Finset V) (t : V) (ht : t ∈ T) :
    distFromL N d B T t = 0 := by
  apply le_antisymm _ bot_le
  unfold distFromL
  refine (iInf₂_le t ht).trans ?_
  unfold distL
  refine (iInf₂_le (SimpleGraph.Walk.nil : N.graph.Walk t t) (by simpa using hB)).trans ?_
  simp [walkLen]

lemma l21_walkLen_nonneg (N : Network V) {d : V → V → ℝ} (hd : IsDistanceFunction d)
    {u v : V} (p : N.graph.Walk u v) : 0 ≤ walkLen d p := by
  unfold walkLen
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact hd.1 _ _

lemma l21_distFromL_step (N : Network V) {d : V → V → ℝ} (hd : IsDistanceFunction d)
    (T : Finset V) (k : ℕ) (u v : V) (huv : 0 < N.C u v) :
    distFromL N d ((k + 1 : ℕ) : ℝ) T v ≤ distFromL N d (k : ℝ) T u + ENNReal.ofReal (d u v) := by
  have hadj : N.graph.Adj u v := by
    unfold Network.graph
    rw [SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl huv⟩
    rintro rfl
    rw [N.C_self] at huv
    exact lt_irrefl _ huv
  unfold distFromL
  unfold distL
  simp only [ENNReal.iInf_add]
  refine le_iInf fun t => le_iInf fun ht => le_iInf fun p => le_iInf fun hp => ?_
  refine (iInf₂_le t ht).trans ((iInf₂_le (p.concat hadj) ?_).trans ?_)
  · simp only [SimpleGraph.Walk.length_concat]; push_cast; linarith
  · have : walkLen d (p.concat hadj) = walkLen d p + d u v := by
      simp [walkLen, SimpleGraph.Walk.darts_concat]
    rw [this]
    exact ENNReal.ofReal_add_le


section Abstract
variable (N : Network V) (d : V → V → ℝ) (T : Finset V) (F : ℕ → V → ENNReal)

noncomputable def l21B (k : ℕ) (ρ : ℝ) : Finset V :=
  Finset.univ.filter (fun u => F k u ≤ ENNReal.ofReal ρ)

noncomputable def l21Pot (k : ℕ) (ρ : ℝ) : ℝ :=
  ∑ u ∈ Tᶜ, (min (F k u) (ENNReal.ofReal ρ)).toReal

noncomputable def l21res (k : ℕ) (ρ : ℝ) (u v : V) : ℝ :=
  if F k u ≤ ENNReal.ofReal ρ then max 0 ((F k u).toReal + d u v - ρ) else d u v

noncomputable def l21Res (k : ℕ) (ρ : ℝ) : ℝ :=
  ∑ u, ∑ v, N.C u v * l21res d F k ρ u v

end Abstract

lemma l21_median {ι : Type} [DecidableEq ι] (s : Finset ι) (w r : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∃ t, 0 ≤ t ∧ ∑ i ∈ s, w i ≤ 2 * ∑ i ∈ s.filter (fun i => r i ≤ t), w i ∧
      ∑ i ∈ s, w i ≤ 2 * ∑ i ∈ s.filter (fun i => t ≤ r i), w i := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, le_rfl, by simp, by simp⟩
  have htot : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  set c := s.filter (fun j => ∑ i ∈ s, w i ≤ 2 * ∑ i ∈ s.filter (fun i => r i ≤ r j), w i)
    with hc
  have hcne : c.Nonempty := by
    obtain ⟨j, hj, hmax⟩ := s.exists_max_image r hs
    refine ⟨j, Finset.mem_filter.2 ⟨hj, ?_⟩⟩
    rw [Finset.filter_true_of_mem (fun i hi => hmax i hi)]
    linarith
  obtain ⟨j0, hj0, hmin⟩ := c.exists_min_image r hcne
  have hj0' := Finset.mem_filter.1 hj0
  refine ⟨r j0, hr j0 hj0'.1, hj0'.2, ?_⟩
  have hsplit : ∑ i ∈ s, w i = ∑ i ∈ s.filter (fun i => r i < r j0), w i +
      ∑ i ∈ s.filter (fun i => r j0 ≤ r i), w i := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun i => r i < r j0)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp [not_lt]
  have hlow : 2 * ∑ i ∈ s.filter (fun i => r i < r j0), w i ≤ ∑ i ∈ s, w i := by
    rcases (s.filter (fun i => r i < r j0)).eq_empty_or_nonempty with he | hne
    · rw [he]; simpa using htot
    obtain ⟨j1, hj1, hmax1⟩ := (s.filter (fun i => r i < r j0)).exists_max_image r hne
    have hj1' := Finset.mem_filter.1 hj1
    have hnot : j1 ∉ c := by
      intro h; have := hmin j1 h; linarith [hj1'.2]
    have hsub : s.filter (fun i => r i < r j0) ⊆ s.filter (fun i => r i ≤ r j1) := by
      intro i hi
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hi).1, hmax1 i hi⟩
    have hn : ¬ (∑ i ∈ s, w i ≤ 2 * ∑ i ∈ s.filter (fun i => r i ≤ r j1), w i) :=
      fun h => hnot (Finset.mem_filter.2 ⟨hj1'.1, h⟩)
    have h2 : ∑ i ∈ s.filter (fun i => r i < r j0), w i ≤
        ∑ i ∈ s.filter (fun i => r i ≤ r j1), w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hw i (Finset.mem_filter.1 hi).1)
    push_neg at hn; linarith
  linarith

lemma l21_mem_B (F : ℕ → V → ENNReal) (k : ℕ) (ρ : ℝ) (u : V) :
    u ∈ l21B F k ρ ↔ F k u ≤ ENNReal.ofReal ρ := by
  simp [l21B]

lemma l21_res_nonneg (d : V → V → ℝ) (hd : IsDistanceFunction d) (F : ℕ → V → ENNReal)
    (k : ℕ) (ρ : ℝ) (u v : V) : 0 ≤ l21res d F k ρ u v := by
  unfold l21res; split_ifs
  · exact le_max_left _ _
  · exact hd.1 _ _

lemma l21_aux (x y Δ : ℝ) (hy : y ≤ x - Δ) (hΔ : 0 ≤ Δ) :
    max 0 y + min (max 0 x) Δ ≤ max 0 x := by
  simp only [max_def, min_def]; split_ifs <;> linarith

lemma l21_step (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (F : ℕ → V → ENNReal) (T : Finset V)
    (hF1 : ∀ k u v, 0 < N.C u v → F (k+1) v ≤ F k u + ENNReal.ofReal (d u v))
    (hF2 : ∀ k u, F (k+1) u ≤ F k u)
    (M : ℝ) (hM : ∀ v, ∑ u, N.C u v ≤ M)
    (k : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ Δ, 0 ≤ Δ ∧
      cutCap N (l21B F k ρ) ≤ 2 * M * ((l21B F (k+1) (ρ+Δ)).card - (l21B F k ρ).card : ℝ) ∧
      l21Pot T F (k+1) (ρ+Δ) ≤ l21Pot T F k ρ + Δ * ((l21B F k ρ)ᶜ.card : ℝ) ∧
      l21Res N d F (k+1) (ρ+Δ) + Δ * cutCap N (l21B F k ρ) / 2 ≤ l21Res N d F k ρ := by
  set B := l21B F k ρ with hB
  have hcut : cutCap N B = ∑ p ∈ B ×ˢ Bᶜ, N.C p.1 p.2 := by
    unfold cutCap; rw [Finset.sum_product]
  obtain ⟨Δ, hΔ, h1, h2⟩ := l21_median (B ×ˢ Bᶜ) (fun p => N.C p.1 p.2)
    (fun p => l21res d F k ρ p.1 p.2)
    (fun p _ => N.C_nonneg _ _) (fun p _ => l21_res_nonneg d hd F k ρ _ _)
  set B' := l21B F (k+1) (ρ+Δ) with hB'
  have hsub : B ⊆ B' := by
    intro u hu
    rw [l21_mem_B] at hu ⊢
    exact (hF2 k u).trans (hu.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  refine ⟨Δ, hΔ, ?_, ?_, ?_⟩
  · -- hop progress
    rw [hcut]
    set X := (B ×ˢ Bᶜ).filter (fun p => l21res d F k ρ p.1 p.2 ≤ Δ)
    have hX : ∑ p ∈ X, N.C p.1 p.2 = ∑ p ∈ X.filter (fun p => 0 < N.C p.1 p.2), N.C p.1 p.2 := by
      symm; apply Finset.sum_filter_of_ne
      intro p _ hp
      exact lt_of_le_of_ne (N.C_nonneg _ _) (Ne.symm hp)
    have hXsub : X.filter (fun p => 0 < N.C p.1 p.2) ⊆ Finset.univ ×ˢ (B' \ B) := by
      intro p hp
      simp only [X, Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at hp
      obtain ⟨⟨⟨hu, hv⟩, hres⟩, hC⟩ := hp
      refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_sdiff.2 ⟨?_, hv⟩⟩
      have hu' := (l21_mem_B F k ρ p.1).1 hu
      rw [l21_mem_B]
      have hne : F k p.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu'
      unfold l21res at hres
      rw [if_pos hu'] at hres
      have hle := (le_max_right _ _).trans hres
      refine (hF1 k p.1 p.2 hC).trans ?_
      rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_add ENNReal.toReal_nonneg (hd.1 _ _)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h3 : ∑ p ∈ Finset.univ ×ˢ (B' \ B), N.C p.1 p.2 ≤ ((B' \ B).card : ℝ) * M := by
      rw [Finset.sum_product, Finset.sum_comm]
      calc ∑ y ∈ B' \ B, ∑ x, N.C x y ≤ ∑ y ∈ B' \ B, M := Finset.sum_le_sum fun y _ => hM y
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h4 := Finset.card_sdiff_add_card_eq_card hsub
    have h5 : ((B' \ B).card : ℝ) = B'.card - B.card := by
      rw [← h4]; push_cast; ring
    have h6 : ∑ p ∈ X.filter (fun p => 0 < N.C p.1 p.2), N.C p.1 p.2 ≤
        ∑ p ∈ Finset.univ ×ˢ (B' \ B), N.C p.1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hXsub (fun _ _ _ => N.C_nonneg _ _)
    rw [h5] at h3
    have h1' : ∑ p ∈ B ×ˢ Bᶜ, N.C p.1 p.2 ≤ 2 * ∑ p ∈ X, N.C p.1 p.2 := h1
    linarith
  · -- potential
    have hper : ∀ u, (min (F (k+1) u) (ENNReal.ofReal (ρ+Δ))).toReal ≤
        (min (F k u) (ENNReal.ofReal ρ)).toReal + (if u ∈ Bᶜ then Δ else 0) := by
      intro u
      by_cases hu : F k u ≤ ENNReal.ofReal ρ
      · have huB : u ∉ Bᶜ := by
          rw [Finset.mem_compl, not_not, l21_mem_B]; exact hu
        rw [if_neg huB, add_zero, min_eq_left hu]
        have hne : F k u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
        exact ENNReal.toReal_mono hne (min_le_left _ _ |>.trans (hF2 k u))
      · have huB : u ∈ Bᶜ := by
          rw [Finset.mem_compl, l21_mem_B]; exact hu
        rw [if_pos huB, min_eq_right (le_of_not_ge hu), ENNReal.toReal_ofReal hρ]
        calc (min (F (k+1) u) (ENNReal.ofReal (ρ+Δ))).toReal
            ≤ (ENNReal.ofReal (ρ+Δ)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right _ _)
          _ = ρ + Δ := ENNReal.toReal_ofReal (by linarith)
    unfold l21Pot
    calc ∑ u ∈ Tᶜ, (min (F (k+1) u) (ENNReal.ofReal (ρ+Δ))).toReal
        ≤ ∑ u ∈ Tᶜ, ((min (F k u) (ENNReal.ofReal ρ)).toReal + (if u ∈ Bᶜ then Δ else 0)) :=
          Finset.sum_le_sum fun u _ => hper u
      _ = ∑ u ∈ Tᶜ, (min (F k u) (ENNReal.ofReal ρ)).toReal + ∑ u ∈ Tᶜ ∩ Bᶜ, Δ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have : ((Tᶜ ∩ Bᶜ).card : ℝ) ≤ (Bᶜ.card : ℝ) := by
            exact_mod_cast Finset.card_le_card Finset.inter_subset_right
          nlinarith
  · -- residual budget
    set g : V → V → ℝ := fun u v => N.C u v * min (l21res d F k ρ u v) Δ with hg
    let ind : V → V → ℝ := fun u v => if u ∈ B then (if v ∈ Bᶜ then g u v else 0) else 0
    have hgnn : ∀ u v, 0 ≤ g u v := fun u v =>
      mul_nonneg (N.C_nonneg _ _) (le_min (l21_res_nonneg d hd F k ρ u v) hΔ)
    have hper : ∀ u v, N.C u v * l21res d F (k+1) (ρ+Δ) u v + ind u v ≤
        N.C u v * l21res d F k ρ u v := by
      intro u v
      have hC := N.C_nonneg u v
      by_cases hu : F k u ≤ ENNReal.ofReal ρ
      · have hu1 : F (k+1) u ≤ ENNReal.ofReal (ρ+Δ) := (l21_mem_B F (k+1) (ρ+Δ) u).1
          (hsub ((l21_mem_B F k ρ u).2 hu))
        have hne : F k u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
        have hmono : (F (k+1) u).toReal ≤ (F k u).toReal := ENNReal.toReal_mono hne (hF2 k u)
        have hind : ind u v ≤ g u v := by
          simp only [ind]; split_ifs
          · exact le_rfl
          · exact hgnn u v
          · exact hgnn u v
        simp only [hg] at hind
        unfold l21res at hind ⊢
        rw [if_pos hu1]
        rw [if_pos hu] at hind ⊢
        have := l21_aux ((F k u).toReal + d u v - ρ) ((F (k+1) u).toReal + d u v - (ρ + Δ)) Δ
          (by linarith) hΔ
        nlinarith
      · have hind : ind u v = 0 := by
          simp only [ind]; rw [if_neg]; rw [l21_mem_B]; exact hu
        rw [hind, add_zero]
        apply mul_le_mul_of_nonneg_left _ hC
        unfold l21res
        rw [if_neg hu]
        split_ifs with h'
        · apply max_le (hd.1 _ _)
          have : (F (k+1) u).toReal ≤ ρ + Δ := ENNReal.toReal_le_of_le_ofReal (by linarith) h'
          linarith
        · exact le_rfl
    have hsumind : ∑ u, ∑ v, ind u v = ∑ p ∈ B ×ˢ Bᶜ, g p.1 p.2 := by
      have hi : ∀ u, ∑ v, ind u v = if u ∈ B then ∑ v ∈ Bᶜ, g u v else 0 := by
        intro u
        by_cases hu : u ∈ B
        · simp only [ind, if_pos hu]
          rw [Finset.sum_ite_mem, Finset.univ_inter]
        · simp [ind, hu]
      simp_rw [hi]
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_product]
    have hlow : Δ * cutCap N B / 2 ≤ ∑ p ∈ B ×ˢ Bᶜ, g p.1 p.2 := by
      have hf : ∑ p ∈ (B ×ˢ Bᶜ).filter (fun p => Δ ≤ l21res d F k ρ p.1 p.2), g p.1 p.2 ≤
          ∑ p ∈ B ×ˢ Bᶜ, g p.1 p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => hgnn p.1 p.2)
      have he : ∑ p ∈ (B ×ˢ Bᶜ).filter (fun p => Δ ≤ l21res d F k ρ p.1 p.2), g p.1 p.2 =
          Δ * ∑ p ∈ (B ×ˢ Bᶜ).filter (fun p => Δ ≤ l21res d F k ρ p.1 p.2), N.C p.1 p.2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_filter] at hp
        simp only [hg, min_eq_right hp.2]; ring
      have h2' : cutCap N B ≤ 2 * ∑ p ∈ (B ×ˢ Bᶜ).filter
          (fun p => Δ ≤ l21res d F k ρ p.1 p.2), N.C p.1 p.2 := by rw [hcut]; exact h2
      nlinarith
    unfold l21Res
    have htot := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
      Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hper u v
    simp only [Finset.sum_add_distrib] at htot
    linarith

lemma l21_main (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (F : ℕ → V → ENNReal) (T : Finset V)
    (hF0 : ∀ k, ∀ t ∈ T, F k t = 0)
    (hF1 : ∀ k u v, 0 < N.C u v → F (k+1) v ≤ F k u + ENNReal.ofReal (d u v))
    (hF2 : ∀ k u, F (k+1) u ≤ F k u)
    (M S : ℝ) (hM : ∀ v, ∑ u, N.C u v ≤ M) (hMpos : 0 < M) (hS : 0 < S)
    (hcut : ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty →
      S * U.card * Uᶜ.card ≤ cutCap N U)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ)) (hTne : T.Nonempty)
    (hq : (Fintype.card V : ℝ) * S ≤ 3 * M) :
    ∀ K : ℕ, ∃ ρ, 0 ≤ ρ ∧
      ((l21B F K ρ)ᶜ.card : ℝ) ≤
        ((Fintype.card V : ℝ) / 3) * (1 - (Fintype.card V : ℝ) * S / (3 * M)) ^ K ∧
      l21Pot T F K ρ + 3 / ((Fintype.card V : ℝ) * S) * l21Res N d F K ρ ≤
        6 * totalWeight N d / ((Fintype.card V : ℝ) * S) := by
  have hn : (0 : ℝ) < Fintype.card V := by
    have := hTne.card_pos.trans_le (Finset.card_le_univ T); exact_mod_cast this
  have hTB : ∀ K ρ, 0 ≤ ρ → T ⊆ l21B F K ρ := by
    intro K ρ hρ t ht
    rw [l21_mem_B, hF0 K t ht]; exact bot_le
  have hcompl : ∀ U : Finset V, ((Uᶜ).card : ℝ) = Fintype.card V - U.card := by
    intro U
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ U)]
  have hcutnn : ∀ U : Finset V, 0 ≤ cutCap N U := fun U =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => N.C_nonneg _ _
  intro K
  induction K with
  | zero =>
    refine ⟨0, le_rfl, ?_, ?_⟩
    · have hsub : (l21B F 0 0)ᶜ ⊆ Tᶜ := Finset.compl_subset_compl.2 (hTB 0 0 le_rfl)
      have h1 : (((l21B F 0 0)ᶜ).card : ℝ) ≤ (Tᶜ.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      rw [hcompl T] at h1
      simp only [pow_zero, mul_one]
      linarith
    · have hP : l21Pot T F 0 0 = 0 := by
        unfold l21Pot; simp
      have hR : l21Res N d F 0 0 ≤ 2 * totalWeight N d := by
        unfold l21Res totalWeight
        rw [show 2 * ((1 / 2 : ℝ) * ∑ u, ∑ v, N.C u v * d u v) = ∑ u, ∑ v, N.C u v * d u v by ring]
        apply Finset.sum_le_sum; intro u _; apply Finset.sum_le_sum; intro v _
        apply mul_le_mul_of_nonneg_left _ (N.C_nonneg _ _)
        unfold l21res
        split_ifs with h
        · rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h
          rw [h]; simp [hd.1 u v]
        · exact le_rfl
      rw [hP, zero_add]
      have hc : 0 ≤ 3 / ((Fintype.card V : ℝ) * S) := by positivity
      calc 3 / ((Fintype.card V : ℝ) * S) * l21Res N d F 0 0
          ≤ 3 / ((Fintype.card V : ℝ) * S) * (2 * totalWeight N d) :=
            mul_le_mul_of_nonneg_left hR hc
        _ = _ := by ring
  | succ K ih =>
    obtain ⟨ρ, hρ, hm, hpot⟩ := ih
    obtain ⟨Δ, hΔ, ha, hb, hc⟩ := l21_step N d hd F T hF1 hF2 M hM K ρ hρ
    refine ⟨ρ + Δ, by linarith, ?_, ?_⟩
    · set B := l21B F K ρ
      set B' := l21B F (K+1) (ρ+Δ)
      have hb1 : (T.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card (hTB K ρ hρ)
      have hcutB : S * B.card * (Bᶜ.card : ℝ) ≤ cutCap N B := by
        rcases (Bᶜ).eq_empty_or_nonempty with he | hne
        · rw [he]; simp [hcutnn]
        · exact hcut B (hTne.mono (hTB K ρ hρ)) hne
      have hm0 : (0 : ℝ) ≤ Bᶜ.card := by positivity
      have key : (Fintype.card V : ℝ) * S / (3 * M) * Bᶜ.card ≤ B'.card - B.card := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hS.le hm0) (sub_nonneg.2 (hT.trans
          (mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 3))))]
      have hq1 : 0 ≤ 1 - (Fintype.card V : ℝ) * S / (3 * M) := by
        rw [sub_nonneg, div_le_one (by positivity)]; exact hq
      rw [hcompl B'] ; rw [hcompl B] at hm key
      rw [pow_succ]
      have : (Fintype.card V : ℝ) - B'.card ≤
          ((Fintype.card V : ℝ) - B.card) * (1 - (Fintype.card V : ℝ) * S / (3 * M)) := by
        nlinarith
      calc (Fintype.card V : ℝ) - B'.card
          ≤ ((Fintype.card V : ℝ) - B.card) * (1 - (Fintype.card V : ℝ) * S / (3 * M)) := this
        _ ≤ _ := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hm hq1
    · set B := l21B F K ρ
      have hb1 : (T.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card (hTB K ρ hρ)
      have hcutB : S * B.card * (Bᶜ.card : ℝ) ≤ cutCap N B := by
        rcases (Bᶜ).eq_empty_or_nonempty with he | hne
        · rw [he]; simp [hcutnn]
        · exact hcut B (hTne.mono (hTB K ρ hρ)) hne
      have hm0 : (0 : ℝ) ≤ Bᶜ.card := by positivity
      have key : 2 * ((Fintype.card V : ℝ) * S) * Bᶜ.card ≤ 3 * cutCap N B := by
        nlinarith [mul_nonneg (mul_nonneg hS.le hm0) (sub_nonneg.2 (hT.trans
          (mul_le_mul_of_nonneg_left hb1 (by norm_num : (0:ℝ) ≤ 3))))]
      have key2 : (Bᶜ.card : ℝ) ≤ 3 / ((Fintype.card V : ℝ) * S) * cutCap N B / 2 := by
        rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
        linarith
      set c := 3 / ((Fintype.card V : ℝ) * S) with hcdef
      have hc0 : 0 ≤ c := by positivity
      have e1 : c * l21Res N d F (K+1) (ρ+Δ) ≤ c * l21Res N d F K ρ - c * (Δ * cutCap N B / 2) := by
        rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (by linarith) hc0
      have e2 : Δ * (Bᶜ.card : ℝ) ≤ c * (Δ * cutCap N B / 2) := by
        have := mul_le_mul_of_nonneg_left key2 hΔ
        calc Δ * (Bᶜ.card : ℝ) ≤ Δ * (c * cutCap N B / 2) := this
          _ = _ := by ring
      linarith

lemma l21_minCut_le (N : Network V) (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty) :
    minCut N * U.card * Uᶜ.card ≤ cutCap N U := by
  have hcnn : 0 ≤ cutCap N U :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => N.C_nonneg _ _
  have h : minCut N ≤ ratioCost N U := by
    unfold minCut
    refine ciInf_le (f := fun U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} => ratioCost N U.1)
      ⟨0, ?_⟩ ⟨U, hU, hUc⟩
    rintro _ ⟨W, rfl⟩
    unfold ratioCost
    apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => N.C_nonneg _ _
  unfold ratioCost at h
  have hpos : (0:ℝ) < U.card * Uᶜ.card := by
    have h1 : (0:ℝ) < U.card := by exact_mod_cast hU.card_pos
    have h2 : (0:ℝ) < Uᶜ.card := by exact_mod_cast hUc.card_pos
    positivity
  rw [le_div_iff₀ hpos] at h; linarith

lemma l21_minCut_pos (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) :
    0 < minCut N := by
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hvc : ({v}ᶜ : Finset V).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton]; omega
  haveI : Nonempty {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} :=
    ⟨⟨{v}, Finset.singleton_nonempty v, hvc⟩⟩
  obtain ⟨U, hU⟩ := exists_eq_ciInf_of_finite
    (f := fun U : {U : Finset V // U.Nonempty ∧ Uᶜ.Nonempty} => ratioCost N U.1)
  unfold minCut; rw [← hU]
  unfold ratioCost
  have h1 : (0:ℝ) < U.1.card := by exact_mod_cast U.2.1.card_pos
  have h2 : (0:ℝ) < U.1ᶜ.card := by exact_mod_cast U.2.2.card_pos
  exact div_pos (hconn _ U.2.1 U.2.2) (by positivity)

theorem lemma_21_core {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (L : ℝ)
    (hL : 12 * cmax N * Real.log (Fintype.card V : ℝ) /
      ((Fintype.card V : ℝ) * minCut N) ≤ L)
    (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ)) :
    ∑ u ∈ Tᶜ, distFromL N d (L / 4) T u ≤
      ENNReal.ofReal (6 * totalWeight N d /
        ((Fintype.card V : ℝ) * minCut N)) := by
  have hS := l21_minCut_pos N hn hconn
  have hM : ∀ v, ∑ u, N.C u v ≤ cmax N := by
    intro v
    have : ∑ u, N.C v u ≤ cmax N :=
      le_csSup (Set.finite_range _).bddAbove ⟨v, rfl⟩
    calc ∑ u, N.C u v = ∑ u, N.C v u := Finset.sum_congr rfl fun u _ => N.C_symm u v
      _ ≤ _ := this
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  have hvc : ({v0}ᶜ : Finset V).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_singleton]; omega
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hSM : minCut N * ((Fintype.card V : ℝ) - 1) ≤ cmax N := by
    have h := l21_minCut_le N {v0} (Finset.singleton_nonempty v0) hvc
    rw [Finset.card_compl, Finset.card_singleton, Nat.cast_sub (by omega)] at h
    have h2 : cutCap N {v0} ≤ cmax N := by
      unfold cutCap
      rw [Finset.sum_singleton]
      calc ∑ w ∈ ({v0}ᶜ : Finset V), N.C v0 w ≤ ∑ w, N.C v0 w :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => N.C_nonneg _ _)
        _ = ∑ w, N.C w v0 := Finset.sum_congr rfl fun w _ => N.C_symm v0 w
        _ ≤ _ := hM v0
    push_cast at h
    linarith
  have hMpos : 0 < cmax N := by nlinarith
  have hq : (Fintype.card V : ℝ) * minCut N ≤ 3 * cmax N := by nlinarith
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos]
    have : (0:ℝ) < T.card := by linarith
    exact_mod_cast this
  let F : ℕ → V → ENNReal := fun k u => distFromL N d (k : ℝ) T u
  have hF0 : ∀ k, ∀ t ∈ T, F k t = 0 := fun k t ht =>
    l21_distFromL_mem N d (Nat.cast_nonneg k) T t ht
  have hF1 : ∀ k u v, 0 < N.C u v → F (k+1) v ≤ F k u + ENNReal.ofReal (d u v) :=
    fun k u v h => l21_distFromL_step N hd T k u v h
  have hF2 : ∀ k u, F (k+1) u ≤ F k u := fun k u =>
    l21_distFromL_anti N d (by push_cast; linarith) T u
  have hlogpos : 0 < Real.log (Fintype.card V : ℝ) := Real.log_pos (by linarith)
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨ρ, hρ, hm, hpot⟩ := l21_main N d hd F T hF0 hF1 hF2 (cmax N) (minCut N) hM hMpos hS
    (fun U hU hUc => l21_minCut_le N U hU hUc) hT hTne hq ⌊L / 4⌋₊
  set K := ⌊L / 4⌋₊ with hKdef
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  set S := minCut N
  set M := cmax N
  set q := n * S / (3 * M) with hqdef
  have hqpos : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hqdef, div_le_one (by positivity)]; exact hq
  have hL4 : Real.log n / q ≤ L / 4 := by
    have : Real.log n / q = 12 * M * Real.log n / (n * S) / 4 := by
      rw [hqdef]; field_simp; ring
    rw [this]; linarith
  have hK : L / 4 < K + 1 := Nat.lt_floor_add_one _
  have hlt : n / 3 * (1 - q) ^ K < 1 := by
    have h1 : (1 - q) ^ K ≤ Real.exp (-q) ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) K
    have h2 : Real.exp (-q) ^ K = Real.exp (-(q * K)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : -(q * K) < q - Real.log n := by
      have h' := (div_le_iff₀ hqpos).1 hL4
      have : Real.log n < q * (K + 1) := by nlinarith
      linarith
    have h4 : Real.exp (q - Real.log n) = Real.exp q / n := by
      rw [Real.exp_sub, Real.exp_log (by linarith)]
    have h5 : Real.exp q ≤ Real.exp 1 := Real.exp_le_exp.2 hq1
    have h6 := Real.exp_one_lt_d9
    calc n / 3 * (1 - q) ^ K ≤ n / 3 * Real.exp (-(q * K)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ < n / 3 * Real.exp (q - Real.log n) :=
          mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 h3) (by positivity)
      _ = Real.exp q / 3 := by rw [h4]; field_simp
      _ < 1 := by linarith
  have hempty : (l21B F K ρ)ᶜ = ∅ := by
    have h1 : ((l21B F K ρ)ᶜ.card : ℝ) < 1 := lt_of_le_of_lt hm hlt
    have h2 : (l21B F K ρ)ᶜ.card < 1 := by exact_mod_cast h1
    exact Finset.card_eq_zero.1 (by omega)
  have hall : ∀ u, F K u ≤ ENNReal.ofReal ρ := by
    intro u
    have : u ∈ l21B F K ρ := by
      by_contra h
      have h' : u ∈ (l21B F K ρ)ᶜ := Finset.mem_compl.2 h
      rw [hempty] at h'; simp at h'
    exact (l21_mem_B F K ρ u).1 this
  have hResnn : 0 ≤ l21Res N d F K ρ :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg _ _) (l21_res_nonneg d hd F K ρ u v)
  have hPot : l21Pot T F K ρ ≤ 6 * totalWeight N d / (n * S) := by
    have : 0 ≤ 3 / (n * S) * l21Res N d F K ρ := mul_nonneg (by positivity) hResnn
    linarith
  have hPot' : ∑ u ∈ Tᶜ, (F K u).toReal ≤ 6 * totalWeight N d / (n * S) := by
    unfold l21Pot at hPot
    rwa [Finset.sum_congr rfl fun u _ => by rw [min_eq_left (hall u)]] at hPot
  calc ∑ u ∈ Tᶜ, distFromL N d (L / 4) T u ≤ ∑ u ∈ Tᶜ, F K u :=
        Finset.sum_le_sum fun u _ =>
          l21_distFromL_anti N d (Nat.floor_le (by positivity)) T u
    _ = ∑ u ∈ Tᶜ, ENNReal.ofReal (F K u).toReal :=
        Finset.sum_congr rfl fun u _ =>
          (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hall u))).symm
    _ = ENNReal.ofReal (∑ u ∈ Tᶜ, (F K u).toReal) :=
        (ENNReal.ofReal_sum_of_nonneg fun _ _ => ENNReal.toReal_nonneg).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hPot'

end LeightonRao.ShortPaths

open LeightonRao.ShortPaths


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (L : ℝ)
    (hL : 12 * cmax N * Real.log (Fintype.card V : ℝ) /
      ((Fintype.card V : ℝ) * minCut N) ≤ L)
    (T : Finset V)
    (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ)) :
    ∑ u ∈ Tᶜ, distFromL N d (L / 4) T u ≤
      ENNReal.ofReal (6 * totalWeight N d /
        ((Fintype.card V : ℝ) * minCut N)) := by
  exact lemma_21_core N hn hconn d hd L hL T hT
