-- Prove2me | solution 1 for ModernConvex.Spectral.majorization_principle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:44:39.655576+00:00
-- url     : https://prove2.me/submissions/13309f84-3eaf-45da-a5b5-d6dcbb7d3b72

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix
open ModernConvex.Spectral

lemma g71m_abel (b c w : ℕ → ℝ) (n : ℕ) (hb : ∀ k, k + 1 < n → b (k + 1) ≤ b k)
    (hD : ∀ j, j < n → 0 ≤ ∑ k ∈ Finset.range j, (c k - w k)) :
    b (n - 1) * ∑ k ∈ Finset.range n, (c k - w k) ≤ ∑ k ∈ Finset.range n, b k * (c k - w k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => hb k (by omega)) (fun j hj => hD j (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_sub_cancel, mul_add]
    have hDn := hD n (by omega)
    have : b n * ∑ k ∈ Finset.range n, (c k - w k) ≤ b (n - 1) * ∑ k ∈ Finset.range n, (c k - w k) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact mul_le_mul_of_nonneg_right (hb (n - 1) (by omega) |>.trans_eq' (by congr 1; omega)) hDn
    linarith

/-- extension by zero of a `Fin m` vector to `ℕ` -/
noncomputable def g71m_ext {m : ℕ} (g : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : k < m then g ⟨k, h⟩ else 0

lemma g71m_ext_val {m : ℕ} (g : Fin m → ℝ) (i : Fin m) : g71m_ext g i = g i := by
  simp [g71m_ext, i.2]

lemma g71m_sum_ext {m : ℕ} (g : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ Finset.range j, g71m_ext g k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), g i := by
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin m, (if (i : ℕ) < j then g i else 0) =
      ∑ i : Fin m, (fun k : ℕ => if k < j then g71m_ext g k else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g71m_ext_val]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j then g71m_ext g k else 0) m,
    ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

lemma g71m_card_R {m : ℕ} (j : ℕ) (hj : j ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  rw [Fin.card_filter_val_lt]; omega

lemma g71m_top {m : ℕ} (c : Fin m → ℝ) (hc : Antitone c) (s : Finset (Fin m)) (j : ℕ)
    (hs : s.card = j) :
    ∑ i ∈ s, c i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), c i := by
  set R := Finset.univ.filter (fun i : Fin m => (i : ℕ) < j) with hR
  have hjm : j ≤ m := by rw [← hs]; simpa using Finset.card_le_univ s
  have hRc : R.card = j := g71m_card_R j hjm
  have hcard : (s \ R).card = (R \ s).card := by
    have h1 := Finset.card_sdiff_add_card_inter s R
    have h2 := Finset.card_sdiff_add_card_inter R s
    rw [Finset.inter_comm] at h2
    omega
  have hpq : ∀ p ∈ s \ R, ∀ q ∈ R \ s, c p ≤ c q := by
    intro p hp q hq
    simp only [Finset.mem_sdiff, hR, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact hc (Fin.le_iff_val_le_val.mpr (by omega))
  have hdiff : ∑ i ∈ s \ R, c i ≤ ∑ i ∈ R \ s, c i := by
    rcases (s \ R).eq_empty_or_nonempty with he | hne
    · have : R \ s = ∅ := by
        rw [← Finset.card_eq_zero, ← hcard, he, Finset.card_empty]
      rw [he, this]
    · obtain ⟨p0, hp0, hmax⟩ := Finset.exists_max_image (s \ R) c hne
      calc ∑ i ∈ s \ R, c i ≤ (s \ R).card • c p0 := Finset.sum_le_card_nsmul _ _ _ hmax
        _ = (R \ s).card • c p0 := by rw [hcard]
        _ ≤ ∑ i ∈ R \ s, c i := Finset.card_nsmul_le_sum _ _ _ (fun q hq => hpq p0 hp0 q hq)
  rw [← Finset.sum_inter_add_sum_sdiff s R, ← Finset.sum_inter_add_sum_sdiff R s,
    Finset.inter_comm]
  linarith

lemma g71m_le_sumLargest {m : ℕ} (y : Fin m → ℝ) (s : Finset (Fin m)) (j : ℕ) (hs : s.card = j) :
    ∑ i ∈ s, y i ≤ sumLargest j y := by
  unfold sumLargest
  exact le_ciSup (f := fun s : {s : Finset (Fin m) // s.card = j} => ∑ i ∈ s.1, y i)
    (Set.finite_range _).bddAbove ⟨s, hs⟩

lemma g71m_sumLargest_le {m : ℕ} (x : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (hπ : Antitone (x ∘ π))
    (j : ℕ) (hj : j ≤ m) :
    sumLargest j x ≤ ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) := by
  unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, g71m_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map π.symm.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := g71m_top (x ∘ π) hπ _ j hc
  simpa [Finset.sum_map] using this

lemma g71m_sumLargest_perm {m : ℕ} (x : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (j : ℕ) (hj : j ≤ m) :
    sumLargest j (x ∘ σ) ≤ sumLargest j x := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, g71m_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map σ.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := g71m_le_sumLargest x _ j hc
  simpa [Finset.sum_map] using this

lemma g71m_sumLargest_convex {m : ℕ} (j : ℕ) (hj : j ≤ m) (y y' : Fin m → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, g71m_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := g71m_le_sumLargest y s.1 j s.2
  have h2 := g71m_le_sumLargest y' s.1 j s.2
  nlinarith

lemma g71m_antitone_sort {m : ℕ} (x : Fin m → ℝ) : Antitone (x ∘ Tuple.sort (fun i => -x i)) := by
  intro i k hik
  have := Tuple.monotone_sort (fun i => -x i) hik
  simp only [Function.comp_apply] at this ⊢
  linarith

theorem solution {m : ℕ} (x : Fin m → ℝ) :
    permHull x =
      {y : Fin m → ℝ | (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → sumLargest j y ≤ sumLargest j x) ∧
        ∑ i, y i = ∑ i, x i} := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨σ, rfl⟩
      refine ⟨fun j _ hj => g71m_sumLargest_perm x σ j (by omega), ?_⟩
      exact Equiv.sum_comp σ x
    · intro y hy y' hy' a b ha hb hab
      refine ⟨fun j hj1 hj2 => ?_, ?_⟩
      · calc sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' :=
              g71m_sumLargest_convex j (by omega) y y' a b ha hb
          _ ≤ a * sumLargest j x + b * sumLargest j x := by
              have := hy.1 j hj1 hj2; have := hy'.1 j hj1 hj2; nlinarith
          _ = sumLargest j x := by rw [← add_mul, hab, one_mul]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hy.2, hy'.2]
        rw [← add_mul, hab, one_mul]
  · rintro y ⟨hy1, hy2⟩
    by_contra hy
    have hcl : IsClosed (permHull x) :=
      (Set.finite_range (fun σ : Equiv.Perm (Fin m) => x ∘ σ)).isCompact_convexHull ℝ |>.isClosed
    obtain ⟨f, u, hfx, hfy⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hcl hy
    set a : Fin m → ℝ := fun i => f (fun j => if i = j then 1 else 0) with ha
    have hf : ∀ v : Fin m → ℝ, f v = ∑ i, v i * a i := by
      intro v
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) v
      simpa [ha, smul_eq_mul] using this
    set τ := Tuple.sort (fun i => -a i) with hτ
    set π := Tuple.sort (fun i => -x i) with hπ
    have hτa : Antitone (a ∘ τ) := g71m_antitone_sort a
    have hπx : Antitone (x ∘ π) := g71m_antitone_sort x
    set σ0 : Equiv.Perm (Fin m) := τ.symm.trans π with hσ0
    have hmem : x ∘ σ0 ∈ permHull x := subset_convexHull ℝ _ ⟨σ0, rfl⟩
    have h1 := hfx _ hmem
    have hfx0 : f (x ∘ σ0) = ∑ k, x (π k) * a (τ k) := by
      rw [hf, ← Equiv.sum_comp τ]
      simp [hσ0]
    have hfy0 : f y = ∑ k, y (τ k) * a (τ k) := by
      rw [hf, ← Equiv.sum_comp τ]
    -- the key inequality
    have key : ∑ k, y (τ k) * a (τ k) ≤ ∑ k, x (π k) * a (τ k) := by
      set b := g71m_ext (a ∘ τ)
      set c := g71m_ext (x ∘ π)
      set w := g71m_ext (y ∘ τ)
      have hb : ∀ k, k + 1 < m → b (k + 1) ≤ b k := by
        intro k hk
        simp only [b, g71m_ext, dif_pos hk, dif_pos (show k < m by omega)]
        exact hτa (Fin.le_iff_val_le_val.mpr (by simp))
      have hpart : ∀ j, j ≤ m → ∑ k ∈ Finset.range j, (c k - w k) =
          ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) -
          ∑ i ∈ (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).map τ.toEmbedding, y i := by
        intro j hj
        rw [Finset.sum_sub_distrib, g71m_sum_ext _ j hj, g71m_sum_ext _ j hj, Finset.sum_map]
        rfl
      have hD : ∀ j, j < m → 0 ≤ ∑ k ∈ Finset.range j, (c k - w k) := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; simp
        rw [hpart j hj.le, sub_nonneg]
        have hc : ((Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).map τ.toEmbedding).card = j := by
          rw [Finset.card_map, g71m_card_R j hj.le]
        calc _ ≤ sumLargest j y := g71m_le_sumLargest y _ j hc
          _ ≤ sumLargest j x := hy1 j hpos (by omega)
          _ ≤ _ := g71m_sumLargest_le x π hπx j hj.le
      have hDm : ∑ k ∈ Finset.range m, (c k - w k) = 0 := by
        rw [hpart m le_rfl]
        have e1 : Finset.univ.filter (fun i : Fin m => (i : ℕ) < m) = Finset.univ := by
          ext i; simp
        rw [e1, Finset.map_univ_equiv, Equiv.sum_comp π x, hy2, sub_self]
      have := g71m_abel b c w m hb hD
      rw [hDm, mul_zero] at this
      have hconv : ∑ k ∈ Finset.range m, b k * (c k - w k) =
          ∑ k : Fin m, a (τ k) * (x (π k) - y (τ k)) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => b k * (c k - w k)) m]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [b, c, w, g71m_ext_val, Function.comp_apply]
      rw [hconv] at this
      have : 0 ≤ ∑ k : Fin m, (x (π k) * a (τ k) - y (τ k) * a (τ k)) := by
        refine this.trans_eq (Finset.sum_congr rfl fun k _ => by ring)
      rw [Finset.sum_sub_distrib] at this
      linarith
    linarith
