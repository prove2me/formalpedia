-- Prove2me | solution 1 for ModernConvex.Spectral.singular_function_sdr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:29:08.628275+00:00
-- url     : https://prove2.me/submissions/e28f6172-f7f3-4b49-b643-70bbdaf1d6f4

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix
open ModernConvex.Spectral

lemma g72mnb_abel (b c w : ℕ → ℝ) (n : ℕ) (hb : ∀ k, k + 1 < n → b (k + 1) ≤ b k)
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
noncomputable def g72mnb_ext {m : ℕ} (g : Fin m → ℝ) (k : ℕ) : ℝ :=
  if h : k < m then g ⟨k, h⟩ else 0

lemma g72mnb_ext_val {m : ℕ} (g : Fin m → ℝ) (i : Fin m) : g72mnb_ext g i = g i := by
  simp [g72mnb_ext, i.2]

lemma g72mnb_sum_ext {m : ℕ} (g : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ Finset.range j, g72mnb_ext g k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), g i := by
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin m, (if (i : ℕ) < j then g i else 0) =
      ∑ i : Fin m, (fun k : ℕ => if k < j then g72mnb_ext g k else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g72mnb_ext_val]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < j then g72mnb_ext g k else 0) m,
    ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

lemma g72mnb_card_R {m : ℕ} (j : ℕ) (hj : j ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  rw [Fin.card_filter_val_lt]; omega

lemma g72mnb_top {m : ℕ} (c : Fin m → ℝ) (hc : Antitone c) (s : Finset (Fin m)) (j : ℕ)
    (hs : s.card = j) :
    ∑ i ∈ s, c i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), c i := by
  set R := Finset.univ.filter (fun i : Fin m => (i : ℕ) < j) with hR
  have hjm : j ≤ m := by rw [← hs]; simpa using Finset.card_le_univ s
  have hRc : R.card = j := g72mnb_card_R j hjm
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

lemma g72mnb_le_sumLargest {m : ℕ} (y : Fin m → ℝ) (s : Finset (Fin m)) (j : ℕ) (hs : s.card = j) :
    ∑ i ∈ s, y i ≤ sumLargest j y := by
  unfold sumLargest
  exact le_ciSup (f := fun s : {s : Finset (Fin m) // s.card = j} => ∑ i ∈ s.1, y i)
    (Set.finite_range _).bddAbove ⟨s, hs⟩

lemma g72mnb_sumLargest_le {m : ℕ} (x : Fin m → ℝ) (π : Equiv.Perm (Fin m)) (hπ : Antitone (x ∘ π))
    (j : ℕ) (hj : j ≤ m) :
    sumLargest j x ≤ ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) := by
  unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, g72mnb_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map π.symm.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := g72mnb_top (x ∘ π) hπ _ j hc
  simpa [Finset.sum_map] using this

lemma g72mnb_sumLargest_perm {m : ℕ} (x : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (j : ℕ) (hj : j ≤ m) :
    sumLargest j (x ∘ σ) ≤ sumLargest j x := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, g72mnb_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  have hc : (s.1.map σ.toEmbedding).card = j := by rw [Finset.card_map]; exact s.2
  have := g72mnb_le_sumLargest x _ j hc
  simpa [Finset.sum_map] using this

lemma g72mnb_sumLargest_convex {m : ℕ} (j : ℕ) (hj : j ≤ m) (y y' : Fin m → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' := by
  conv_lhs => unfold sumLargest
  have : Nonempty {s : Finset (Fin m) // s.card = j} :=
    ⟨⟨_, g72mnb_card_R j hj⟩⟩
  refine ciSup_le fun s => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := g72mnb_le_sumLargest y s.1 j s.2
  have h2 := g72mnb_le_sumLargest y' s.1 j s.2
  nlinarith

lemma g72mnb_antitone_sort {m : ℕ} (x : Fin m → ℝ) : Antitone (x ∘ Tuple.sort (fun i => -x i)) := by
  intro i k hik
  have := Tuple.monotone_sort (fun i => -x i) hik
  simp only [Function.comp_apply] at this ⊢
  linarith

theorem g72mnb_permHull_eq {m : ℕ} (x : Fin m → ℝ) :
    permHull x =
      {y : Fin m → ℝ | (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → sumLargest j y ≤ sumLargest j x) ∧
        ∑ i, y i = ∑ i, x i} := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨σ, rfl⟩
      refine ⟨fun j _ hj => g72mnb_sumLargest_perm x σ j (by omega), ?_⟩
      exact Equiv.sum_comp σ x
    · intro y hy y' hy' a b ha hb hab
      refine ⟨fun j hj1 hj2 => ?_, ?_⟩
      · calc sumLargest j (a • y + b • y') ≤ a * sumLargest j y + b * sumLargest j y' :=
              g72mnb_sumLargest_convex j (by omega) y y' a b ha hb
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
    have hτa : Antitone (a ∘ τ) := g72mnb_antitone_sort a
    have hπx : Antitone (x ∘ π) := g72mnb_antitone_sort x
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
      set b := g72mnb_ext (a ∘ τ)
      set c := g72mnb_ext (x ∘ π)
      set w := g72mnb_ext (y ∘ τ)
      have hb : ∀ k, k + 1 < m → b (k + 1) ≤ b k := by
        intro k hk
        simp only [b, g72mnb_ext, dif_pos hk, dif_pos (show k < m by omega)]
        exact hτa (Fin.le_iff_val_le_val.mpr (by simp))
      have hpart : ∀ j, j ≤ m → ∑ k ∈ Finset.range j, (c k - w k) =
          ∑ k ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x (π k) -
          ∑ i ∈ (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).map τ.toEmbedding, y i := by
        intro j hj
        rw [Finset.sum_sub_distrib, g72mnb_sum_ext _ j hj, g72mnb_sum_ext _ j hj, Finset.sum_map]
        rfl
      have hD : ∀ j, j < m → 0 ≤ ∑ k ∈ Finset.range j, (c k - w k) := by
        intro j hj
        rcases Nat.eq_zero_or_pos j with h0 | hpos
        · subst h0; simp
        rw [hpart j hj.le, sub_nonneg]
        have hc : ((Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).map τ.toEmbedding).card = j := by
          rw [Finset.card_map, g72mnb_card_R j hj.le]
        calc _ ≤ sumLargest j y := g72mnb_le_sumLargest y _ j hc
          _ ≤ sumLargest j x := hy1 j hpos (by omega)
          _ ≤ _ := g72mnb_sumLargest_le x π hπx j hj.le
      have hDm : ∑ k ∈ Finset.range m, (c k - w k) = 0 := by
        rw [hpart m le_rfl]
        have e1 : Finset.univ.filter (fun i : Fin m => (i : ℕ) < m) = Finset.univ := by
          ext i; simp
        rw [e1, Finset.map_univ_equiv, Equiv.sum_comp π x, hy2, sub_self]
      have := g72mnb_abel b c w m hb hD
      rw [hDm, mul_zero] at this
      have hconv : ∑ k ∈ Finset.range m, b k * (c k - w k) =
          ∑ k : Fin m, a (τ k) * (x (π k) - y (τ k)) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => b k * (c k - w k)) m]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [b, c, w, g72mnb_ext_val, Function.comp_apply]
      rw [hconv] at this
      have : 0 ≤ ∑ k : Fin m, (x (π k) * a (τ k) - y (τ k) * a (τ k)) := by
        refine this.trans_eq (Finset.sum_congr rfl fun k _ => by ring)
      rw [Finset.sum_sub_distrib] at this
      linarith
    linarith

lemma g72mnb_eval_comb {m K N : ℕ} (S : EpiLMI m K N) (y1 y2 : Fin m → ℝ) (t : ℝ)
    (u1 u2 : Fin K → ℝ) (a b : ℝ) (hab : a + b = 1) :
    S.eval (a • y1 + b • y2) t (a • u1 + b • u2) = a • S.eval y1 t u1 + b • S.eval y2 t u2 := by
  obtain rfl : b = 1 - a := by linarith
  simp only [EpiLMI.eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  module

lemma g72mnb_sublevel_convex {m K N : ℕ} (g : (Fin m → ℝ) → EReal) (S : EpiLMI m K N)
    (hS : S.Represents g) (t : ℝ) : Convex ℝ {y | g y ≤ (t : EReal)} := by
  intro y1 hy1 y2 hy2 a b ha hb hab
  obtain ⟨u1, hu1⟩ := (hS y1 t).1 hy1
  obtain ⟨u2, hu2⟩ := (hS y2 t).1 hy2
  refine (hS _ t).2 ⟨a • u1 + b • u2, ?_⟩
  rw [g72mnb_eval_comb S y1 y2 t u1 u2 a b hab]
  exact (hu1.smul ha).add (hu2.smul hb)

lemma g72mnb_sumLargest_anti {m : ℕ} (y : Fin m → ℝ) (hy : Antitone y) (j : ℕ) (hj : j ≤ m) :
    sumLargest j y = partialSum j y := by
  apply le_antisymm
  · have := g72mnb_sumLargest_le y (Equiv.refl _) (by simpa using hy) j hj
    simpa [partialSum] using this
  · exact g72mnb_le_sumLargest y _ j (g72mnb_card_R j hj)

lemma g72mnb_partial_ext {m : ℕ} (y : Fin m → ℝ) (j : ℕ) (hj : j ≤ m) :
    partialSum j y = ∑ k ∈ Finset.range j, g72mnb_ext y k := by
  rw [g72mnb_sum_ext y j hj]; rfl

lemma g72mnb_ext_anti {m : ℕ} (x : Fin m → ℝ) (hx : Antitone x) (hx0 : 0 ≤ x) :
    Antitone (g72mnb_ext x) := by
  intro i j hij
  unfold g72mnb_ext
  by_cases hj : j < m
  · rw [dif_pos hj, dif_pos (by omega)]
    exact hx (Fin.le_iff_val_le_val.mpr hij)
  · rw [dif_neg hj]
    split_ifs with hi
    · exact hx0 _
    · exact le_rfl

lemma g72mnb_ext_nonneg {m : ℕ} (x : Fin m → ℝ) (hx0 : 0 ≤ x) (k : ℕ) :
    0 ≤ g72mnb_ext x k := by
  unfold g72mnb_ext; split_ifs
  · exact hx0 _
  · exact le_rfl

/-- the key majorization step: `σ ≥ 0` antitone, weakly submajorized by antitone `x ≥ 0`;
then there is `z` with `0 ≤ z ≤ x` and `σ ∈ permHull z`. -/
lemma g72mnb_exists_z {m : ℕ} (x σ : Fin m → ℝ) (hx : Antitone x) (hx0 : 0 ≤ x)
    (hσ : Antitone σ) (hσ0 : 0 ≤ σ)
    (hpart : ∀ j : ℕ, 1 ≤ j → j ≤ m → partialSum j σ ≤ partialSum j x) :
    ∃ z : Fin m → ℝ, 0 ≤ z ∧ z ≤ x ∧ σ ∈ permHull z := by
  set T : ℝ := ∑ i, σ i with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => hσ0 i
  set xe := g72mnb_ext x with hxe
  let P : ℕ → ℝ := fun j => ∑ k ∈ Finset.range j, xe k
  let Z : ℕ → ℝ := fun j => min (P j) T
  let zN : ℕ → ℝ := fun i => Z (i + 1) - Z i
  have hxe0 : ∀ k, 0 ≤ xe k := g72mnb_ext_nonneg x hx0
  have hxeA : Antitone xe := g72mnb_ext_anti x hx hx0
  have hPs : ∀ i, P (i + 1) = P i + xe i := fun i => Finset.sum_range_succ _ _
  have hZ0 : Z 0 = 0 := by simp [Z, P, hT0]
  have hzN0 : ∀ i, 0 ≤ zN i := by
    intro i; simp only [zN, Z, hPs]
    have := hxe0 i
    rcases le_total (P i + xe i) T with h | h <;> rcases le_total (P i) T with h' | h' <;>
      simp [min_eq_left, min_eq_right, h, h'] <;> linarith
  have hzNle : ∀ i, zN i ≤ xe i := by
    intro i; simp only [zN, Z, hPs]
    have := hxe0 i
    rcases le_total (P i + xe i) T with h | h <;> rcases le_total (P i) T with h' | h' <;>
      simp [min_eq_left, min_eq_right, h, h'] <;> linarith
  have hzNA : ∀ i, zN (i + 1) ≤ zN i := by
    intro i; simp only [zN, Z, hPs]
    have h1 := hxe0 i; have h2 := hxe0 (i + 1); have h3 := hxeA (Nat.le_succ i)
    rcases le_total (P i + xe i + xe (i + 1)) T with h | h <;>
      rcases le_total (P i + xe i) T with h' | h' <;>
      rcases le_total (P i) T with h'' | h'' <;>
      simp [min_eq_left, min_eq_right, h, h', h''] <;> linarith
  have hzNsum : ∀ j, ∑ i ∈ Finset.range j, zN i = Z j := by
    intro j; rw [Finset.sum_range_sub (fun i => Z i) j, hZ0, sub_zero]
  let z : Fin m → ℝ := fun i => zN i
  have hze : ∀ k, k < m → g72mnb_ext z k = zN k := by
    intro k hk; simp [g72mnb_ext, hk, z]
  have hzpart : ∀ j, j ≤ m → partialSum j z = Z j := by
    intro j hj
    rw [g72mnb_partial_ext z j hj, ← hzNsum j]
    exact Finset.sum_congr rfl fun k hk => hze k (by simp at hk; omega)
  have hσpart : ∀ j, j ≤ m → partialSum j σ ≤ T := by
    intro j hj
    unfold partialSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => hσ0 i)
  have hxpart : ∀ j, j ≤ m → partialSum j x = P j := fun j hj => g72mnb_partial_ext x j hj
  have hzA : Antitone z := by
    have : Antitone zN := antitone_nat_of_succ_le hzNA
    intro i k hik; exact this (Fin.le_iff_val_le_val.mp hik)
  refine ⟨z, fun i => hzN0 i, fun i => ?_, ?_⟩
  · have := hzNle i; simp only [hxe, g72mnb_ext_val] at this; exact this
  rw [g72mnb_permHull_eq]
  refine ⟨fun j hj1 hj2 => ?_, ?_⟩
  · rw [g72mnb_sumLargest_anti σ hσ j (by omega), g72mnb_sumLargest_anti z hzA j (by omega),
      hzpart j (by omega)]
    exact le_min ((hpart j hj1 (by omega)).trans_eq (hxpart j (by omega))) (hσpart j (by omega))
  · have hall : ∀ y : Fin m → ℝ, ∑ i, y i = partialSum m y := by
      intro y; unfold partialSum; congr 1; ext i; simp [i.2]
    rw [hall z, hzpart m le_rfl]
    show ∑ i, σ i = min (P m) T
    rw [min_eq_right]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [hT, P]
    · rw [← hxpart m le_rfl, hT, hall σ]; exact hpart m hm le_rfl

lemma g72mnb_singVec_anti {k l : ℕ} (X : Matrix (Fin k) (Fin l) ℝ) : Antitone (singVec X) := by
  have hH : (X * Xᵀ).IsHermitian := by
    have := Matrix.isHermitian_mul_conjTranspose_self X
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  intro i j hij
  unfold singVec eigVec
  rw [dif_pos hH]
  exact Real.sqrt_le_sqrt (hH.eigenvalues₀_antitone (by simpa using hij))

lemma g72mnb_singVec_nonneg {k l : ℕ} (X : Matrix (Fin k) (Fin l) ℝ) : 0 ≤ singVec X :=
  fun i => Real.sqrt_nonneg _

theorem g72mnb_main {k l K N : ℕ} (hkl : k ≤ l) (g : (Fin k → ℝ) → EReal)
    (hg : ∀ x, g x ≠ ⊥) (hdom : ∀ x : Fin k → ℝ, ¬ (0 ≤ x) → g x = ⊤)
    (hsym : IsSymmetricFn g)
    (hmono : ∀ x y : Fin k → ℝ, 0 ≤ y → y ≤ x → g x ≠ ⊤ → g y ≤ g x)
    (S : EpiLMI k K N) (hS : S.Represents g) (X : Matrix (Fin k) (Fin l) ℝ) (t : ℝ) :
    g (singVec X) ≤ (t : EReal) ↔
      ∃ (x : Fin k → ℝ) (u : Fin K → ℝ),
        (S.eval x t u).PosSemidef ∧ Antitone x ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → sumLargestSing j X ≤ partialSum j x) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (hS _ t).1 h
    exact ⟨singVec X, u, hu, g72mnb_singVec_anti X, fun j _ _ => le_rfl⟩
  · rintro ⟨x, u, hu, hxA, hpart⟩
    have hgx : g x ≤ (t : EReal) := (hS x t).2 ⟨u, hu⟩
    have hgxt : g x ≠ ⊤ := fun h => by rw [h] at hgx; exact absurd hgx (by simp)
    have hx0 : 0 ≤ x := by
      by_contra h; exact hgxt (hdom x h)
    obtain ⟨z, hz0, hzx, hmem⟩ := g72mnb_exists_z x (singVec X) hxA hx0
      (g72mnb_singVec_anti X) (g72mnb_singVec_nonneg X) hpart
    have hgz : g z ≤ (t : EReal) := (hmono x z hz0 hzx hgxt).trans hgx
    have hsub : permHull z ⊆ {y | g y ≤ (t : EReal)} := by
      refine convexHull_min ?_ (g72mnb_sublevel_convex g S hS t)
      rintro _ ⟨π, rfl⟩
      show g (z ∘ π) ≤ _
      rw [hsym]; exact hgz
    exact hsub hmem

theorem solution {k l K N : ℕ} (hkl : k ≤ l) (g : (Fin k → ℝ) → EReal)
    (hg : ∀ x, g x ≠ ⊥) (hdom : ∀ x : Fin k → ℝ, ¬ (0 ≤ x) → g x = ⊤)
    (hsym : IsSymmetricFn g)
    (hmono : ∀ x y : Fin k → ℝ, 0 ≤ y → y ≤ x → g x ≠ ⊤ → g y ≤ g x)
    (S : EpiLMI k K N) (hS : S.Represents g) (X : Matrix (Fin k) (Fin l) ℝ) (t : ℝ) :
    g (singVec X) ≤ (t : EReal) ↔
      ∃ (x : Fin k → ℝ) (u : Fin K → ℝ),
        (S.eval x t u).PosSemidef ∧ Antitone x ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → sumLargestSing j X ≤ partialSum j x) :=
  g72mnb_main hkl g hg hdom hsym hmono S hS X t
