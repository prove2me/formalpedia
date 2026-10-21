-- Prove2me | solution 1 for GivenDegreeSeq.Interior.gf_nonneg_of_mem_F
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:55:25.04501+00:00
-- url     : https://prove2.me/submissions/ca7fd8df-03b4-40fc-bfc3-1128ed53c522

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit

set_option autoImplicit false
open GivenDegreeSeq.Interior MeasureTheory intervalIntegral

open Classical in
lemma gdi_eg_nec {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    ∑ v ∈ A, G.degree v ≤ A.card * (A.card - 1) + ∑ u ∈ Aᶜ, min (G.degree u) A.card := by
  have hdeg : ∀ v, G.degree v = ∑ w, if G.Adj v w then 1 else 0 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
      Finset.card_filter]
  have hsplit : ∀ v, G.degree v = (∑ w ∈ A, if G.Adj v w then 1 else 0) +
      ∑ w ∈ Aᶜ, if G.Adj v w then 1 else 0 := by
    intro v
    rw [hdeg v, ← Finset.sum_add_sum_compl A]
  have h1 : ∀ v ∈ A, (∑ w ∈ A, if G.Adj v w then 1 else 0) ≤ A.card - 1 := by
    intro v hv
    calc (∑ w ∈ A, if G.Adj v w then 1 else 0)
        ≤ ∑ w ∈ A.erase v, 1 := by
          rw [← Finset.add_sum_erase _ _ hv]
          simp only [SimpleGraph.irrefl, if_false, zero_add]
          exact Finset.sum_le_sum (fun w _ => by split_ifs <;> simp)
      _ = A.card - 1 := by simp [Finset.card_erase_of_mem hv]
  have h2 : ∑ v ∈ A, (∑ w ∈ Aᶜ, if G.Adj v w then 1 else 0) =
      ∑ w ∈ Aᶜ, ∑ v ∈ A, if G.Adj v w then 1 else 0 := Finset.sum_comm
  have h3 : ∀ w ∈ Aᶜ, (∑ v ∈ A, if G.Adj v w then 1 else 0) ≤ min (G.degree w) A.card := by
    intro w _
    apply le_min
    · rw [hdeg w]
      calc (∑ v ∈ A, if G.Adj v w then 1 else 0)
          ≤ ∑ v, if G.Adj v w then 1 else 0 :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ A)
        _ = ∑ v, if G.Adj w v then 1 else 0 :=
            Finset.sum_congr rfl (fun v _ => by simp [G.adj_comm])
    · calc (∑ v ∈ A, if G.Adj v w then 1 else 0) ≤ ∑ v ∈ A, 1 :=
            Finset.sum_le_sum (fun v _ => by split_ifs <;> simp)
        _ = A.card := by simp
  calc ∑ v ∈ A, G.degree v
      = ∑ v ∈ A, ((∑ w ∈ A, if G.Adj v w then 1 else 0) +
          ∑ w ∈ Aᶜ, if G.Adj v w then 1 else 0) := Finset.sum_congr rfl (fun v _ => hsplit v)
    _ = ∑ v ∈ A, (∑ w ∈ A, if G.Adj v w then 1 else 0) +
          ∑ v ∈ A, (∑ w ∈ Aᶜ, if G.Adj v w then 1 else 0) := Finset.sum_add_distrib
    _ ≤ ∑ v ∈ A, (A.card - 1) + ∑ w ∈ Aᶜ, min (G.degree w) A.card := by
        apply add_le_add (Finset.sum_le_sum h1)
        rw [h2]
        exact Finset.sum_le_sum h3
    _ = A.card * (A.card - 1) + ∑ u ∈ Aᶜ, min (G.degree u) A.card := by simp

lemma gdi_int_anti (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (a b : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable f volume a b := by
  apply AntitoneOn.intervalIntegrable
  intro x hx y hy hxy
  have h01 : Set.uIcc a b ⊆ Set.Icc (0:ℝ) 1 := Set.uIcc_subset_Icc ha hb
  exact hf (h01 hx) (h01 hy) hxy

lemma gdi_min_anti (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (x : ℝ) :
    AntitoneOn (fun y => min (f y) x) (Set.Icc 0 1) := by
  intro a ha b hb hab
  exact min_le_min_right _ (hf ha hb hab)

lemma gdi_R2 (g : ℝ → ℝ) (hg : AntitoneOn g (Set.Icc 0 1)) (c h : ℝ) (hh : 0 < h) (hc : 0 ≤ c)
    (m : ℕ) (hm : c + m * h ≤ 1) :
    h * ∑ j ∈ Finset.range m, g (c + (j + 1) * h) ≤ ∫ t in c..c + m * h, g t := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast at hm ⊢
    have hmm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hm' : c + (m:ℝ) * h ≤ 1 := by nlinarith
    have ha : c ∈ Set.Icc (0:ℝ) 1 := ⟨hc, by nlinarith⟩
    have hb : c + (m:ℝ) * h ∈ Set.Icc (0:ℝ) 1 := ⟨by nlinarith, hm'⟩
    have hq : c + ((m:ℝ) + 1) * h ∈ Set.Icc (0:ℝ) 1 := ⟨by nlinarith, hm⟩
    have e : c + ((m:ℝ) + 1) * h = (c + (m:ℝ) * h) + h := by ring
    rw [Finset.sum_range_succ, mul_add, ← integral_add_adjacent_intervals
      (gdi_int_anti g hg c _ ha hb) (gdi_int_anti g hg _ (c + ((m:ℝ) + 1) * h) hb hq)]
    have ih' := ih hm'
    have key : h * g (c + ((m:ℝ) + 1) * h) ≤ ∫ t in (c + (m:ℝ) * h)..(c + ((m:ℝ) + 1) * h), g t := by
      have h1 : ∫ t in (c + (m:ℝ) * h)..(c + ((m:ℝ) + 1) * h), g (c + ((m:ℝ) + 1) * h) =
          h * g (c + ((m:ℝ) + 1) * h) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, e]; ring_nf
      rw [← h1]
      apply intervalIntegral.integral_mono_on (by rw [e]; linarith) intervalIntegrable_const
        (gdi_int_anti g hg _ _ hb hq)
      intro t ht
      exact hg (⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1) hq ht.2
    linarith

lemma gdi_R1 (g : ℝ → ℝ) (hg : AntitoneOn g (Set.Icc 0 1)) (c h : ℝ) (hh : 0 < h) (hc : 0 ≤ c)
    (m : ℕ) (hm : c + m * h ≤ 1) :
    ∫ t in c..c + m * h, g t ≤ h * ∑ j ∈ Finset.range m, g (c + j * h) := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast at hm ⊢
    have hmm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hm' : c + (m:ℝ) * h ≤ 1 := by nlinarith
    have ha : c ∈ Set.Icc (0:ℝ) 1 := ⟨hc, by nlinarith⟩
    have hb : c + (m:ℝ) * h ∈ Set.Icc (0:ℝ) 1 := ⟨by nlinarith, hm'⟩
    have hq : c + ((m:ℝ) + 1) * h ∈ Set.Icc (0:ℝ) 1 := ⟨by nlinarith, hm⟩
    have e : c + ((m:ℝ) + 1) * h = (c + (m:ℝ) * h) + h := by ring
    rw [Finset.sum_range_succ, mul_add, ← integral_add_adjacent_intervals
      (gdi_int_anti g hg c _ ha hb) (gdi_int_anti g hg _ (c + ((m:ℝ) + 1) * h) hb hq)]
    have ih' := ih hm'
    have key : ∫ t in (c + (m:ℝ) * h)..(c + ((m:ℝ) + 1) * h), g t ≤ h * g (c + (m:ℝ) * h) := by
      have h1 : ∫ t in (c + (m:ℝ) * h)..(c + ((m:ℝ) + 1) * h), g (c + (m:ℝ) * h) =
          h * g (c + (m:ℝ) * h) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, e]; ring_nf
      rw [← h1]
      apply intervalIntegral.integral_mono_on (by rw [e]; linarith)
        (gdi_int_anti g hg _ _ hb hq) intervalIntegrable_const
      intro t ht
      exact hg hb (⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ : t ∈ Set.Icc (0:ℝ) 1) ht.1
    linarith

lemma gdi_eg_fin {n : ℕ} (d : Fin n → ℕ) (hg : IsGraphic d) (k : ℕ) (hk : k ≤ n) :
    ∑ i : Fin n, (if (i : ℕ) < k then (d i : ℝ) else 0) ≤
      (k : ℝ) * ((k : ℝ) - 1) + ∑ i : Fin n, (if (i : ℕ) < k then 0 else min (d i : ℝ) (k : ℝ)) := by
  classical
  obtain ⟨G, hG⟩ := hg
  have h := gdi_eg_nec G (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k))
  have hcard : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).card = k := by
    rw [Fin.card_filter_val_lt]; exact min_eq_right hk
  rw [hcard] at h
  have hc : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k))ᶜ =
      Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < k) := by
    ext i; simp
  rw [hc] at h
  have h' : (∑ v ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), d v : ℕ) ≤
      k * (k - 1) + ∑ u ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < k), min (d u) k := by
    have e1 : ∑ v ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), d v =
        ∑ v ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), G.degree v :=
      Finset.sum_congr rfl (fun v _ => (hG v).symm)
    have e2 : ∑ v ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < k), min (d v) k =
        ∑ v ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < k), min (G.degree v) k :=
      Finset.sum_congr rfl (fun v _ => by rw [hG v])
    rw [e1, e2]; exact h
  have h'' : ((∑ v ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), d v : ℕ) : ℝ) ≤
      ((k * (k - 1) + ∑ u ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < k), min (d u) k : ℕ) : ℝ) :=
    by exact_mod_cast h'
  rw [Finset.sum_filter, Finset.sum_filter] at h''
  push_cast at h''
  have e3 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (by rw [Nat.cast_sub h0]; simp)
  have e4 : (∑ x : Fin n, if ¬(x : ℕ) < k then min (d x : ℝ) (k : ℝ) else 0) =
      ∑ i : Fin n, if (i : ℕ) < k then 0 else min (d i : ℝ) (k : ℝ) :=
    Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp_all)
  rw [e4] at h''
  rcases e3 with e3 | e3
  · rw [e3] at h''; exact h''
  · subst e3
    simp only [Nat.cast_zero, zero_mul, zero_add] at h'' ⊢
    exact h''

lemma gdi_discrete (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) (n : ℕ) (hn : 0 < n)
    (d : Fin n → ℕ) (hg : IsGraphic d) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    -((f 0 - f 1) / n + 2 * ((1 / (n:ℝ)) * ∑ i : Fin n, |(d i : ℝ) / n - f (((i:ℕ) + 1 : ℝ) / n)|))
      ≤ Gf f ((k:ℝ) / n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hknR : (k:ℝ) ≤ n := by exact_mod_cast hkn
  set x' : ℝ := (k:ℝ) / n with hx'
  have hx'0 : 0 ≤ x' := by positivity
  have hx'1 : x' ≤ 1 := by rw [hx', div_le_one hnR]; exact hknR
  set F : Fin n → ℝ := fun i => f (((i:ℕ) + 1 : ℝ) / n) with hF
  set a : Fin n → ℝ := fun i => (d i : ℝ) / n with ha
  set E' : ℝ := ∑ i : Fin n, |a i - F i| with hE'
  have eg := gdi_eg_fin d hg k hkn
  have eg2 : (∑ i : Fin n, if (i:ℕ) < k then a i else 0) ≤
      x' * ((k:ℝ) - 1) + ∑ i : Fin n, if (i:ℕ) < k then 0 else min (a i) x' := by
    have h1 := div_le_div_of_nonneg_right eg hnR.le
    have e1 : (∑ i : Fin n, if (i : ℕ) < k then (d i : ℝ) else 0) / n =
        ∑ i : Fin n, if (i:ℕ) < k then a i else 0 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp [ha])
    have e2 : ((k : ℝ) * ((k : ℝ) - 1) + ∑ i : Fin n, (if (i : ℕ) < k then 0 else min (d i : ℝ) (k : ℝ))) / n =
        x' * ((k:ℝ) - 1) + ∑ i : Fin n, if (i:ℕ) < k then 0 else min (a i) x' := by
      rw [add_div, Finset.sum_div, hx']
      congr 1
      · ring
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        split_ifs
        · simp
        · simp only [ha]; rw [min_div_div_right hnR.le]
    rw [e1, e2] at h1
    exact h1
  -- comparison of a and F
  have b1 : |(∑ i : Fin n, if (i:ℕ) < k then a i else 0) - ∑ i : Fin n, if (i:ℕ) < k then F i else 0| ≤ E' := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    split_ifs <;> simp
  have b2 : |(∑ i : Fin n, if (i:ℕ) < k then 0 else min (a i) x') -
      ∑ i : Fin n, if (i:ℕ) < k then 0 else min (F i) x'| ≤ E' := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    split_ifs
    · simp
    · have := abs_min_sub_min_le_max (a i) x' (F i) x'
      simpa using this
  rw [abs_le] at b1 b2
  have hS1 : (∑ i : Fin n, if (i:ℕ) < k then F i else 0) ≤
      x' * ((k:ℝ) - 1) + (∑ i : Fin n, if (i:ℕ) < k then 0 else min (F i) x') + 2 * E' := by
    linarith [b1.1, b1.2, b2.1, b2.2]
  -- sums to range sums
  have hS1' : (∑ i : Fin n, if (i:ℕ) < k then F i else 0) =
      ∑ j ∈ Finset.range k, f (((j:ℕ) + 1 : ℝ) / n) := by
    have := Fin.sum_univ_eq_sum_range (fun j : ℕ => if j < k then f (((j:ℝ) + 1) / n) else 0) n
    simp only [hF]
    rw [this, ← Finset.sum_range_add_sum_Ico _ hkn]
    have e1 : ∑ j ∈ Finset.range k, (if j < k then f (((j:ℝ) + 1) / n) else 0) =
        ∑ j ∈ Finset.range k, f (((j:ℝ) + 1) / n) :=
      Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.1 hj))
    have e2 : ∑ j ∈ Finset.Ico k n, (if j < k then f (((j:ℝ) + 1) / n) else 0) = 0 :=
      Finset.sum_eq_zero (fun j hj => if_neg (by have := (Finset.mem_Ico.1 hj).1; omega))
    rw [e1, e2, add_zero]
  have hS2' : (∑ i : Fin n, if (i:ℕ) < k then 0 else min (F i) x') =
      ∑ j ∈ Finset.range (n - k), min (f ((((k + j : ℕ) : ℝ) + 1) / n)) x' := by
    have := Fin.sum_univ_eq_sum_range
      (fun j : ℕ => if j < k then (0:ℝ) else min (f (((j:ℝ) + 1) / n)) x') n
    simp only [hF]
    rw [this, ← Finset.sum_range_add_sum_Ico _ hkn]
    have e1 : ∑ j ∈ Finset.range k, (if j < k then (0:ℝ) else min (f (((j:ℝ) + 1) / n)) x') = 0 :=
      Finset.sum_eq_zero (fun j hj => if_pos (Finset.mem_range.1 hj))
    have e2 : ∑ j ∈ Finset.Ico k n, (if j < k then (0:ℝ) else min (f (((j:ℝ) + 1) / n)) x') =
        ∑ j ∈ Finset.Ico k n, min (f (((j:ℝ) + 1) / n)) x' :=
      Finset.sum_congr rfl (fun j hj => if_neg (by have := (Finset.mem_Ico.1 hj).1; omega))
    rw [e1, e2, zero_add, Finset.sum_Ico_eq_sum_range]
  -- Riemann bounds
  have hh : (0:ℝ) < 1 / n := by positivity
  have R1 := gdi_R1 f hf 0 (1 / n) hh le_rfl k (by
    rw [zero_add, ← div_eq_mul_one_div]; exact hx'1)
  have R2 := gdi_R2 (fun y => min (f y) x') (gdi_min_anti f hf x') x' (1 / n) hh hx'0 (n - k) (by
    rw [Nat.cast_sub hkn, hx']; field_simp; linarith)
  have lim1 : (0:ℝ) + (k:ℝ) * (1 / n) = x' := by rw [hx']; ring
  have lim2 : x' + ((n - k : ℕ) : ℝ) * (1 / n) = 1 := by
    rw [Nat.cast_sub hkn, hx']; field_simp; ring
  rw [lim1] at R1
  simp only [lim2] at R2
  have sumR1 : ∑ j ∈ Finset.range k, f (0 + (j:ℝ) * (1 / n)) =
      (∑ j ∈ Finset.range k, f (((j:ℕ) + 1 : ℝ) / n)) + f 0 - f x' := by
    have s1 := Finset.sum_range_succ' (fun j : ℕ => f ((j:ℝ) / n)) k
    have s2 := Finset.sum_range_succ (fun j : ℕ => f ((j:ℝ) / n)) k
    have e1 : ∑ j ∈ Finset.range k, f (0 + (j:ℝ) * (1 / n)) = ∑ j ∈ Finset.range k, f ((j:ℝ) / n) :=
      Finset.sum_congr rfl (fun j _ => by congr 1; ring)
    have e2 : ∑ j ∈ Finset.range k, f (((j + 1 : ℕ) : ℝ) / n) =
        ∑ j ∈ Finset.range k, f (((j:ℕ) + 1 : ℝ) / n) :=
      Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    rw [e1]
    simp only [Nat.cast_zero, zero_div] at s1
    rw [e2] at s1
    rw [← hx'] at s2
    linarith
  have sumR2 : ∑ j ∈ Finset.range (n - k), min (f (x' + ((j:ℝ) + 1) * (1 / n))) x' =
      ∑ j ∈ Finset.range (n - k), min (f ((((k + j : ℕ) : ℝ) + 1) / n)) x' :=
    Finset.sum_congr rfl (fun j _ => by
      congr 2
      push_cast; rw [hx']; field_simp; ring)
  rw [sumR1] at R1
  rw [sumR2] at R2
  have hfx : f 1 ≤ f x' := hf ⟨hx'0, hx'1⟩ ⟨zero_le_one, le_rfl⟩ hx'1
  have hk' : (k:ℝ) = n * x' := by rw [hx']; field_simp
  have hE0 : 0 ≤ E' := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  rw [hS1', hS2'] at hS1
  unfold Gf
  have e3 : 1 / (n:ℝ) * (x' * ((k:ℝ) - 1)) = x' ^ 2 - x' / n := by
    rw [hk']; field_simp
  have key := mul_le_mul_of_nonneg_left hS1 hh.le
  have e4 : 1 / (n:ℝ) * E' = (1 / (n:ℝ)) * ∑ i : Fin n, |a i - F i| := rfl
  have hxn : 0 ≤ x' / n := by positivity
  have e5 : (f 0 - f 1) / n = 1 / (n:ℝ) * (f 0 - f 1) := by ring
  nlinarith [R1, R2, key, e3, hfx, hxn, e5]

lemma gdi_T1_lip (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc 0 1)) :
    LipschitzOnWith (|f 0| + |f 1| + 2).toNNReal
      (fun x => ∫ y in x..1, min (f y) x) (Set.Icc 0 1) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hM : (0:ℝ) ≤ |f 0| + |f 1| + 2 := by positivity
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx x0 hx0
  rw [Real.coe_toNNReal _ hM, Real.dist_eq, Real.dist_eq]
  have Mx := gdi_int_anti _ (gdi_min_anti f hf x) x 1 hx h1
  have Mx0 := gdi_int_anti _ (gdi_min_anti f hf x0) x 1 hx h1
  have Mx0' := gdi_int_anti _ (gdi_min_anti f hf x0) x x0 hx hx0
  have Mx0'' := gdi_int_anti _ (gdi_min_anti f hf x0) x0 1 hx0 h1
  have e : (∫ y in x..1, min (f y) x) - ∫ y in x0..1, min (f y) x0 =
      (∫ y in x..1, (min (f y) x - min (f y) x0)) + ∫ y in x..x0, min (f y) x0 := by
    rw [integral_sub Mx Mx0, ← integral_add_adjacent_intervals Mx0' Mx0'']
    ring
  rw [e]
  have b1 : ‖∫ y in x..1, (min (f y) x - min (f y) x0)‖ ≤ |x - x0| * |1 - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y _
    have := abs_min_sub_min_le_max (f y) x (f y) x0
    simpa using this
  have b2 : ‖∫ y in x..x0, min (f y) x0‖ ≤ (|f 0| + |f 1| + 1) * |x0 - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ Set.Icc (0:ℝ) 1 := Set.uIcc_subset_Icc hx hx0 (Set.uIoc_subset_uIcc hy)
    have a1 := hf h0 hy' hy'.1
    have a2 := hf hy' h1 hy'.2
    have a3 : |f y| ≤ |f 0| + |f 1| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le (f 0), neg_abs_le (f 1), le_abs_self (f 0), le_abs_self (f 1)]
    have a4 := abs_min_sub_min_le_max (f y) x0 (0:ℝ) 0
    have a5 : |min (f y) x0| ≤ |f y| + 1 := by
      have := hx0.2
      have h6 : |min (f y) x0| ≤ max |f y| |x0| := by
        rcases min_choice (f y) x0 with h | h <;> rw [h]
        · exact le_max_left _ _
        · exact le_max_right _ _
      have h7 : |x0| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx0.1, hx0.2]
      rcases max_cases |f y| |x0| with h | h <;> linarith [abs_nonneg (f y)]
    simpa [Real.norm_eq_abs] using (by linarith : |min (f y) x0| ≤ |f 0| + |f 1| + 1)
  have hx1 : |1 - x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hxx : |x0 - x| = |x - x0| := abs_sub_comm _ _
  have hn : 0 ≤ |x - x0| := abs_nonneg _
  rw [Real.norm_eq_abs] at b1 b2
  calc |(∫ y in x..1, (min (f y) x - min (f y) x0)) + ∫ y in x..x0, min (f y) x0|
      ≤ |∫ y in x..1, (min (f y) x - min (f y) x0)| + |∫ y in x..x0, min (f y) x0| := abs_add_le _ _
    _ ≤ _ := by
      rw [hxx] at b2
      nlinarith [abs_nonneg (f 0), abs_nonneg (f 1), mul_le_mul_of_nonneg_left hx1 hn]

lemma gdi_gf_cont (f : ℝ → ℝ) (hf : InDprime f) :
    ContinuousOn (Gf f) (Set.Icc 0 1) := by
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hT1 := (gdi_T1_lip f hf.1).continuousOn
  have hT3 : ContinuousOn (fun x => ∫ y in (0:ℝ)..x, f y) (Set.Icc 0 1) := by
    have hI : IntegrableOn f (Set.uIcc (0:ℝ) 1) volume := by
      rw [Set.uIcc_of_le zero_le_one]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 (gdi_int_anti f hf.1 0 1 h0 h1)
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := 1) hI
    rwa [Set.uIcc_of_le zero_le_one] at this
  unfold Gf
  exact (hT1.add (continuousOn_pow 2)).sub hT3

theorem solution (f : ℝ → ℝ) (hf : f ∈ setF) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ Gf f x := by
  obtain ⟨hD, d, hd, hanti, hlim⟩ := hf
  have hcont := gdi_gf_cont f hD
  intro x hx
  set k : ℕ → ℕ := fun n => max 1 ⌈x * n⌉₊ with hk
  set u : ℕ → ℝ := fun n => (k n : ℝ) / n with hu
  have hk1 : ∀ n, 1 ≤ k n := fun n => le_max_left _ _
  have hkn : ∀ n, 1 ≤ n → k n ≤ n := by
    intro n hn
    refine max_le hn ?_
    rw [Nat.ceil_le]
    nlinarith [hx.2, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hu_ge : ∀ n, 1 ≤ n → x ≤ u n := by
    intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [hu]; simp only
    rw [le_div_iff₀ hnR]
    have := Nat.le_ceil (x * n)
    have h2 : (⌈x * n⌉₊ : ℝ) ≤ (k n : ℝ) := by exact_mod_cast le_max_right _ _
    linarith
  have hu_le : ∀ n, 1 ≤ n → u n ≤ x + 1 / n := by
    intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    rw [hu]; simp only
    rw [div_le_iff₀ hnR]
    have h0 : 0 ≤ x * n := mul_nonneg hx.1 hnR.le
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : (k n : ℝ) ≤ x * n + 1 := by
      have : (k n : ℝ) = max (1:ℝ) (⌈x * n⌉₊ : ℝ) := by simp [hk]
      rw [this]
      exact max_le (by linarith) h1.le
    have : (x + 1 / (n:ℝ)) * n = x * n + 1 := by field_simp
    linarith
  have hu_mem : ∀ n, 1 ≤ n → u n ∈ Set.Icc (0:ℝ) 1 := by
    intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    refine ⟨by rw [hu]; positivity, ?_⟩
    rw [hu]; simp only
    rw [div_le_one hnR]; exact_mod_cast hkn n hn
  have hutend : Filter.Tendsto u Filter.atTop (nhds x) := by
    have h1 : Filter.Tendsto (fun n : ℕ => x + 1 / (n:ℝ)) Filter.atTop (nhds (x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hu_ge n hn
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hu_le n hn
  have hG : Filter.Tendsto (fun n => Gf f (u n)) Filter.atTop (nhds (Gf f x)) := by
    have := (hcont.continuousWithinAt hx).tendsto
    refine this.comp ?_
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hutend, by filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hu_mem n hn⟩
  have hL : Filter.Tendsto (fun n : ℕ => -((f 0 - f 1) / n + 2 * scalingError d f n)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (f 0 - f 1) / (n:ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h2 := hlim
    have := (h1.add (h2.const_mul 2)).neg
    simpa using this
  refine le_of_tendsto_of_tendsto hL hG ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have key := gdi_discrete f hD.1 n hn0 (d n) (hd n).2 (k n) (hk1 n) (hkn n hn)
  have hse : (1 / (n:ℝ)) * ∑ i : Fin n, |(d n i : ℝ) / n - f (((i:ℕ) + 1 : ℝ) / n)| ≤
      scalingError d f n := by
    unfold scalingError
    rw [dif_pos hn0]
    have := abs_nonneg ((d n ⟨0, hn0⟩ : ℝ) / n - f 0)
    have := abs_nonneg ((d n ⟨n - 1, Nat.sub_lt hn0 Nat.one_pos⟩ : ℝ) / n - f 1)
    linarith
  have : Gf f (u n) = Gf f ((k n : ℝ) / n) := rfl
  rw [this]
  linarith
