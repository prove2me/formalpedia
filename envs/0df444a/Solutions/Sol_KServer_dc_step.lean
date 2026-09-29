-- Prove2me | solution 1 for KServer.dc_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T04:44:40.630704+00:00
-- url     : https://prove2.me/submissions/9bb44b2d-23f2-4270-a8be-c3e69008aa2f

import Mathlib
import Definitions.Def_KServer_model

open KServer

/-- Two sums whose summands agree off one index differ by that index's contribution. -/
private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- Two sums whose summands agree off two indices differ by those indices' contributions. -/
private theorem sum_diff_two {k : ℕ} (F G : Fin k → ℝ) (p q : Fin k) (hpq : p ≠ q)
    (h : ∀ i, i ≠ p → i ≠ q → F i = G i) :
    ∑ i, F i - ∑ i, G i = (F p - G p) + (F q - G q) := by
  classical
  have hq : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    ← Finset.add_sum_erase _ F hq, ← Finset.add_sum_erase _ G hq,
    Finset.sum_congr rfl (fun i hi => h i
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi))]
  ring

/-- For a sorted configuration the spread is a fixed linear form in the positions. -/
private theorem spread_eq {k : ℕ} (z : Fin k → ℝ) (hz : Monotone z) :
    ∑ i, ∑ j, max (z j - z i) 0 = ∑ m : Fin k, (2 * (m:ℝ) + 1 - (k:ℝ)) * z m := by
  classical
  have cnt1 : ∀ (j : Fin k) (c : ℝ),
      ∑ i : Fin k, (if i ≤ j then c else 0) = ((j:ℝ) + 1) * c := by
    intro j c
    have hset : Finset.univ.filter (fun i : Fin k => i ≤ j) = Finset.Iic j := by ext i; simp
    rw [← Finset.sum_filter, hset, Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
    push_cast
    ring
  have cnt2 : ∀ (i : Fin k) (c : ℝ),
      ∑ j : Fin k, (if i ≤ j then c else 0) = ((k:ℝ) - (i:ℝ)) * c := by
    intro i c
    have hset : Finset.univ.filter (fun j : Fin k => i ≤ j) = Finset.Ici i := by ext j; simp
    rw [← Finset.sum_filter, hset, Finset.sum_const, Fin.card_Ici, nsmul_eq_mul]
    have hik : (i:ℕ) ≤ k := le_of_lt i.2
    rw [Nat.cast_sub hik]
  have hmax : ∀ i j : Fin k,
      max (z j - z i) 0 = (if i ≤ j then z j else 0) - (if i ≤ j then z i else 0) := by
    intro i j
    by_cases h : i ≤ j
    · rw [if_pos h, if_pos h]
      exact max_eq_left (by linarith [hz h])
    · rw [if_neg h, if_neg h, sub_zero]
      push_neg at h
      exact max_eq_right (by linarith [hz h.le])
  have step1 : ∑ i, ∑ j, max (z j - z i) 0
      = (∑ i : Fin k, ∑ j : Fin k, (if i ≤ j then z j else 0))
        - ∑ i : Fin k, ∑ j : Fin k, (if i ≤ j then z i else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hmax i j
  have hA : (∑ i : Fin k, ∑ j : Fin k, (if i ≤ j then z j else 0))
      = ∑ j : Fin k, ((j:ℝ) + 1) * z j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => cnt1 j (z j)
  have hB : (∑ i : Fin k, ∑ j : Fin k, (if i ≤ j then z i else 0))
      = ∑ i : Fin k, ((k:ℝ) - (i:ℝ)) * z i :=
    Finset.sum_congr rfl fun i _ => cnt2 i (z i)
  rw [step1, hA, hB, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem solution (k : ℕ) (hk : 1 ≤ k) (x : Fin k → ℝ) (hx : Monotone x) (r : ℝ) :
    ∃ x' : Fin k → ℝ, Monotone x' ∧ (∃ i, x' i = r) ∧
      ∀ y : Fin k → ℝ, Monotone y → (∃ m, y m = r) →
        moveCost x x'
            + ((k : ℝ) * (∑ i, |x' i - y i|) + ∑ i, ∑ j, max (x' j - x' i) 0)
          ≤ (k : ℝ) * (∑ i, |x i - y i|) + ∑ i, ∑ j, max (x j - x i) 0 := by
  classical
  have hk0 : 0 < k := hk
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hmc : ∀ u v : Fin k → ℝ, moveCost u v = ∑ i, |u i - v i| := by
    intro u v; unfold moveCost; exact Finset.sum_congr rfl fun i _ => Real.dist_eq _ _
  set first : Fin k := ⟨0, hk0⟩ with hfirstdef
  set last : Fin k := ⟨k - 1, by omega⟩ with hlastdef
  have hfirst_le : ∀ b : Fin k, first ≤ b := by
    intro b; simp [hfirstdef, Fin.le_def]
  have hlast_ge : ∀ b : Fin k, b ≤ last := by
    intro b; simp only [hlastdef, Fin.le_def]; omega
  by_cases hhit : ∃ i, x i = r
  · refine ⟨x, hx, hhit, ?_⟩
    intro y _ _
    have h0 : moveCost x x = 0 := by rw [hmc]; simp
    rw [h0]; linarith
  rw [not_exists] at hhit
  by_cases hlo : r < x first
  -- CASE: the request is left of every server; the leftmost one goes to it
  · have hmono : Monotone (Function.update x first r) := by
      intro a b hab
      by_cases ha : a = first
      · rw [ha, Function.update_self]
        by_cases hb : b = first
        · rw [hb, Function.update_self]
        · rw [Function.update_of_ne hb]
          exact le_trans hlo.le (hx (hfirst_le b))
      · have hb : b ≠ first := fun hbf =>
          ha (le_antisymm (hbf ▸ hab) (hfirst_le a))
        rw [Function.update_of_ne ha, Function.update_of_ne hb]
        exact hx hab
    refine ⟨Function.update x first r, hmono, ⟨first, by simp⟩, ?_⟩
    intro y hy hycov
    obtain ⟨m, hm⟩ := hycov
    have hyf : y first ≤ r := by rw [← hm]; exact hy (hfirst_le m)
    have hmv : moveCost x (Function.update x first r) = x first - r := by
      rw [hmc, Finset.sum_eq_single first (fun i _ hi => by
        rw [Function.update_of_ne hi]; simp) (by simp)]
      rw [Function.update_self, abs_of_pos (by linarith)]
    have hmatch : (∑ i, |Function.update x first r i - y i|) - ∑ i, |x i - y i|
        = r - x first := by
      rw [sum_diff_single _ _ first (fun i hi => by rw [Function.update_of_ne hi]),
        Function.update_self,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ r - y first),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ x first - y first)]
      ring
    have hsp : (∑ i, ∑ j, max (Function.update x first r j - Function.update x first r i) 0)
        - ∑ i, ∑ j, max (x j - x i) 0 = (r - x first) * (1 - (k:ℝ)) := by
      rw [spread_eq _ hmono, spread_eq _ hx,
        sum_diff_single _ _ first (fun i hi => by rw [Function.update_of_ne hi]),
        Function.update_self]
      simp only [hfirstdef, Fin.val_mk, Nat.cast_zero]
      ring
    have hkm : (k:ℝ) * (∑ i, |Function.update x first r i - y i|)
        = (k:ℝ) * (∑ i, |x i - y i|) + (k:ℝ) * (r - x first) := by
      have he : (∑ i, |Function.update x first r i - y i|)
          = (∑ i, |x i - y i|) + (r - x first) := by linarith [hmatch]
      rw [he]; ring
    rw [hmv, hkm]
    linarith [hsp]
  rw [not_lt] at hlo
  by_cases hhi : x last < r
  -- CASE: the request is right of every server; the rightmost one goes to it
  · have hmono : Monotone (Function.update x last r) := by
      intro a b hab
      by_cases hb : b = last
      · rw [hb, Function.update_self]
        by_cases ha : a = last
        · rw [ha, Function.update_self]
        · rw [Function.update_of_ne ha]
          exact le_trans (hx (hlast_ge a)) hhi.le
      · have ha : a ≠ last := fun haf =>
          hb (le_antisymm (hlast_ge b) (haf ▸ hab))
        rw [Function.update_of_ne ha, Function.update_of_ne hb]
        exact hx hab
    refine ⟨Function.update x last r, hmono, ⟨last, by simp⟩, ?_⟩
    intro y hy hycov
    obtain ⟨m, hm⟩ := hycov
    have hyl : r ≤ y last := by rw [← hm]; exact hy (hlast_ge m)
    have hmv : moveCost x (Function.update x last r) = r - x last := by
      rw [hmc, Finset.sum_eq_single last (fun i _ hi => by
        rw [Function.update_of_ne hi]; simp) (by simp)]
      rw [Function.update_self, abs_of_neg (by linarith)]
      ring
    have hmatch : (∑ i, |Function.update x last r i - y i|) - ∑ i, |x i - y i|
        = x last - r := by
      rw [sum_diff_single _ _ last (fun i hi => by rw [Function.update_of_ne hi]),
        Function.update_self,
        abs_of_nonpos (by linarith : r - y last ≤ 0),
        abs_of_nonpos (by linarith : x last - y last ≤ 0)]
      ring
    have hlastR : ((last : Fin k) : ℝ) = (k:ℝ) - 1 := by
      simp only [hlastdef, Fin.val_mk]
      rw [Nat.cast_sub hk]
      norm_num
    have hsp : (∑ i, ∑ j, max (Function.update x last r j - Function.update x last r i) 0)
        - ∑ i, ∑ j, max (x j - x i) 0 = (r - x last) * ((k:ℝ) - 1) := by
      rw [spread_eq _ hmono, spread_eq _ hx,
        sum_diff_single _ _ last (fun i hi => by rw [Function.update_of_ne hi]),
        Function.update_self, hlastR]
      ring
    have hkm : (k:ℝ) * (∑ i, |Function.update x last r i - y i|)
        = (k:ℝ) * (∑ i, |x i - y i|) + (k:ℝ) * (x last - r) := by
      have he : (∑ i, |Function.update x last r i - y i|)
          = (∑ i, |x i - y i|) + (x last - r) := by linarith [hmatch]
      rw [he]; ring
    rw [hmv, hkm]
    linarith [hsp]
  rw [not_lt] at hhi
  -- INTERIOR CASE: the request lies strictly between two neighbouring servers,
  -- which both move toward it at equal speed until one arrives
  have hlt1 : x first < r := lt_of_le_of_ne hlo (hhit first)
  have hlt2 : r < x last := lt_of_le_of_ne hhi (Ne.symm (hhit last))
  set T : Finset (Fin k) := Finset.univ.filter (fun i => x i < r) with hTdef
  have hTne : T.Nonempty := ⟨first, by simp [hTdef, hlt1]⟩
  set i : Fin k := T.max' hTne with hidef
  have hiT : i ∈ T := T.max'_mem hTne
  have hxi : x i < r := by simpa [hTdef] using hiT
  have hilast : i ≠ last := fun h => absurd hxi (by rw [h]; linarith)
  have hivlt : (i:ℕ) < k := i.2
  have hine : (i:ℕ) ≠ k - 1 := fun h => hilast (Fin.ext h)
  have hival : (i:ℕ) + 1 < k := by omega
  set i' : Fin k := ⟨(i:ℕ) + 1, hival⟩ with hi'def
  have hii' : i < i' := by simp only [hi'def, Fin.lt_def]; omega
  have hi'T : i' ∉ T := fun h => absurd (T.le_max' i' h) (not_le.mpr hii')
  have hxi' : r < x i' := by
    have hn : ¬ (x i' < r) := by simpa [hTdef] using hi'T
    exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm (hhit i'))
  set δ : ℝ := min (r - x i) (x i' - r) with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ r - x i := min_le_left _ _
  have hδ2 : δ ≤ x i' - r := min_le_right _ _
  set x' : Fin k → ℝ := fun m => if m = i then x i + δ else if m = i' then x i' - δ else x m
    with hx'def
  have hii'ne : i ≠ i' := ne_of_lt hii'
  have hx'i : x' i = x i + δ := by rw [hx'def]; simp
  have hx'i' : x' i' = x i' - δ := by
    rw [hx'def]; simp only []; rw [if_neg (Ne.symm hii'ne)]; simp
  have hx'other : ∀ m : Fin k, m ≠ i → m ≠ i' → x' m = x m := by
    intro m h1 h2
    rw [hx'def]; simp only []; rw [if_neg h1, if_neg h2]
  have hgap : ∀ m : Fin k, m ≠ i → m ≠ i' → m < i ∨ i' < m := by
    intro m h1 h2
    have hm1 : (m:ℕ) ≠ (i:ℕ) := fun h => h1 (Fin.ext h)
    have hm2 : (m:ℕ) ≠ (i:ℕ) + 1 := fun h => h2 (Fin.ext h)
    rcases lt_or_gt_of_ne hm1 with h | h
    · left; exact Fin.lt_def.mpr h
    · right; simp only [hi'def, Fin.lt_def]; omega
  have hxi_le : x' i ≤ r := by rw [hx'i]; linarith
  have hxi'_ge : r ≤ x' i' := by rw [hx'i']; linarith
  have hii'val : x' i ≤ x' i' := le_trans hxi_le hxi'_ge
  have hbelow : ∀ m : Fin k, m < i → x' m ≤ x' i := by
    intro m hmi
    rw [hx'other m (ne_of_lt hmi) (ne_of_lt (lt_trans hmi hii')), hx'i]
    have := hx hmi.le
    linarith
  have habove : ∀ m : Fin k, i' < m → x' i' ≤ x' m := by
    intro m hmi
    rw [hx'other m (ne_of_gt (lt_trans hii' hmi)) (ne_of_gt hmi), hx'i']
    have := hx hmi.le
    linarith
  have hmono : Monotone x' := by
    intro a b hab
    by_cases ha : a = i
    · by_cases hb : b = i
      · rw [ha, hb]
      · by_cases hb' : b = i'
        · rw [ha, hb']; exact hii'val
        · rcases hgap b hb hb' with h | h
          · exact absurd hab (not_le.mpr (by rw [ha]; exact h))
          · rw [ha]; exact le_trans hii'val (habove b h)
    · by_cases ha' : a = i'
      · by_cases hb : b = i
        · exact absurd hab (not_le.mpr (by rw [ha', hb]; exact hii'))
        · by_cases hb' : b = i'
          · rw [ha', hb']
          · rcases hgap b hb hb' with h | h
            · exact absurd hab (not_le.mpr (by rw [ha']; exact lt_trans h hii'))
            · rw [ha']; exact habove b h
      · rcases hgap a ha ha' with hA | hA
        · by_cases hb : b = i
          · rw [hb]; exact hbelow a hA
          · by_cases hb' : b = i'
            · rw [hb']; exact le_trans (hbelow a hA) hii'val
            · rw [hx'other a ha ha', hx'other b hb hb']; exact hx hab
        · by_cases hb : b = i
          · exact absurd hab (not_le.mpr (by rw [hb]; exact lt_trans hii' hA))
          · by_cases hb' : b = i'
            · exact absurd hab (not_le.mpr (by rw [hb']; exact hA))
            · rw [hx'other a ha ha', hx'other b hb hb']; exact hx hab
  have hserve : ∃ mm, x' mm = r := by
    rcases min_cases (r - x i) (x i' - r) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ⟨i, by rw [hx'i, hδdef, h1]; ring⟩
    · exact ⟨i', by rw [hx'i', hδdef, h1]; ring⟩
  refine ⟨x', hmono, hserve, ?_⟩
  intro y hy hycov
  obtain ⟨m, hm⟩ := hycov
  have hmv : moveCost x x' = 2 * δ := by
    rw [hmc]
    have h0 : ∑ _m : Fin k, (0:ℝ) = 0 := by simp
    have hd := sum_diff_two (fun m => |x m - x' m|) (fun _ => (0:ℝ)) i i' hii'ne
      (fun m h1 h2 => by
        show |x m - x' m| = 0
        rw [hx'other m h1 h2]; simp)
    rw [h0] at hd
    simp only [sub_zero] at hd
    rw [hd, hx'i, hx'i', abs_of_nonpos (by linarith : x i - (x i + δ) ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x i' - (x i' - δ))]
    ring
  have hmatch : (∑ i0, |x' i0 - y i0|) - ∑ i0, |x i0 - y i0| ≤ 0 := by
    rw [sum_diff_two _ _ i i' hii'ne (fun mm h1 h2 => by rw [hx'other mm h1 h2])]
    by_cases hcase : r ≤ y i
    · have t1 : |x' i - y i| - |x i - y i| = -δ := by
        rw [hx'i, abs_of_nonpos (by linarith : x i + δ - y i ≤ 0),
          abs_of_nonpos (by linarith : x i - y i ≤ 0)]
        ring
      have t2 : |x' i' - y i'| - |x i' - y i'| ≤ δ := by
        have hb := abs_sub_abs_le_abs_sub (x' i' - y i') (x i' - y i')
        have he : |x' i' - y i' - (x i' - y i')| = δ := by
          rw [hx'i', show x i' - δ - y i' - (x i' - y i') = -δ by ring, abs_neg,
            abs_of_pos hδ0]
        linarith
      linarith
    · push_neg at hcase
      have him : i < m := by
        by_contra hc
        push_neg at hc
        have hle := hy hc
        rw [hm] at hle
        linarith
      have hi'm : i' ≤ m := by
        simp only [hi'def, Fin.le_def]
        have := Fin.lt_def.mp him
        omega
      have hyi' : y i' ≤ r := by rw [← hm]; exact hy hi'm
      have t2 : |x' i' - y i'| - |x i' - y i'| = -δ := by
        rw [hx'i', abs_of_nonneg (by linarith : (0:ℝ) ≤ x i' - δ - y i'),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ x i' - y i')]
        ring
      have t1 : |x' i - y i| - |x i - y i| ≤ δ := by
        have hb := abs_sub_abs_le_abs_sub (x' i - y i) (x i - y i)
        have he : |x' i - y i - (x i - y i)| = δ := by
          rw [hx'i, show x i + δ - y i - (x i - y i) = δ by ring, abs_of_pos hδ0]
        linarith
      linarith
  have hi'R : ((i' : Fin k) : ℝ) = ((i : Fin k):ℝ) + 1 := by
    simp only [hi'def, Fin.val_mk]
    push_cast
    ring
  have hsp : (∑ i0, ∑ j, max (x' j - x' i0) 0) - ∑ i0, ∑ j, max (x j - x i0) 0
      = -(2 * δ) := by
    rw [spread_eq _ hmono, spread_eq _ hx,
      sum_diff_two _ _ i i' hii'ne (fun mm h1 h2 => by rw [hx'other mm h1 h2]),
      hx'i, hx'i', hi'R]
    ring
  have hkm : (k:ℝ) * (∑ i0, |x' i0 - y i0|) ≤ (k:ℝ) * (∑ i0, |x i0 - y i0|) := by
    have hle : (∑ i0, |x' i0 - y i0|) ≤ ∑ i0, |x i0 - y i0| := by linarith
    exact mul_le_mul_of_nonneg_left hle (by linarith)
  rw [hmv]
  linarith
