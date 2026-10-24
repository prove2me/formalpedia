-- Prove2me | solution 1 for LearnAugFL.CMP.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:14:27.782163+00:00
-- url     : https://prove2.me/submissions/f0e55b7c-be5e-4176-ac06-06ec71e526e2

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting
import Theorems.Thm_LearnAugFL_CMP_lemma_17

-- Complete inline local file FamilyBounds.lean


namespace LearnAugFL.CMP.AxisProof

noncomputable def total {n : ℕ} (P : Fin n → Pt) (f : Pt) : ℝ := ∑ i, dist f (P i)

lemma total_nonneg {n : ℕ} (P : Fin n → Pt) (f : Pt) : 0 ≤ total P f :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma total_zero {n : ℕ} (P : Fin n → Pt) (o : Pt) (h : total P o = 0) :
    P = fun _ => o := by
  funext i
  have hi : dist o (P i) ≤ total P o := Finset.single_le_sum
    (fun _ _ => dist_nonneg) (Finset.mem_univ i)
  have hdist : dist o (P i) = 0 := le_antisymm (by simpa [h] using hi) dist_nonneg
  exact (dist_eq_zero.mp hdist).symm

lemma ratio_total {n k : ℕ} (hn : n ≠ 0) (P : Fin n → Pt) (b o : Pt) :
    ratio P b o k = total P (cmp P b k) / total P o := by
  unfold ratio ucost total
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

lemma total_update {n : ℕ} (P : Fin n → Pt) (i : Fin n) (p f : Pt) :
    total (Function.update P i p) f = total P f - dist f (P i) + dist f p := by
  classical
  unfold total
  have hfun : (fun j => dist f (Function.update P i p j)) =
      Function.update (fun j => dist f (P j)) i (dist f p) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => dist f (P j)) (Finset.mem_univ i)
  linarith

lemma total_pos {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (hij : P i ≠ P j) (z : Pt) :
    0 < total P z := by
  refine lt_of_le_of_ne (total_nonneg P z) ?_
  intro he
  have hh := total_zero P z he.symm
  exact hij (by simp [hh])

lemma isOpt_iff {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt) :
    IsOpt P o ↔ ∀ z, total P o ≤ total P z := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simp only [IsOpt, ucost, total, div_le_div_iff_of_pos_right hnR]

lemma continuous_total {n : ℕ} (P : Fin n → Pt) : Continuous (total P) := by
  unfold total
  fun_prop


end LearnAugFL.CMP.AxisProof


namespace LearnAugFL.CMP.AxisProof

lemma median_zero_positive_count (s : Multiset ℝ) (hs : lowerMedian s = 0) :
    2 * (s.filter (fun x => 0 < x)).card ≤ s.card := by
  classical
  by_cases hn : s.card = 0
  · have : s = 0 := Multiset.card_eq_zero.mp hn
    subst s
    simp
  let l := s.sort (· ≤ ·)
  let m := (s.card + 1) / 2 - 1
  have hlen : l.length = s.card := Multiset.length_sort (· ≤ ·)
  have hm : m < l.length := by dsimp [m]; omega
  have hzero : l[m] = 0 := by
    change l.getD m 0 = 0 at hs
    simpa only [List.getD_eq_getElem _ _ hm] using hs
  have hsorted : l.SortedLE := (Multiset.pairwise_sort s (· ≤ ·)).sortedLE
  have htake : (l.take (m+1)).filter (fun x => decide (0 < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi' : i < l.length := by simp only [List.length_take] at hi; omega
    have him : i ≤ m := by simp only [List.length_take] at hi; omega
    have hle : x ≤ 0 := by
      have h := hsorted.getElem_le_getElem_of_le (hi := hi') (hj := hm) him
      simp only [List.getElem_take] at hxi
      simpa only [hxi, hzero] using h
    simpa using not_lt_of_ge hle
  have hcount : (l.filter (fun x => decide (0 < x))).length ≤ l.length - (m+1) := by
    calc
      _ = ((l.drop (m+1)).filter (fun x => decide (0 < x))).length := by
        conv_lhs => rw [← List.take_append_drop (m+1) l, List.filter_append, htake, List.nil_append]
      _ ≤ _ := by
        simpa only [List.length_drop] using List.length_filter_le (fun x : ℝ => decide (0 < x)) (l.drop (m+1))
  have hcard : (l.filter (fun x => decide (0 < x))).length = (s.filter (fun x => 0 < x)).card := by
    have heq := congrArg (fun t : Multiset ℝ => (t.filter (fun x => 0 < x)).card) (Multiset.sort_eq s (· ≤ ·))
    simpa only [Multiset.filter_coe, Multiset.coe_card] using heq
  rw [hcard, hlen] at hcount
  dsimp [m] at hcount
  omega

end LearnAugFL.CMP.AxisProof



namespace LearnAugFL.CMP.AxisProof

lemma norm_axis_x (p : Pt) (hp : p 1 = 0) : ‖p‖ = |p 0| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma norm_axis_y (p : Pt) (hp : p 0 = 0) : ‖p‖ = |p 1| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma horizontal_bound (p o : Pt) (hp : p 1 = 0) (ho0 : o 0 = 0) (ho1 : 0 < o 1)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * o 1 := by
  have hd : dist o p ^ 2 = ‖p‖ ^ 2 + (o 1) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, norm_axis_x p hp]
    simp [ho0, hp, sq_abs]
  have he : (t * dist o p) ^ 2 = (‖p‖ + s * o 1) ^ 2 + (s * ‖p‖ - o 1) ^ 2 := by
    rw [mul_pow, hst, hd]
    ring
  have hnonneg : 0 ≤ t * dist o p := mul_nonneg ht dist_nonneg
  have hnonneg' : 0 ≤ ‖p‖ + s * o 1 := add_nonneg (norm_nonneg p) (mul_nonneg hs ho1.le)
  have hsq := sq_nonneg (s * ‖p‖ - o 1)
  nlinarith

lemma nonpositive_bound (p o : Pt) (hp : onX p ∨ onY p) (hp1 : p 1 ≤ 0)
    (ho0 : o 0 = 0) (ho1 : 0 < o 1) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * o 1 := by
  rcases hp with hp | hp
  · exact horizontal_bound p o hp ho0 ho1 s t hs ht hst
  · have hnorm : ‖p‖ = -p 1 := by rw [norm_axis_y p hp, abs_of_nonpos hp1]
    have hdist : dist o p = o 1 - p 1 := by
      rw [dist_eq_norm, norm_axis_y (o - p) (by change o 0 - p 0 = 0; rw [ho0, hp]; simp)]
      simpa only [PiLp.sub_apply] using abs_of_pos (by linarith : 0 < o 1 - p 1)
    have ht1 : 1 ≤ t := by nlinarith [sq_nonneg s]
    have hts : s ≤ t := by nlinarith
    rw [hnorm, hdist]
    have h1 := mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hp1)
    have h2 := mul_nonneg (sub_nonneg.mpr hts) ho1.le
    nlinarith

lemma positive_bound (p o : Pt) (ho0 : o 0 = 0) (ho1 : 0 < o 1)
    (t : ℝ) (ht : 1 ≤ t) : ‖p‖ ≤ t * dist o p + o 1 := by
  have hnorm : ‖o‖ = o 1 := by rw [norm_axis_y o ho0, abs_of_pos ho1]
  have htriangle := dist_triangle (0 : Pt) o p
  simp only [dist_zero_left, hnorm] at htriangle
  have hscale : dist o p ≤ t * dist o p := by nlinarith [dist_nonneg (x := o) (y := p)]
  linarith

open Classical in
lemma count_weight_sum {n : ℕ} (P : Fin n → Pt) (f : Pt → Prop) (D : ℝ) :
    (∑ i : Fin n, if f (P i) then D else 0) = (count P f : ℝ) * D := by
  classical
  rw [← Finset.sum_filter]
  simp [count, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

lemma total_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho0 : o 0 = 0) (ho1 : 0 < o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i)) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : (1 + s) * count P (fun p => 0 < p 1) ≤ s * n) :
    total P 0 ≤ t * total P o := by
  classical
  have ht1 : 1 ≤ t := by nlinarith [sq_nonneg s]
  have hpoint (i : Fin n) : ‖P i‖ ≤ t * dist o (P i) +
      (if 0 < P i 1 then (1 + s) * o 1 else 0) - s * o 1 := by
    by_cases hi : 0 < P i 1
    · simp only [hi, if_true]
      have h := positive_bound (P i) o ho0 ho1 t ht1
      nlinarith
    · simp only [hi, if_false, add_zero]
      exact nonpositive_bound (P i) o (haxes i) (le_of_not_gt hi) ho0 ho1 s t hs ht hst
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 1) ((1 + s) * o 1)] at hsum
  have hc := mul_le_mul_of_nonneg_right hcount ho1.le
  simp only [total, dist_zero_left]
  nlinarith

lemma ratio_bound {n k : ℕ} (hn : 0 < n) (P : Fin n → Pt) (b o : Pt)
    (hcmp : cmp P b k = 0) (t : ℝ) (ht : 0 ≤ t) (hbound : total P 0 ≤ t * total P o) :
    ratio P b o k ≤ t := by
  rw [ratio_total hn.ne', hcmp]
  rcases eq_or_lt_of_le (total_nonneg P o) with hzero | hpos
  · rw [← hzero, div_zero]
    exact ht
  · exact (div_le_iff₀ hpos).mpr hbound

end LearnAugFL.CMP.AxisProof


namespace LearnAugFL.CMP.AxisProof

lemma count_filter {n : ℕ} (P : Fin n → Pt) (p : Pt → Prop) [DecidablePred p] :
    count P p = (Finset.univ.filter (fun i => p (P i))).card := by
  classical
  simp [count, Set.ncard_eq_toFinset_card']

lemma coord_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2) :
    (coordValues P b k j).card = n + k := by simp [coordValues]

lemma coord_positive_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2) :
    ((coordValues P b k j).filter (fun x => 0 < x)).card =
      count P (fun p => 0 < p j) + if 0 < b j then k else 0 := by
  classical
  unfold coordValues
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_map, Multiset.card_map]
  have hm : (Multiset.filter ((fun x : ℝ => 0 < x) ∘ fun i : Fin n => P i j) Finset.univ.val).card =
      count P (fun p => 0 < p j) := by
    rw [count_filter]
    rfl
  rw [hm]
  congr 1
  by_cases hb : 0 < b j
  · rw [if_pos hb, Multiset.filter_eq_self.mpr]
    · simp
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb
  · rw [if_neg hb, Multiset.filter_eq_nil.mpr]
    · rfl
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb

lemma y_median_zero {n k : ℕ} (P : Fin n → Pt) (b : Pt) (h : cmp P b k = 0) :
    lowerMedian (coordValues P b k 1) = 0 := by
  have hh := congrArg (fun v : Pt => v 1) h
  simpa [cmp] using hh

lemma consistency_count_bound {n k : ℕ} (P : Fin n → Pt) (o : Pt) (ho : 0 < o 1)
    (hcmp : cmp P o k = 0)
    (hmedian : ∀ s : Multiset ℝ, lowerMedian s = 0 → 2 * (s.filter (fun x => 0 < x)).card ≤ s.card) :
    2 * count P (fun p => 0 < p 1) + k ≤ n := by
  have hh := hmedian (coordValues P o k 1) (y_median_zero P o hcmp)
  rw [coord_positive_card, if_pos ho, coord_card] at hh
  omega

lemma robustness_count_bound {n k : ℕ} (P : Fin n → Pt) (hcmp : cmp P 0 k = 0)
    (hmedian : ∀ s : Multiset ℝ, lowerMedian s = 0 → 2 * (s.filter (fun x => 0 < x)).card ≤ s.card) :
    2 * count P (fun p => 0 < p 1) ≤ n + k := by
  have hh := hmedian (coordValues P 0 k 1) (y_median_zero P 0 hcmp)
  simpa only [coord_positive_card, PiLp.zero_apply, lt_self_iff_false, if_false, add_zero,
    coord_card] using hh

lemma consistency_bound (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ}
    (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho0 : o 0 = 0) (ho1 : 0 < o 1) (haxes : ∀ i, onX (P i) ∨ onY (P i))
    (hcmp : cmp P o k = 0) (hcount : 2 * count P (fun p => 0 < p 1) + k ≤ n) :
    ucost P (cmp P o k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) * ucost P o := by
  let s := (1 - c) / (1 + c)
  let t := Real.sqrt (2 * c ^ 2 + 2) / (1 + c)
  have hd : 0 < 1 + c := by linarith
  have hs : 0 ≤ s := div_nonneg (by linarith) hd.le
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hst : t ^ 2 = 1 + s ^ 2 := by
    dsimp [t, s]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hm : (2 : ℝ) * count P (fun p => 0 < p 1) ≤ (1 - c) * n := by
    have hh : (2 : ℝ) * count P (fun p => 0 < p 1) + k ≤ n := by exact_mod_cast hcount
    rw [hnk.2] at hh
    nlinarith
  have hc : (1 + s) * count P (fun p => 0 < p 1) ≤ s * n := by
    calc
      _ = (2 * count P (fun p => 0 < p 1)) / (1 + c) := by dsimp [s]; field_simp; ring
      _ ≤ ((1 - c) * n) / (1 + c) := div_le_div_of_nonneg_right hm hd.le
      _ = _ := by dsimp [s]; ring
  have hbound := total_bound P o ho0 ho1 haxes s t hs ht hst hc
  change ucost P (cmp P o k) ≤ t * ucost P o
  rw [hcmp]
  change total P 0 / (n : ℝ) ≤ t * (total P o / n)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)

lemma robustness_bound (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ}
    (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho0 : o 0 = 0) (ho1 : 0 < o 1) (haxes : ∀ i, onX (P i) ∨ onY (P i))
    (hcmp : cmp P 0 k = 0) (hcount : 2 * count P (fun p => 0 < p 1) ≤ n + k) :
    ucost P (cmp P 0 k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) * ucost P o := by
  let s := (1 + c) / (1 - c)
  let t := Real.sqrt (2 * c ^ 2 + 2) / (1 - c)
  have hd : 0 < 1 - c := by linarith
  have hs : 0 ≤ s := div_nonneg (by linarith) hd.le
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hst : t ^ 2 = 1 + s ^ 2 := by
    dsimp [t, s]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hm : (2 : ℝ) * count P (fun p => 0 < p 1) ≤ (1 + c) * n := by
    have hh : (2 : ℝ) * count P (fun p => 0 < p 1) ≤ n + k := by exact_mod_cast hcount
    rw [hnk.2] at hh
    nlinarith
  have hc : (1 + s) * count P (fun p => 0 < p 1) ≤ s * n := by
    calc
      _ = (2 * count P (fun p => 0 < p 1)) / (1 - c) := by dsimp [s]; field_simp; ring
      _ ≤ ((1 + c) * n) / (1 - c) := div_le_div_of_nonneg_right hm hd.le
      _ = _ := by dsimp [s]; ring
  have hbound := total_bound P o ho0 ho1 haxes s t hs ht hst hc
  change ucost P (cmp P 0 k) ≤ t * ucost P o
  rw [hcmp]
  change total P 0 / (n : ℝ) ≤ t * (total P o / n)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)

end LearnAugFL.CMP.AxisProof


namespace LearnAugFL.CMP.ConsistencyProof

noncomputable def total {n : ℕ} (P : Fin n → Pt) (f : Pt) : ℝ := ∑ i, dist f (P i)

lemma total_nonneg {n : ℕ} (P : Fin n → Pt) (f : Pt) : 0 ≤ total P f :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma total_zero {n : ℕ} (P : Fin n → Pt) (o : Pt) (h : total P o = 0) :
    P = fun _ => o := by
  funext i
  have hi : dist o (P i) ≤ total P o := Finset.single_le_sum
    (fun _ _ => dist_nonneg) (Finset.mem_univ i)
  have hdist : dist o (P i) = 0 := le_antisymm (by simpa [h] using hi) dist_nonneg
  exact (dist_eq_zero.mp hdist).symm

lemma ratio_total {n k : ℕ} (hn : n ≠ 0) (P : Fin n → Pt) (b o : Pt) :
    ratio P b o k = total P (cmp P b k) / total P o := by
  unfold ratio ucost total
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

lemma total_update {n : ℕ} (P : Fin n → Pt) (i : Fin n) (p f : Pt) :
    total (Function.update P i p) f = total P f - dist f (P i) + dist f p := by
  classical
  unfold total
  have hfun : (fun j => dist f (Function.update P i p j)) =
      Function.update (fun j => dist f (P j)) i (dist f p) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => dist f (P j)) (Finset.mem_univ i)
  linarith

lemma total_pos {n : ℕ} (P : Fin n → Pt) (i j : Fin n) (hij : P i ≠ P j) (z : Pt) :
    0 < total P z := by
  refine lt_of_le_of_ne (total_nonneg P z) ?_
  intro he
  have hh := total_zero P z he.symm
  exact hij (by simp [hh])

lemma isOpt_iff {n : ℕ} (hn : 0 < n) (P : Fin n → Pt) (o : Pt) :
    IsOpt P o ↔ ∀ z, total P o ≤ total P z := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  simp only [IsOpt, ucost, total, div_le_div_iff_of_pos_right hnR]

lemma continuous_total {n : ℕ} (P : Fin n → Pt) : Continuous (total P) := by
  unfold total
  fun_prop


end LearnAugFL.CMP.ConsistencyProof


namespace LearnAugFL.CMP.ConsistencyProof

lemma median_zero_positive_count (s : Multiset ℝ) (hs : lowerMedian s = 0) :
    2 * (s.filter (fun x => 0 < x)).card ≤ s.card := by
  classical
  by_cases hn : s.card = 0
  · have : s = 0 := Multiset.card_eq_zero.mp hn
    subst s
    simp
  let l := s.sort (· ≤ ·)
  let m := (s.card + 1) / 2 - 1
  have hlen : l.length = s.card := Multiset.length_sort (· ≤ ·)
  have hm : m < l.length := by dsimp [m]; omega
  have hzero : l[m] = 0 := by
    change l.getD m 0 = 0 at hs
    simpa only [List.getD_eq_getElem _ _ hm] using hs
  have hsorted : l.SortedLE := (Multiset.pairwise_sort s (· ≤ ·)).sortedLE
  have htake : (l.take (m+1)).filter (fun x => decide (0 < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi' : i < l.length := by simp only [List.length_take] at hi; omega
    have him : i ≤ m := by simp only [List.length_take] at hi; omega
    have hle : x ≤ 0 := by
      have h := hsorted.getElem_le_getElem_of_le (hi := hi') (hj := hm) him
      simp only [List.getElem_take] at hxi
      simpa only [hxi, hzero] using h
    simpa using not_lt_of_ge hle
  have hcount : (l.filter (fun x => decide (0 < x))).length ≤ l.length - (m+1) := by
    calc
      _ = ((l.drop (m+1)).filter (fun x => decide (0 < x))).length := by
        conv_lhs => rw [← List.take_append_drop (m+1) l, List.filter_append, htake, List.nil_append]
      _ ≤ _ := by
        simpa only [List.length_drop] using List.length_filter_le (fun x : ℝ => decide (0 < x)) (l.drop (m+1))
  have hcard : (l.filter (fun x => decide (0 < x))).length = (s.filter (fun x => 0 < x)).card := by
    have heq := congrArg (fun t : Multiset ℝ => (t.filter (fun x => 0 < x)).card) (Multiset.sort_eq s (· ≤ ·))
    simpa only [Multiset.filter_coe, Multiset.coe_card] using heq
  rw [hcard, hlen] at hcount
  dsimp [m] at hcount
  omega

end LearnAugFL.CMP.ConsistencyProof



namespace LearnAugFL.CMP.ConsistencyProof

lemma count_filter {n : ℕ} (P : Fin n → Pt) (p : Pt → Prop) [DecidablePred p] :
    count P p = (Finset.univ.filter (fun i => p (P i))).card := by
  classical
  simp [count, Set.ncard_eq_toFinset_card']

lemma coord_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2) :
    (coordValues P b k j).card = n + k := by simp [coordValues]

lemma coord_positive_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2) :
    ((coordValues P b k j).filter (fun x => 0 < x)).card =
      count P (fun p => 0 < p j) + if 0 < b j then k else 0 := by
  classical
  unfold coordValues
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_map, Multiset.card_map]
  have hm : (Multiset.filter ((fun x : ℝ => 0 < x) ∘ fun i : Fin n => P i j) Finset.univ.val).card =
      count P (fun p => 0 < p j) := by
    rw [count_filter]
    rfl
  rw [hm]
  congr 1
  by_cases hb : 0 < b j
  · rw [if_pos hb, Multiset.filter_eq_self.mpr]
    · simp
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb
  · rw [if_neg hb, Multiset.filter_eq_nil.mpr]
    · rfl
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb

lemma coordinate_median_zero {n k : ℕ} (P : Fin n → Pt) (b : Pt) (h : cmp P b k = 0)
    (j : Fin 2) : lowerMedian (coordValues P b k j) = 0 := by
  have hh := congrArg (fun v : Pt => v j) h
  fin_cases j <;> simpa [cmp] using hh

lemma coordinate_count {n k : ℕ} (P : Fin n → Pt) (o : Pt) (ho : ∀ j, 0 < o j)
    (hcmp : cmp P o k = 0) (j : Fin 2) :
    2 * count P (fun p => 0 < p j) + k ≤ n := by
  have hh := median_zero_positive_count (coordValues P o k j) (coordinate_median_zero P o hcmp j)
  rw [coord_positive_card, if_pos (ho j), coord_card] at hh
  omega

end LearnAugFL.CMP.ConsistencyProof


namespace LearnAugFL.CMP.ConsistencyProof

lemma norm_sq_coords (p : Pt) (a b : Fin 2) (hab : a ≠ b) :
    ‖p‖ ^ 2 = (p a) ^ 2 + (p b) ^ 2 := by
  fin_cases a <;> fin_cases b <;> simp_all [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, add_comm]

lemma norm_axis (p : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0) : ‖p‖ = |p a| := by
  have hh := norm_sq_coords p a b hab
  simp only [hp, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
  have ha := sq_abs (p a)
  nlinarith [norm_nonneg p, abs_nonneg (p a)]

lemma quadratic_bound (r w z s t d : ℝ) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hst : t ^ 2 = 1 + s ^ 2) (hdd : d ^ 2 = (r - w) ^ 2 + z ^ 2) :
    r ≤ t * d + w - s * z := by
  have he : (t * d) ^ 2 = (r - w + s * z) ^ 2 + (s * (r - w) - z) ^ 2 := by
    rw [mul_pow, hst, hdd]
    ring
  have hnonneg := mul_nonneg ht hd
  have hsq := sq_nonneg (s * (r - w) - z)
  nlinarith

lemma axis_positive_bound (p o : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0)
    (hpa : 0 < p a) (s t : ℝ) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p + o a - s * o b := by
  apply quadratic_bound _ _ _ _ _ _ ht dist_nonneg hst
  rw [dist_eq_norm, norm_sq_coords (o - p) a b hab, norm_axis p a b hab hp, abs_of_pos hpa]
  simp only [PiLp.sub_apply, hp, sub_zero]
  ring

lemma axis_nonpositive_bound (p o : Pt) (a b : Fin 2) (hab : a ≠ b) (hp : p b = 0)
    (hpa : p a ≤ 0) (s t : ℝ) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - o a - s * o b := by
  have h := quadratic_bound ‖p‖ (-o a) (o b) s t (dist o p) ht dist_nonneg hst
  apply h
  rw [dist_eq_norm, norm_sq_coords (o - p) a b hab, norm_axis p a b hab hp, abs_of_nonpos hpa]
  simp only [PiLp.sub_apply, hp, sub_zero]
  ring

lemma pointwise_bound (p o : Pt) (ho : ∀ j, 0 < o j) (ho01 : o 0 ≤ o 1)
    (haxes : onX p ∨ onY p ∨ p = o) (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - (o 0 + s * o 1) +
      (if 0 < p 0 then 2 * o 0 else 0) +
      (if 0 < p 1 then (1 - s) * o 0 + (1 + s) * o 1 else 0) := by
  rcases haxes with hpx | hpy | hpo
  · change p 1 = 0 at hpx
    simp only [hpx, lt_self_iff_false, if_false, add_zero]
    by_cases hx : 0 < p 0
    · rw [if_pos hx]
      have h := axis_positive_bound p o 0 1 (by decide) hpx hx s t ht hst
      nlinarith
    · rw [if_neg hx, add_zero]
      have h := axis_nonpositive_bound p o 0 1 (by decide) hpx (le_of_not_gt hx) s t ht hst
      linarith
  · change p 0 = 0 at hpy
    simp only [hpy, lt_self_iff_false, if_false, add_zero]
    by_cases hy : 0 < p 1
    · rw [if_pos hy]
      have h := axis_positive_bound p o 1 0 (by decide) hpy hy s t ht hst
      nlinarith
    · rw [if_neg hy, add_zero]
      have h := axis_nonpositive_bound p o 1 0 (by decide) hpy (le_of_not_gt hy) s t ht hst
      have hdiff := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ho01)
      nlinarith
  · subst p
    simp only [ho, if_true, dist_self, mul_zero, zero_sub]
    have hn : ‖o‖ ≤ o 0 + o 1 := by
      have h := norm_sq_coords o 0 1 (by decide)
      nlinarith [norm_nonneg o, ho 0, ho 1]
    have hh := mul_nonneg (sub_nonneg.mpr hs1) (ho 0).le
    nlinarith

open Classical in
lemma count_weight_sum {n : ℕ} (P : Fin n → Pt) (f : Pt → Prop) (D : ℝ) :
    (∑ i : Fin n, if f (P i) then D else 0) = (count P f : ℝ) * D := by
  classical
  rw [← Finset.sum_filter]
  simp [count, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

lemma total_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho : ∀ j, 0 < o j) (ho01 : o 0 ≤ o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : ∀ j, (1 + s) * count P (fun p => 0 < p j) ≤ s * n) :
    total P 0 ≤ t * total P o := by
  classical
  let α := 2 * o 0
  let β := (1 - s) * o 0 + (1 + s) * o 1
  have hα : 0 ≤ α := mul_nonneg (by norm_num) (ho 0).le
  have hβ : 0 ≤ β := add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (ho 0).le)
    (mul_nonneg (by linarith) (ho 1).le)
  have hx := mul_le_mul_of_nonneg_right (hcount 0) hα
  have hy := mul_le_mul_of_nonneg_right (hcount 1) hβ
  have hcoef : s * (α + β) ≤ (1 + s) * (o 0 + s * o 1) := by
    have hh := mul_nonneg (sq_nonneg (1 - s)) (ho 0).le
    dsimp [α, β]
    nlinarith
  have hcoefn := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    pointwise_bound (P i) o ho ho01 (haxes i) s t hs0 hs1 ht hst)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 0) (2 * o 0),
    count_weight_sum P (fun p => 0 < p 1) ((1 - s) * o 0 + (1 + s) * o 1)] at hsum
  have hb : count P (fun p => 0 < p 0) * α + count P (fun p => 0 < p 1) * β ≤
      n * (o 0 + s * o 1) := by nlinarith
  dsimp [α, β] at hb
  simp only [total, dist_zero_left]
  linarith

end LearnAugFL.CMP.ConsistencyProof


namespace LearnAugFL.CMP.ConsistencyProof

lemma consistency_bound (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ}
    (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho : ∀ j, 0 < o j) (ho01 : o 0 ≤ o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o) (hcmp : cmp P o k = 0) :
    ucost P (cmp P o k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) * ucost P o := by
  let s := (1 - c) / (1 + c)
  let t := Real.sqrt (2 * c ^ 2 + 2) / (1 + c)
  have hd : 0 < 1 + c := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).mpr (by linarith)
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hst : t ^ 2 = 1 + s ^ 2 := by
    dsimp [t, s]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hcnt (j : Fin 2) : (1 + s) * count P (fun p => 0 < p j) ≤ s * n := by
    have hm : (2 : ℝ) * count P (fun p => 0 < p j) ≤ (1 - c) * n := by
      have hh : (2 : ℝ) * count P (fun p => 0 < p j) + k ≤ n := by
        exact_mod_cast coordinate_count P o ho hcmp j
      rw [hnk.2] at hh
      nlinarith
    calc
      _ = (2 * count P (fun p => 0 < p j)) / (1 + c) := by dsimp [s]; field_simp; ring
      _ ≤ ((1 - c) * n) / (1 + c) := div_le_div_of_nonneg_right hm hd.le
      _ = _ := by dsimp [s]; ring
  have hbound := total_bound P o ho ho01 haxes s t hs0 hs1 ht hst hcnt
  change ucost P (cmp P o k) ≤ t * ucost P o
  rw [hcmp]
  change total P 0 / (n : ℝ) ≤ t * (total P o / n)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)

end LearnAugFL.CMP.ConsistencyProof


namespace LearnAugFL.CMP.RobustnessProof

noncomputable def total {n : ℕ} (P : Fin n → Pt) (f : Pt) : ℝ := ∑ i, dist f (P i)

lemma total_nonneg {n : ℕ} (P : Fin n → Pt) (f : Pt) : 0 ≤ total P f :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma total_zero {n : ℕ} (P : Fin n → Pt) (o : Pt) (h : total P o = 0) :
    P = fun _ => o := by
  funext i
  have hi : dist o (P i) ≤ total P o := Finset.single_le_sum
    (fun _ _ => dist_nonneg) (Finset.mem_univ i)
  have hdist : dist o (P i) = 0 := le_antisymm (by simpa [h] using hi) dist_nonneg
  exact (dist_eq_zero.mp hdist).symm

lemma ratio_total {n k : ℕ} (hn : n ≠ 0) (P : Fin n → Pt) (b o : Pt) :
    ratio P b o k = total P (cmp P b k) / total P o := by
  unfold ratio ucost total
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

end LearnAugFL.CMP.RobustnessProof


namespace LearnAugFL.CMP.RobustnessProof

lemma median_zero_positive_count (s : Multiset ℝ) (hs : lowerMedian s = 0) :
    2 * (s.filter (fun x => 0 < x)).card ≤ s.card := by
  classical
  by_cases hn : s.card = 0
  · have : s = 0 := Multiset.card_eq_zero.mp hn
    subst s
    simp
  let l := s.sort (· ≤ ·)
  let m := (s.card + 1) / 2 - 1
  have hlen : l.length = s.card := Multiset.length_sort (· ≤ ·)
  have hm : m < l.length := by dsimp [m]; omega
  have hzero : l[m] = 0 := by
    change l.getD m 0 = 0 at hs
    simpa only [List.getD_eq_getElem _ _ hm] using hs
  have hsorted : l.SortedLE := (Multiset.pairwise_sort s (· ≤ ·)).sortedLE
  have htake : (l.take (m+1)).filter (fun x => decide (0 < x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi' : i < l.length := by simp only [List.length_take] at hi; omega
    have him : i ≤ m := by simp only [List.length_take] at hi; omega
    have hle : x ≤ 0 := by
      have h := hsorted.getElem_le_getElem_of_le (hi := hi') (hj := hm) him
      simp only [List.getElem_take] at hxi
      simpa only [hxi, hzero] using h
    simpa using not_lt_of_ge hle
  have hcount : (l.filter (fun x => decide (0 < x))).length ≤ l.length - (m+1) := by
    calc
      _ = ((l.drop (m+1)).filter (fun x => decide (0 < x))).length := by
        conv_lhs => rw [← List.take_append_drop (m+1) l, List.filter_append, htake, List.nil_append]
      _ ≤ _ := by
        simpa only [List.length_drop] using List.length_filter_le (fun x : ℝ => decide (0 < x)) (l.drop (m+1))
  have hcard : (l.filter (fun x => decide (0 < x))).length = (s.filter (fun x => 0 < x)).card := by
    have heq := congrArg (fun t : Multiset ℝ => (t.filter (fun x => 0 < x)).card) (Multiset.sort_eq s (· ≤ ·))
    simpa only [Multiset.filter_coe, Multiset.coe_card] using heq
  rw [hcard, hlen] at hcount
  dsimp [m] at hcount
  omega

end LearnAugFL.CMP.RobustnessProof



namespace LearnAugFL.CMP.RobustnessProof

lemma norm_axis_x (p : Pt) (hp : p 1 = 0) : ‖p‖ = |p 0| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma norm_axis_y (p : Pt) (hp : p 0 = 0) : ‖p‖ = |p 1| := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, hp, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

lemma norm_sq_two (p : Pt) : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma dist_sq_two (o p : Pt) : dist o p ^ 2 = (o 0 - p 0) ^ 2 + (o 1 - p 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_two]
  rfl

lemma quadratic_bound (r w z d s t : ℝ) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hds : d ^ 2 = (r - w) ^ 2 + z ^ 2) (hst : t ^ 2 = 1 + s ^ 2) :
    r ≤ t * d + w - s * z := by
  have he : (t*d)^2 = (r-w+s*z)^2 + (s*(r-w)-z)^2 := by
    rw [mul_pow, hds, hst]
    ring
  have htd := mul_nonneg ht hd
  have hsq := sq_nonneg (s*(r-w)-z)
  nlinarith

lemma norm_upper (o : Pt) (ho0 : 0 ≤ o 0) (ho1 : 0 ≤ o 1) :
    ‖o‖ ≤ o 0 + o 1 := by
  have hh := norm_sq_two o
  nlinarith [norm_nonneg o, mul_nonneg ho0 ho1]

lemma negative_bound (p o : Pt) (hp0 : p 0 ≤ 0) (hp1 : p 1 ≤ 0)
    (ho0 : 0 ≤ o 0) (ho1 : 0 ≤ o 1) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * ‖o‖ := by
  have hd : ‖p‖ ^ 2 + ‖o‖ ^ 2 ≤ dist o p ^ 2 := by
    rw [norm_sq_two p, norm_sq_two o, dist_sq_two]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ho0 hp0,
      mul_nonpos_of_nonneg_of_nonpos ho1 hp1]
  have he : (‖p‖ + s*‖o‖)^2 ≤ (t*dist o p)^2 := by
    calc
      _ ≤ (1+s^2)*(‖p‖^2+‖o‖^2) := by nlinarith [sq_nonneg (s*‖p‖-‖o‖)]
      _ ≤ (1+s^2)*dist o p^2 := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by rw [mul_pow, hst]
  have ha : 0 ≤ ‖p‖ + s*‖o‖ := by positivity
  have hb : 0 ≤ t*dist o p := mul_nonneg ht dist_nonneg
  nlinarith

open Classical in
lemma point_bound (p o : Pt) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (hp : onX p ∨ onY p ∨ p = o) (s t : ℝ)
    (hs : 1 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2) :
    ‖p‖ ≤ t * dist o p - s * ‖o‖ +
      (if 0 < p 0 then (1+s)/2*(‖o‖+o 0-o 1) else 0) +
      (if 0 < p 1 then (1+s)/2*(‖o‖-o 0+o 1) else 0) := by
  have hnorm := norm_upper o ho0.le ho1.le
  have hgap := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hnorm)
  rcases hp with hp | hp | rfl
  · change p 1 = 0 at hp
    by_cases hx : 0 < p 0
    · simp only [hx, hp, lt_self_iff_false, if_false, if_true, add_zero]
      rw [norm_axis_x p hp, abs_of_pos hx]
      have hd : dist o p ^ 2 = (p 0 - o 0)^2+(o 1)^2 := by
        rw [dist_sq_two, hp]
        ring
      have h := quadratic_bound (p 0) (o 0) (o 1) (dist o p) s t dist_nonneg ht hd hst
      nlinarith
    · simp only [hx, hp, lt_self_iff_false, if_false, add_zero]
      exact negative_bound p o (le_of_not_gt hx) (by rw [hp]) ho0.le ho1.le s t (by linarith) ht hst
  · change p 0 = 0 at hp
    by_cases hy : 0 < p 1
    · simp only [hy, hp, lt_self_iff_false, if_false, if_true, add_zero]
      rw [norm_axis_y p hp, abs_of_pos hy]
      have hd : dist o p ^ 2 = (p 1 - o 1)^2+(o 0)^2 := by
        rw [dist_sq_two, hp]
        ring
      have h := quadratic_bound (p 1) (o 1) (o 0) (dist o p) s t dist_nonneg ht hd hst
      nlinarith
    · simp only [hy, hp, lt_self_iff_false, if_false, add_zero]
      exact negative_bound p o (by rw [hp]) (le_of_not_gt hy) ho0.le ho1.le s t (by linarith) ht hst
  · simp only [ho0, ho1, if_true, dist_self, mul_zero]
    ring_nf
    exact le_refl _

open Classical in
lemma count_weight_sum {n : ℕ} (P : Fin n → Pt) (f : Pt → Prop) (D : ℝ) :
    (∑ i : Fin n, if f (P i) then D else 0) = (count P f : ℝ) * D := by
  classical
  rw [← Finset.sum_filter]
  simp [count, Set.ncard_eq_toFinset_card', nsmul_eq_mul]

lemma total_bound {n : ℕ} (P : Fin n → Pt) (o : Pt) (ho0 : 0 < o 0) (ho1 : 0 < o 1)
    (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o) (s t : ℝ)
    (hs : 1 ≤ s) (ht : 0 ≤ t) (hst : t ^ 2 = 1 + s ^ 2)
    (hcount : ∀ j : Fin 2, (1+s)*(count P (fun p => 0 < p j) : ℝ) ≤ s*n) :
    total P 0 ≤ t * total P o := by
  classical
  let a := (1+s)/2*(‖o‖+o 0-o 1)
  let b := (1+s)/2*(‖o‖-o 0+o 1)
  have ho0n : o 0 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 1), norm_nonneg o]
  have ho1n : o 1 ≤ ‖o‖ := by
    have hh := norm_sq_two o
    nlinarith [sq_nonneg (o 0), norm_nonneg o]
  have ha : 0 ≤ a := mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ b := mul_nonneg (by linarith) (by linarith)
  have hab : a+b=(1+s)*‖o‖ := by dsimp [a,b]; ring
  have hc0 := mul_le_mul_of_nonneg_left (hcount 0) ha
  have hc1 := mul_le_mul_of_nonneg_left (hcount 1) hb
  have hc : (count P (fun p => 0 < p 0) : ℝ)*a +
      (count P (fun p => 0 < p 1) : ℝ)*b ≤ (n:ℝ)*s*‖o‖ := by
    apply (mul_le_mul_iff_right₀ (show 0 < 1+s by linarith)).mp
    nlinarith [congrArg (fun x : ℝ => x*s*n) hab]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    point_bound (P i) o ho0 ho1 (haxes i) s t hs ht hst)
  change (∑ i, ‖P i‖) ≤ ∑ i, (t*dist o (P i)-s*‖o‖+
    (if 0 < P i 0 then a else 0)+(if 0 < P i 1 then b else 0)) at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [count_weight_sum P (fun p => 0 < p 0) a,
    count_weight_sum P (fun p => 0 < p 1) b] at hsum
  simp only [total, dist_zero_left]
  nlinarith

lemma ratio_bound {n k : ℕ} (hn : 0 < n) (P : Fin n → Pt) (b o : Pt)
    (hcmp : cmp P b k = 0) (t : ℝ) (ht : 0 ≤ t) (hbound : total P 0 ≤ t * total P o) :
    ratio P b o k ≤ t := by
  rw [ratio_total hn.ne', hcmp]
  rcases eq_or_lt_of_le (total_nonneg P o) with hzero | hpos
  · rw [← hzero, div_zero]
    exact ht
  · exact (div_le_iff₀ hpos).mpr hbound

end LearnAugFL.CMP.RobustnessProof


namespace LearnAugFL.CMP.RobustnessProof

lemma count_filter {n : ℕ} (P : Fin n → Pt) (p : Pt → Prop) [DecidablePred p] :
    count P p = (Finset.univ.filter (fun i => p (P i))).card := by
  classical
  simp [count, Set.ncard_eq_toFinset_card']

lemma coord_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2) :
    (coordValues P b k j).card = n + k := by simp [coordValues]

lemma coord_positive_card {n : ℕ} (P : Fin n → Pt) (b : Pt) (k : ℕ) (j : Fin 2) :
    ((coordValues P b k j).filter (fun x => 0 < x)).card =
      count P (fun p => 0 < p j) + if 0 < b j then k else 0 := by
  classical
  unfold coordValues
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_map, Multiset.card_map]
  have hm : (Multiset.filter ((fun x : ℝ => 0 < x) ∘ fun i : Fin n => P i j) Finset.univ.val).card =
      count P (fun p => 0 < p j) := by
    rw [count_filter]
    rfl
  rw [hm]
  congr 1
  by_cases hb : 0 < b j
  · rw [if_pos hb, Multiset.filter_eq_self.mpr]
    · simp
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb
  · rw [if_neg hb, Multiset.filter_eq_nil.mpr]
    · rfl
    · intro x hx
      have he := Multiset.mem_replicate.mp hx
      simpa [he.2] using hb

lemma coordinate_median_zero {n k : ℕ} (P : Fin n → Pt) (h : cmp P 0 k = 0)
    (j : Fin 2) : lowerMedian (coordValues P 0 k j) = 0 := by
  have hh := congrArg (fun v : Pt => v j) h
  fin_cases j <;> simpa [cmp] using hh

lemma robustness_count_bound {n k : ℕ} (P : Fin n → Pt) (hcmp : cmp P 0 k = 0)
    (j : Fin 2) : 2 * count P (fun p => 0 < p j) ≤ n + k := by
  have hh := median_zero_positive_count (coordValues P 0 k j) (coordinate_median_zero P hcmp j)
  simpa only [coord_positive_card, PiLp.zero_apply, lt_self_iff_false, if_false, add_zero,
    coord_card] using hh

lemma robustness_bound (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ}
    (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho0 : 0 < o 0) (ho1 : 0 < o 1) (haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o)
    (hcmp : cmp P 0 k = 0) :
    ucost P (cmp P 0 k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) * ucost P o := by
  let s := (1+c)/(1-c)
  let t := Real.sqrt (2*c^2+2)/(1-c)
  have hd : 0 < 1-c := by linarith
  have hs : 1 ≤ s := (le_div_iff₀ hd).mpr (by nlinarith)
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hd.le
  have hst : t^2 = 1+s^2 := by
    dsimp [t,s]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hcount (j : Fin 2) : (1+s)*(count P (fun p => 0 < p j) : ℝ) ≤ s*n := by
    have hm : (2 : ℝ)*count P (fun p => 0 < p j) ≤ (1+c)*n := by
      have hh : (2 : ℝ)*count P (fun p => 0 < p j) ≤ n+k := by
        exact_mod_cast robustness_count_bound P hcmp j
      rw [hnk.2] at hh
      nlinarith
    calc
      _ = (2*count P (fun p => 0 < p j))/(1-c) := by dsimp [s]; field_simp; ring
      _ ≤ ((1+c)*n)/(1-c) := div_le_div_of_nonneg_right hm hd.le
      _ = _ := by dsimp [s]; ring
  have hbound := total_bound P o ho0 ho1 haxes s t hs ht hst hcount
  change ucost P (cmp P 0 k) ≤ t * ucost P o
  rw [hcmp]
  change total P 0 / (n : ℝ) ≤ t * (total P o / n)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)

end LearnAugFL.CMP.RobustnessProof

-- Complete inline local file ReductionTarget.lean

open LearnAugFL.CMP

def ReductionStatement : Prop :=
  ∀ (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1),
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_C c m k' Q oQ ∨ CA_C c m k' Q oQ) →
        ucost Q (cmp Q oQ k') ≤ α * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), (OA_R c m k' Q oQ ∨ CA_R c m k' Q oQ) →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q oQ) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o)

-- Complete inline local file Conditional.lean

namespace LearnAugFL.CMP.HeadlineProof

lemma ca_axes {c : ℝ} {n k : ℕ} {P : Fin n → Pt} {b o : Pt}
    (hP : CA c n k P b o) : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o := by
  obtain ⟨x₁, x₂, y₁, y₂, _, _, _, _, hmem, _⟩ := hP.2.2.2.2.2
  intro i
  rcases hmem i with hi | hi | hi | hi | hi <;> simp [hi, onX, onY]

lemma consistency_families (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (m k : ℕ) (P : Fin m → Pt) (o : Pt) (h : OA_C c m k P o ∨ CA_C c m k P o) :
    ucost P (cmp P o k) ≤ Real.sqrt (2*c^2+2)/(1+c)*ucost P o := by
  rcases h with h | h
  · obtain ⟨hnk, _, hcmp, ho0, ho1, haxes⟩ := h
    exact AxisProof.consistency_bound c hc0 hc1 hnk P o ho0 ho1 haxes hcmp
      (AxisProof.consistency_count_bound P o ho1 hcmp AxisProof.median_zero_positive_count)
  · have ho : ∀ j, 0 < o j := by
      intro j
      fin_cases j
      · exact h.2.2.2.1.1
      · exact h.2.2.2.1.1.trans_le h.2.2.2.1.2
    exact ConsistencyProof.consistency_bound c hc0 hc1 h.1 P o ho h.2.2.2.1.2
      (ca_axes h) h.2.2.1

lemma robustness_families (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (m k : ℕ) (P : Fin m → Pt) (o : Pt) (h : OA_R c m k P o ∨ CA_R c m k P o) :
    ucost P (cmp P 0 k) ≤ Real.sqrt (2*c^2+2)/(1-c)*ucost P o := by
  rcases h with h | h
  · obtain ⟨hnk, _, hcmp, ho0, ho1, haxes⟩ := h
    exact AxisProof.robustness_bound c hc0 hc1 hnk P o ho0 ho1 haxes hcmp
      (AxisProof.robustness_count_bound P hcmp AxisProof.median_zero_positive_count)
  · exact RobustnessProof.robustness_bound c hc0 hc1 h.1 P o h.2.2.2.1.1
      (h.2.2.2.1.1.trans_le h.2.2.2.1.2) (ca_axes h) h.2.2.1

theorem from_reduction (h17 : ReductionStatement)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n k : ℕ) (hnk : Admissible c n k)
    (P : Fin n → Pt) :
    (∀ o : Pt, IsOpt P o →
        ucost P (cmp P o k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) * ucost P o) ∧
    (∀ ô o : Pt, IsOpt P o →
        ucost P (cmp P ô k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) * ucost P o) := by
  obtain ⟨hC,hR⟩ := h17 c hc0 hc1
  exact ⟨hC _ (consistency_families c hc0 hc1) n k hnk P,
    hR _ (robustness_families c hc0 hc1) n k hnk P⟩

end LearnAugFL.CMP.HeadlineProof


open LearnAugFL.CMP

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n k : ℕ) (hnk : Admissible c n k)
    (P : Fin n → Pt) :
    (∀ o : Pt, IsOpt P o →
        ucost P (cmp P o k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) * ucost P o) ∧
    (∀ ô o : Pt, IsOpt P o →
        ucost P (cmp P ô k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) * ucost P o) := by
  exact HeadlineProof.from_reduction (@LearnAugFL.CMP.lemma_17) c hc0 hc1 n k hnk P
