-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:38:42.988849+00:00
-- url     : https://prove2.me/submissions/d51c7017-73f0-4731-baf0-3bc4f61f69aa

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting
import Theorems.Thm_LearnAugFL_CMP_lemma_8

-- Complete inline local helper: Basic.lean

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

-- Complete inline local helper: Geometry.lean

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

-- Complete inline local helper: Counts.lean

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
    ratio P o o k ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) := by
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
  exact ratio_bound (lt_of_lt_of_le Nat.zero_lt_one hnk.1) P o o hcmp t ht
    (total_bound P o ho0 ho1 haxes s t hs ht hst hc)

lemma robustness_bound (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ}
    (hnk : Admissible c n k) (P : Fin n → Pt) (o : Pt)
    (ho0 : o 0 = 0) (ho1 : 0 < o 1) (haxes : ∀ i, onX (P i) ∨ onY (P i))
    (hcmp : cmp P 0 k = 0) (hcount : 2 * count P (fun p => 0 < p 1) ≤ n + k) :
    ratio P 0 o k ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) := by
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
  exact ratio_bound (lt_of_lt_of_le Nat.zero_lt_one hnk.1) P 0 o hcmp t ht
    (total_bound P o ho0 ho1 haxes s t hs ht hst hc)

end LearnAugFL.CMP.AxisProof

-- Complete inline local helper: MedianRank.lean

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


-- Complete inline local helper: Generic.lean

namespace LearnAugFL.CMP.AxisProof

theorem main_of_median (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hmedian : ∀ s : Multiset ℝ, lowerMedian s = 0 → 2 * (s.filter (fun x => 0 < x)).card ≤ s.card) :
    (∀ (n k : ℕ) (P : Fin n → Pt) (o : Pt), OA_C c n k P o →
      ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
        (ratio P o o k < ratio Q oQ oQ k' ∨
          (COA_C c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P o o k ≤ ratio Q oQ oQ k'))) ∧
    (∀ (n k : ℕ) (P : Fin n → Pt) (o : Pt), OA_R c n k P o →
      ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
        (ratio P 0 o k < ratio Q 0 oQ k' ∨
          (COA_R c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P 0 o k ≤ ratio Q 0 oQ k'))) := by
  constructor
  · intro n k P o hOA
    obtain ⟨hnk, hP, hcmp, ho0, ho1, haxes⟩ := hOA
    obtain ⟨m, k', Q, hQ, hratio⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 ⟨n, k, hnk⟩).1
    refine ⟨m, k', Q, !₂[0, 1], hQ.1, hQ.2.1, Or.inr ⟨hQ, rfl, ?_⟩⟩
    rw [hratio]
    exact consistency_bound c hc0 hc1 hnk P o ho0 ho1 haxes hcmp
      (consistency_count_bound P o ho1 hcmp hmedian)
  · intro n k P o hOA
    obtain ⟨hnk, hP, hcmp, ho0, ho1, haxes⟩ := hOA
    obtain ⟨m, k', Q, hQ, hratio⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 ⟨n, k, hnk⟩).2
    refine ⟨m, k', Q, !₂[0, 1], hQ.1, hQ.2.1, Or.inr ⟨hQ, rfl, ?_⟩⟩
    rw [hratio]
    exact robustness_bound c hc0 hc1 hnk P o ho0 ho1 haxes hcmp
      (robustness_count_bound P hcmp hmedian)

end LearnAugFL.CMP.AxisProof

open LearnAugFL.CMP LearnAugFL.CMP.AxisProof

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ (n k : ℕ) (P : Fin n → Pt) (o : Pt), OA_C c n k P o →
      ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
        (ratio P o o k < ratio Q oQ oQ k' ∨
          (COA_C c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P o o k ≤ ratio Q oQ oQ k'))) ∧
    (∀ (n k : ℕ) (P : Fin n → Pt) (o : Pt), OA_R c n k P o →
      ∃ (m k' : ℕ) (Q : Fin m → Pt) (oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
        (ratio P 0 o k < ratio Q 0 oQ k' ∨
          (COA_R c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P 0 o k ≤ ratio Q 0 oQ k'))) := by
  exact main_of_median c hc0 hc1 median_zero_positive_count
