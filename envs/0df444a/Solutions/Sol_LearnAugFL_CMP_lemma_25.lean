-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_25
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:53:56.696059+00:00
-- url     : https://prove2.me/submissions/0f9706b8-ee00-4c21-ab8a-f171c80f8068

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting
import Theorems.Thm_LearnAugFL_CMP_lemma_8

-- Complete inline local helper: Basic.lean

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

-- Complete inline local helper: MedianRank.lean

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


-- Complete inline local helper: Geometry.lean

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

-- Complete inline local helper: Counts.lean

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
    ratio P 0 o k ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) := by
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
  exact ratio_bound (lt_of_lt_of_le Nat.zero_lt_one hnk.1) P 0 o hcmp t ht
    (total_bound P o ho0 ho1 haxes s t hs ht hst hcount)

end LearnAugFL.CMP.RobustnessProof

open LearnAugFL.CMP

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (P : Fin n → Pt) (o : Pt)
    (hP : CA_R c n k P o) :
    ∃ (m k' : ℕ) (Q : Fin m → Pt) (ô oQ : Pt), Admissible c m k' ∧ IsOpt Q oQ ∧
      (ratio P 0 o k < ratio Q ô oQ k' ∨
        (COA_R c m k' Q ∧ oQ = !₂[0, 1] ∧ ratio P 0 o k ≤ ratio Q 0 oQ k')) := by
  have haxes : ∀ i, onX (P i) ∨ onY (P i) ∨ P i = o := by
    obtain ⟨x₁, x₂, y₁, y₂, _, _, _, _, hloc, _⟩ := hP.2.2.2.2.2
    intro i
    rcases hloc i with hi | hi | hi | hi | hi
    · exact Or.inl (by simp [onX, hi])
    · exact Or.inl (by simp [onX, hi])
    · exact Or.inr (Or.inl (by simp [onY, hi]))
    · exact Or.inr (Or.inl (by simp [onY, hi]))
    · exact Or.inr (Or.inr hi)
  have hbound := RobustnessProof.robustness_bound c hc0 hc1 hP.1 P o hP.2.2.2.1.1
    (lt_of_lt_of_le hP.2.2.2.1.1 hP.2.2.2.1.2) haxes hP.2.2.1
  obtain ⟨m,k',Q,hQ,hratio⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 ⟨n,k,hP.1⟩).2
  exact ⟨m,k',Q,0,!₂[0,1],hQ.1,hQ.2.1,Or.inr ⟨hQ,rfl,hratio ▸ hbound⟩⟩
