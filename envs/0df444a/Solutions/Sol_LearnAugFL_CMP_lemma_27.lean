-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_27
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:53:36.128089+00:00
-- url     : https://prove2.me/submissions/67d52166-eae7-46d2-82c0-7d930962250b

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting

open LearnAugFL.CMP

namespace LearnAugFL.CMP.RatioProof

lemma sort_replicate_add (a b : ℝ) (n k : ℕ) (hab : a ≤ b) :
    (Multiset.replicate n a + Multiset.replicate k b).sort (· ≤ ·) =
      List.replicate n a ++ List.replicate k b := by
  have hsort : (List.replicate n a ++ List.replicate k b).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨List.pairwise_replicate_of_refl, List.pairwise_replicate_of_refl, ?_⟩
    intro x hx y hy
    have hx' : x = a := (List.mem_replicate.mp hx).2
    have hy' : y = b := (List.mem_replicate.mp hy).2
    simpa only [hx', hy'] using hab
  rw [← Multiset.coe_replicate, ← Multiset.coe_replicate, Multiset.coe_add,
    Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hsort

lemma median_majority (a b : ℝ) {n k : ℕ} (hkn : k < n) :
    lowerMedian (Multiset.replicate n a + Multiset.replicate k b) = a := by
  have hlow : k ≤ (n + k + 1) / 2 - 1 := by omega
  have hhigh : (n + k + 1) / 2 - 1 < n := by omega
  unfold lowerMedian
  simp only [Multiset.card_add, Multiset.card_replicate]
  rcases le_total a b with hab | hba
  · rw [sort_replicate_add a b n k hab, List.getD_append]
    · exact List.getD_replicate a hhigh
    · simpa only [List.length_replicate] using hhigh
  · rw [add_comm (Multiset.replicate n a), sort_replicate_add b a k n hba,
      List.getD_append_right]
    · apply List.getD_replicate a
      simp only [List.length_replicate]
      omega
    · simpa only [List.length_replicate] using hlow

lemma cmp_constant {n k : ℕ} (hkn : k < n) (a b : Pt) :
    cmp (fun _ : Fin n => a) b k = a := by
  have hc (j : Fin 2) : coordValues (fun _ : Fin n => a) b k j =
      Multiset.replicate n (a j) + Multiset.replicate k (b j) := by
    simp [coordValues]
  ext j
  fin_cases j <;> simp [cmp, hc, median_majority _ _ hkn]

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

lemma fraction_improves {A B A' B' : ℝ} (hB' : 0 < B') (hdrop : B' < B)
    (hr : B < A) (hgap : A - B ≤ A' - B') : A / B < A' / B' := by
  have hB : 0 < B := lt_trans hB' hdrop
  apply (div_lt_div_iff₀ hB hB').mpr
  have hstrict := mul_pos (sub_pos.mpr hdrop) (sub_pos.mpr hr)
  have hweak := mul_nonneg (le_of_lt hB) (sub_nonneg.mpr hgap)
  nlinarith

end LearnAugFL.CMP.RatioProof

theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) {n k : ℕ} (hnk : Admissible c n k)
    (P : Fin n → Pt) (ô o : Pt) (hP : IsOpt P o) (i : Fin n) (hi : P i ≠ o)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hf : cmp P ô k = cmp (Function.update P i (P i + s • (o - P i))) ô k)
    (hr : 1 < ratio P ô o k) :
    ratio P ô o k < ratio (Function.update P i (P i + s • (o - P i))) ô o k := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnk.1
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hkn : k < n := by
    have hkR : (k : ℝ) < n := by rw [hnk.2]; nlinarith
    exact_mod_cast hkR
  let p := P i + s • (o - P i)
  let Q := Function.update P i p
  let F := cmp P ô k
  have hf' : F = cmp Q ô k := hf
  have hmove : dist (P i) p = s * dist (P i) o := by
    calc
      dist (P i) p = ‖s • (o - P i)‖ := by
        rw [dist_comm, dist_eq_norm]
        congr 1
        dsimp [p]
        module
      _ = s * dist (P i) o := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, ← dist_eq_norm, dist_comm o (P i)]
  have hoptmove : dist o p = (1 - s) * dist o (P i) := by
    have heq : o - p = (1 - s) • (o - P i) := by dsimp [p]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hs1), ← dist_eq_norm]
  have hdelta : 0 < dist (P i) p := by
    rw [hmove]
    exact mul_pos hs0 (dist_pos.mpr hi)
  have hdrop : RatioProof.total Q o = RatioProof.total P o - dist (P i) p := by
    dsimp [Q]
    rw [RatioProof.total_update, hoptmove, hmove, dist_comm (P i) o]
    ring
  have hQpos : 0 < RatioProof.total Q o := by
    by_contra h
    have hz : RatioProof.total Q o = 0 :=
      le_antisymm (le_of_not_gt h) (RatioProof.total_nonneg Q o)
    have hQ := RatioProof.total_zero Q o hz
    have hF : F = o := by
      rw [hf', hQ]
      exact RatioProof.cmp_constant hkn o ô
    have hr' : 1 < RatioProof.total P o / RatioProof.total P o := by
      have h := hr
      rw [RatioProof.ratio_total (Nat.ne_of_gt hn)] at h
      change 1 < RatioProof.total P F / RatioProof.total P o at h
      rwa [hF] at h
    exact (not_lt_of_ge (div_self_le_one (RatioProof.total P o))) hr'
  have hPpos : 0 < RatioProof.total P o := by linarith
  have hratio : RatioProof.total P o < RatioProof.total P F := by
    have hr' : 1 < RatioProof.total P F / RatioProof.total P o := by
      simpa only [RatioProof.ratio_total (Nat.ne_of_gt hn)] using hr
    simpa only [one_mul] using (lt_div_iff₀ hPpos).mp hr'
  have hgap : RatioProof.total P F - RatioProof.total P o ≤
      RatioProof.total Q F - RatioProof.total Q o := by
    have htri := dist_triangle F p (P i)
    have hupdate := RatioProof.total_update P i p F
    change RatioProof.total Q F = _ at hupdate
    rw [dist_comm p (P i)] at htri
    linarith
  rw [RatioProof.ratio_total (Nat.ne_of_gt hn), RatioProof.ratio_total (Nat.ne_of_gt hn)]
  change RatioProof.total P F / RatioProof.total P o <
    RatioProof.total Q (cmp Q ô k) / RatioProof.total Q o
  rw [← hf']
  exact RatioProof.fraction_improves hQpos (by linarith) hratio hgap
