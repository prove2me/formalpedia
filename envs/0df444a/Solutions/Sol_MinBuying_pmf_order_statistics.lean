-- Prove2me | solution 1 for MinBuying.pmf_order_statistics
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:41.743364+00:00
-- url     : https://prove2.me/submissions/c194a9cb-9f01-411d-9849-a57af2ba77df

import Theorems.Thm_MinBuying_sorted_pmf_mass

open scoped BigOperators
noncomputable section

namespace MinBuyingFactorialBalance

lemma factorial_transfer (a d k : ℕ) (had : a ≤ d) :
    (a+k).factorial * d.factorial ≤ a.factorial * (d+k).factorial := by
  rw [← Nat.factorial_mul_ascFactorial a k, ← Nat.factorial_mul_ascFactorial d k]
  have hh := Nat.ascFactorial_le k (Nat.add_le_add_right had 1)
  calc
    a.factorial * (a+1).ascFactorial k * d.factorial =
        (a.factorial*d.factorial) * (a+1).ascFactorial k := by ring
    _ ≤ (a.factorial*d.factorial) * (d+1).ascFactorial k := Nat.mul_le_mul_left _ hh
    _ = _ := by ring

lemma factorial_balancing (a b c d : ℕ) (hmin : min a b ≤ min c d)
    (hsum : a+b=c+d) : c.factorial*d.factorial ≤ a.factorial*b.factorial := by
  rcases le_total a b with hab | hba
  · have hac : a ≤ c := (by simpa [min_eq_left hab] using hmin : a ≤ min c d).trans (min_le_left _ _)
    have had : a ≤ d := (by simpa [min_eq_left hab] using hmin : a ≤ min c d).trans (min_le_right _ _)
    have hc : c = a+(c-a) := by omega
    have hb : b = d+(c-a) := by omega
    rw [hc,hb]
    exact factorial_transfer a d (c-a) had
  · have hbc : b ≤ c := (by simpa [min_eq_right hba] using hmin : b ≤ min c d).trans (min_le_left _ _)
    have hbd : b ≤ d := (by simpa [min_eq_right hba] using hmin : b ≤ min c d).trans (min_le_right _ _)
    have hc : c = b+(c-b) := by omega
    have ha : a = d+(c-b) := by omega
    rw [hc,ha,mul_comm ((d+(c-b)).factorial) b.factorial]
    exact factorial_transfer b d (c-b) hbd

private lemma prefix_or_card {n : ℕ} (P Q : Fin n → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hP : ∀ i j, j ≤ i → P i → P j) (hQ : ∀ i j, j ≤ i → Q i → Q j) :
    (Finset.univ.filter (fun i => P i ∨ Q i)).card =
      max (Finset.univ.filter P).card (Finset.univ.filter Q).card := by
  classical
  have he : Finset.univ.filter (fun i => P i ∨ Q i) =
      Finset.univ.filter (fun i : Fin n => i.val < max (Finset.univ.filter P).card (Finset.univ.filter Q).card) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,lt_max_iff]
    rw [Fin.lt_card_filter_univ_iff_apply_of_imp P hP,
      Fin.lt_card_filter_univ_iff_apply_of_imp Q hQ]
  have hPc : (Finset.univ.filter P).card ≤ n := by simpa using Finset.card_filter_le Finset.univ P
  have hQc : (Finset.univ.filter Q).card ≤ n := by simpa using Finset.card_filter_le Finset.univ Q
  rw [he,Fin.card_filter_val_lt,min_eq_right (max_le hPc hQc)]

private lemma prefix_and_card {n : ℕ} (P Q : Fin n → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hP : ∀ i j, j ≤ i → P i → P j) (hQ : ∀ i j, j ≤ i → Q i → Q j) :
    (Finset.univ.filter (fun i => P i ∧ Q i)).card =
      min (Finset.univ.filter P).card (Finset.univ.filter Q).card := by
  classical
  have he : Finset.univ.filter (fun i => P i ∧ Q i) =
      Finset.univ.filter (fun i : Fin n => i.val < min (Finset.univ.filter P).card (Finset.univ.filter Q).card) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,lt_min_iff]
    rw [Fin.lt_card_filter_univ_iff_apply_of_imp P hP,
      Fin.lt_card_filter_univ_iff_apply_of_imp Q hQ]
  have hPc : (Finset.univ.filter P).card ≤ n := by simpa using Finset.card_filter_le Finset.univ P
  rw [he,Fin.card_filter_val_lt,min_eq_right ((min_le_left _ _).trans hPc)]

def multiplicity {α : Type*} [DecidableEq α] {n : ℕ} (v : Fin n → α) (x : α) : ℕ :=
  (Finset.univ.filter (fun i => v i = x)).card

private lemma multiplicity_difference {α : Type*} [LinearOrder α] {n : ℕ}
    (v : Fin n → α) (x : α) :
    multiplicity v x = (Finset.univ.filter (fun i => v i ≤ x)).card -
      (Finset.univ.filter (fun i => v i < x)).card := by
  classical
  have he : Finset.univ.filter (fun i => v i ≤ x) =
      (Finset.univ.filter (fun i => v i < x)) ∪ (Finset.univ.filter (fun i => v i = x)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    exact le_iff_lt_or_eq
  have hd : Disjoint (Finset.univ.filter (fun i => v i < x)) (Finset.univ.filter (fun i => v i = x)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (ne_of_lt (Finset.mem_filter.mp hi).2) (Finset.mem_filter.mp hj).2
  rw [he,Finset.card_union_of_disjoint hd]
  simp [multiplicity]

lemma multiplicity_min_max_factorial {α : Type*} [LinearOrder α] {n : ℕ}
    (v w : Fin n → α) (hv : Monotone v) (hw : Monotone w) (x : α) :
    (multiplicity (fun i => min (v i) (w i)) x).factorial *
      (multiplicity (fun i => max (v i) (w i)) x).factorial ≤
      (multiplicity v x).factorial * (multiplicity w x).factorial := by
  classical
  let lv := (Finset.univ.filter (fun i => v i < x)).card
  let uv := (Finset.univ.filter (fun i => v i ≤ x)).card
  let lw := (Finset.univ.filter (fun i => w i < x)).card
  let uw := (Finset.univ.filter (fun i => w i ≤ x)).card
  have hvlu : lv ≤ uv := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.le⟩
  have hwlu : lw ≤ uw := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.le⟩
  have hminlt : (Finset.univ.filter (fun i => min (v i) (w i) < x)).card = max lv lw := by
    simp only [min_lt_iff]
    exact prefix_or_card _ _ (fun i j hji hi => (hv hji).trans_lt hi)
      (fun i j hji hi => (hw hji).trans_lt hi)
  have hminle : (Finset.univ.filter (fun i => min (v i) (w i) ≤ x)).card = max uv uw := by
    simp only [min_le_iff]
    exact prefix_or_card _ _ (fun i j hji hi => (hv hji).trans hi)
      (fun i j hji hi => (hw hji).trans hi)
  have hmaxlt : (Finset.univ.filter (fun i => max (v i) (w i) < x)).card = min lv lw := by
    simp only [max_lt_iff]
    exact prefix_and_card _ _ (fun i j hji hi => (hv hji).trans_lt hi)
      (fun i j hji hi => (hw hji).trans_lt hi)
  have hmaxle : (Finset.univ.filter (fun i => max (v i) (w i) ≤ x)).card = min uv uw := by
    simp only [max_le_iff]
    exact prefix_and_card _ _ (fun i j hji hi => (hv hji).trans hi)
      (fun i j hji hi => (hw hji).trans hi)
  rw [multiplicity_difference,multiplicity_difference,multiplicity_difference v x,multiplicity_difference w x,
    hminle,hminlt,hmaxle,hmaxlt]
  change (max uv uw-max lv lw).factorial * (min uv uw-min lv lw).factorial ≤
    (uv-lv).factorial * (uw-lw).factorial
  apply factorial_balancing
  · omega
  · omega

lemma multiplicity_factorial_product {α : Type*} [LinearOrder α] {n : ℕ}
    (v w : Fin n → α) (hv : Monotone v) (hw : Monotone w) (S : Finset α) :
    (∏ x ∈ S, (multiplicity (fun i => min (v i) (w i)) x).factorial) *
      (∏ x ∈ S, (multiplicity (fun i => max (v i) (w i)) x).factorial) ≤
      (∏ x ∈ S, (multiplicity v x).factorial) *
        (∏ x ∈ S, (multiplicity w x).factorial) := by
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun x _ => multiplicity_min_max_factorial v w hv hw x)

end MinBuyingFactorialBalance

open MinBuying MinBuyingFactorialBalance

private def stabilizerFactor {n : ℕ} (v : Valuations n) : ℕ :=
  ∏ x ∈ Finset.univ.image v, (MinBuyingFactorialBalance.multiplicity v x).factorial

private lemma stabilizer_pos {n : ℕ} (v : Valuations n) : 0 < stabilizerFactor v := by
  unfold stabilizerFactor
  exact Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

private lemma stabilizer_on_superset {n : ℕ} (v : Valuations n) (S : Finset ℝ)
    (hS : Finset.univ.image v ⊆ S) :
    stabilizerFactor v = ∏ x ∈ S, (MinBuyingFactorialBalance.multiplicity v x).factorial := by
  classical
  apply Finset.prod_subset hS
  intro x hx hnx
  have hm : MinBuyingFactorialBalance.multiplicity v x = 0 := by
    unfold MinBuyingFactorialBalance.multiplicity
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hnx (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩)
  simp [hm]

private lemma stabilizer_min_max {n : ℕ} (v w : Valuations n)
    (hv : Monotone v) (hw : Monotone w) :
    stabilizerFactor (fun i => min (v i) (w i)) * stabilizerFactor (fun i => max (v i) (w i)) ≤
      stabilizerFactor v * stabilizerFactor w := by
  classical
  let S := Finset.univ.image v ∪ Finset.univ.image w
  have hmin : Finset.univ.image (fun i => min (v i) (w i)) ⊆ S := by
    rintro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    rcases le_total (v i) (w i) with h | h
    · rw [min_eq_left h]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    · rw [min_eq_right h]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hmax : Finset.univ.image (fun i => max (v i) (w i)) ⊆ S := by
    rintro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    rcases le_total (v i) (w i) with h | h
    · rw [max_eq_right h]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    · rw [max_eq_left h]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [stabilizer_on_superset _ S hmin,stabilizer_on_superset _ S hmax,
    stabilizer_on_superset v S Finset.subset_union_left,
    stabilizer_on_superset w S Finset.subset_union_right]
  exact MinBuyingFactorialBalance.multiplicity_factorial_product v w hv hw S

private lemma orbit_multiplier {n : ℕ} (v w : Valuations n)
    (hv : Monotone v) (hw : Monotone w) :
    ((n.factorial : ℝ) / stabilizerFactor v) * ((n.factorial : ℝ) / stabilizerFactor w) ≤
      ((n.factorial : ℝ) / stabilizerFactor (fun i => max (v i) (w i))) *
        ((n.factorial : ℝ) / stabilizerFactor (fun i => min (v i) (w i))) := by
  have hpos (z : Valuations n) : 0 < (stabilizerFactor z : ℝ) := Nat.cast_pos.mpr (stabilizer_pos z)
  have hden : (stabilizerFactor (fun i => max (v i) (w i)) : ℝ) *
      (stabilizerFactor (fun i => min (v i) (w i)) : ℝ) ≤
      (stabilizerFactor v : ℝ) * (stabilizerFactor w : ℝ) := by
    exact_mod_cast (by simpa [mul_comm] using stabilizer_min_max v w hv hw)
  rw [div_mul_div_comm,div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos (hpos v) (hpos w)) (mul_pos (hpos _) (hpos _))).mpr
  exact mul_le_mul_of_nonneg_left hden (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem solution (n : ℕ) (w : PMF (Valuations n))
    (hex : Exchangeable w.toMeasure) (hmtp : MTP2 (fun v => (w v).toReal)) :
    MTP2 (fun v => ((w.map (fun z : Valuations n => z ∘ Tuple.sort z)) v).toReal) := by
  have hmass (v : Valuations n) (hv : Monotone v) :
      ((w.map (fun z : Valuations n => z ∘ Tuple.sort z)) v).toReal =
        ((n.factorial : ℝ) / stabilizerFactor v) * (w v).toReal := by
    simpa only [stabilizerFactor,Nat.cast_prod,MinBuyingFactorialBalance.multiplicity] using (sorted_pmf_mass n w hex v).1 hv
  intro v z
  dsimp only
  by_cases hv : Monotone v
  · by_cases hz : Monotone z
    · rw [hmass v hv,hmass z hz,hmass _ (hv.max hz),hmass _ (hv.min hz)]
      have hc := orbit_multiplier v z hv hz
      have hm := hmtp v z
      have hcoeff : 0 ≤ ((n.factorial : ℝ) / stabilizerFactor (fun i => max (v i) (z i))) *
          ((n.factorial : ℝ) / stabilizerFactor (fun i => min (v i) (z i))) := by positivity
      have hh := mul_le_mul hc hm (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hcoeff
      calc
        ((n.factorial : ℝ) / stabilizerFactor v) * (w v).toReal *
            (((n.factorial : ℝ) / stabilizerFactor z) * (w z).toReal) =
            (((n.factorial : ℝ) / stabilizerFactor v) * ((n.factorial : ℝ) / stabilizerFactor z)) *
              ((w v).toReal * (w z).toReal) := by ring
        _ ≤ _ := hh
        _ = _ := by ring
    · rw [(sorted_pmf_mass n w hex z).2 hz,ENNReal.toReal_zero,mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · rw [(sorted_pmf_mass n w hex v).2 hv,ENNReal.toReal_zero,zero_mul]
    exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
