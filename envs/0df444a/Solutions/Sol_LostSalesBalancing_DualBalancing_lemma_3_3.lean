-- Prove2me | solution 1 for LostSalesBalancing.DualBalancing.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:13:17.949574+00:00
-- url     : https://prove2.me/submissions/eb904692-7816-4b91-88d3-9d03ea405626

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model
open Finset LeviBalancing.DualBalancing LostSalesBalancing.DualBalancing

private lemma sum_extend (f : ℤ → ℝ) (a b : ℤ) (h : a ≤ b + 1) :
    ∑ j ∈ Icc a (b + 1), f j = (∑ j ∈ Icc a b, f j) + f (b + 1) := by
  have he : Icc a (b + 1) = insert (b + 1) (Icc a b) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  rw [he, sum_insert (by simp)]
  ring

private lemma inventory_step (I : LSInstance) (d Q : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r) :
    onHand I d Q (r + 1) = onHand I d Q r - d r + lostUnits I d Q r +
      order I.toInstance Q (r + 1 - I.L) := by
  have hn : r.toNat = (r - 1).toNat + 1 := by omega
  have hc : ((r - 1).toNat : ℤ) = r - 1 := Int.toNat_of_nonneg (by omega)
  have he : onHand I d Q (r + 1) =
      max (onHand I d Q r - d r) 0 + order I.toInstance Q (r + 1 - I.L) := by
    simp only [onHand, show r + 1 - 1 = r by omega, hn, onHandNat, hc]
    congr 2 <;> congr 1 <;> ring
  rw [he, lostUnits]
  by_cases h : d r ≤ onHand I d Q r
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

private lemma inventory_sum (I : LSInstance) (d Q : ℤ → ℝ) (s : ℤ) (hs : 1 ≤ s) (k : ℕ) :
    onHand I d Q (s + k) =
      onHand I d Q s + (∑ j ∈ Icc (s + 1 - I.L) (s + k - I.L), order I.toInstance Q j) -
      (∑ r ∈ Icc s (s + k - 1), d r) +
      ∑ r ∈ Icc s (s + k - 1), lostUnits I d Q r := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    have h1 : Icc (s + 1 - (I.L : ℤ)) (s - I.L) = ∅ := by
      apply Icc_eq_empty_of_lt; omega
    have h2 : Icc s (s - 1) = ∅ := by
      apply Icc_eq_empty_of_lt; omega
    simp [h1, h2]
  | succ k ih =>
    rw [Nat.cast_succ]
    rw [show s + ((k : ℤ) + 1) = (s + k) + 1 by ring, inventory_step I d Q (s + k) (by omega), ih]
    rw [show s + (k : ℤ) + 1 - (I.L : ℤ) = (s + k - I.L) + 1 by ring,
      show s + (k : ℤ) + 1 - 1 = (s + k - 1) + 1 by ring]
    rw [sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega)]
    simp only [show s + (k : ℤ) - 1 + 1 = s + k by ring,
      show s + (k : ℤ) - (I.L : ℤ) + 1 = s + k + 1 - I.L by ring]
    ring


open Finset LeviBalancing.DualBalancing

/-- Equation (11), expressed in lost units so it remains valid for varying or zero penalties. -/
private theorem inventory_balance (I : LSInstance) (d Q : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hQ : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ Q j)
    (t s : ℤ) (ht : 1 ≤ t) (hs : t ≤ s) (hst : s ≤ t + I.L)
    (hT : t + I.L ≤ (I.T : ℤ)) :
    onHand I d Q (t + I.L) =
      truncPos I d Q s t - cumDemand d s (t + I.L - 1) +
        ∑ r ∈ Icc s (t + I.L - 1), lostUnits I d Q r := by
  have he := inventory_sum I d Q s (by omega) (t + I.L - s).toNat
  have hc : ((t + (I.L : ℤ) - s).toNat : ℤ) = t + I.L - s :=
    Int.toNat_of_nonneg (by omega)
  rw [hc, show s + (t + (I.L : ℤ) - s) = t + I.L by ring] at he
  simpa only [truncPos, cumDemand, max_eq_left (by omega : (1 : ℤ) ≤ s),
    show t + (I.L : ℤ) - I.L = t by ring] using he

private theorem sum_split (f : ℤ → ℝ) (a s b : ℤ) (has : a ≤ s) (hsb : s ≤ b+1) :
    ∑ r ∈ Icc a b, f r = (∑ r ∈ Icc a (s-1), f r) + ∑ r ∈ Icc s b, f r
    := by
  have he : Icc a b = Icc a (s-1) ∪ Icc s b := by ext r; simp only [mem_Icc, mem_union]; omega
  rw [he, sum_union]
  exact disjoint_left.mpr (by intro r hr hs; simp only [mem_Icc] at hr hs; omega)

private theorem local_charge (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j)
    (t : ℤ) (ht : 1 ≤ t) (hT : t + I.L ≤ (I.T : ℤ))
    (hmark : ¬ InTH I d QB QP t) (hpos : 0 < lostUnits I d QB (t+I.L)) :
    ∃ s ∈ Icc t (t+I.L),
      (∑ r ∈ Icc s (t+I.L), lostUnits I d QB r) ≤
      ∑ r ∈ Icc s (t+I.L), lostUnits I d QP r := by
  classical
  unfold InTH at hmark
  push_neg at hmark
  obtain ⟨s, hs, hY⟩ := hmark
  have hs' := mem_Icc.mp hs
  have hbalB := inventory_balance I d QB hd hB t s ht hs'.1 hs'.2 hT
  have hbalP := inventory_balance I d QP hd hP t s ht hs'.1 hs'.2 hT
  have hshort : onHand I d QB (t+I.L) < d (t+I.L) := by
    unfold lostUnits at hpos
    by_contra hnot
    have hle : d (t+I.L) - onHand I d QB (t+I.L) ≤ 0 := by linarith
    rw [max_eq_right hle] at hpos
    exact (lt_irrefl _ hpos)
  have hBend : lostUnits I d QB (t+I.L) = d (t+I.L) - onHand I d QB (t+I.L) := by
    unfold lostUnits; rw [max_eq_left (by linarith)]
  have hPend : d (t+I.L) - onHand I d QP (t+I.L) ≤ lostUnits I d QP (t+I.L) := le_max_left _ _
  refine ⟨s, hs, ?_⟩
  rw [show t + (I.L : ℤ) = (t+I.L-1)+1 by ring,
    sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega)]
  simp only [show t + (I.L : ℤ) - 1 + 1 = t+I.L by ring]
  rw [hBend]
  linarith

private theorem weighted_prefix (n : ℕ) (a b p : ℤ → ℝ)
    (hprefix : ∀ k : ℕ, k ≤ n → (∑ r ∈ Icc (1:ℤ) (k:ℤ), a r) ≤ ∑ r ∈ Icc (1:ℤ) (k:ℤ), b r)
    (hp : ∀ r : ℤ, 1 ≤ r → r ≤ (n:ℤ) → 0 ≤ p r)
    (hanti : ∀ r s : ℤ, 1 ≤ r → r ≤ s → s ≤ (n:ℤ) → p s ≤ p r) :
    (∑ r ∈ Icc (1:ℤ) (n:ℤ), p r * a r) ≤ ∑ r ∈ Icc (1:ℤ) (n:ℤ), p r * b r := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have hpre : ∀ k : ℕ, k ≤ n → (∑ r ∈ Icc (1:ℤ) (k:ℤ), a r) ≤ ∑ r ∈ Icc (1:ℤ) (k:ℤ), b r :=
      fun k hk => hprefix k (by omega)
    have hi := ih (fun r => p r - p (n+1)) hpre
      (by intro r hr hnr; have := hanti r (n+1) hr (by omega) (by simp); linarith)
      (by intro r s hr hrs hsn; have := hanti r s hr hrs (by omega); linarith)
    have hlast := mul_le_mul_of_nonneg_left (hprefix (n+1) le_rfl) (hp (n+1) (by omega) (by simp))
    have heq : ∀ f : ℤ → ℝ, (∑ r ∈ Icc (1:ℤ) ((n+1:ℕ):ℤ), p r * f r) =
        (∑ r ∈ Icc (1:ℤ) (n:ℤ), (p r - p (n+1)) * f r) +
          p (n+1) * ∑ r ∈ Icc (1:ℤ) ((n+1:ℕ):ℤ), f r := by
      intro f
      simp only [Nat.cast_add, Nat.cast_one]
      rw [sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega)]
      simp_rw [sub_mul]
      rw [sum_sub_distrib, ← mul_sum]
      ring
    rw [heq a, heq b]
    exact add_le_add hi hlast

private theorem initial_equal (I : LSInstance) (d QB QP : ℤ → ℝ)
    (r : ℤ) (hr : 1 ≤ r) (hrL : r ≤ I.L) :
    lostUnits I d QB r = lostUnits I d QP r := by
  have hn : ∀ n : ℕ, n < I.L → onHandNat I d QB n = onHandNat I d QP n := by
    intro n
    induction n with
    | zero => simp [onHandNat, order, show 1 - (I.L:ℤ) ≤ 0 by omega]
    | succ n ih =>
      intro hnL
      simp only [onHandNat, ih (by omega)]
      simp [order, show (n:ℤ)+2-I.L ≤ 0 by omega]
  unfold lostUnits onHand
  rw [hn (r-1).toNat (by omega)]

open scoped Classical in
private noncomputable def charged (I : LSInstance) (d QB QP : ℤ → ℝ) (r : ℤ) : ℝ :=
  if r ≤ I.L then lostUnits I d QP r else
    if ¬ InTH I d QB QP (r-I.L) then lostUnits I d QB r else 0

private theorem charge_le (I : LSInstance) (d QB QP : ℤ → ℝ) (r : ℤ) (hr : 1 ≤ r) :
    charged I d QB QP r ≤ lostUnits I d QB r := by
  classical
  by_cases hL : r ≤ I.L
  · simp only [charged, if_pos hL]
    rw [initial_equal I d QB QP r hr hL]
  · by_cases hm : ¬ InTH I d QB QP (r-I.L)
    · simp [charged, hL, hm]
    · simp only [charged, if_neg hL, if_neg hm]
      exact le_max_right _ _

private theorem prefix_charge (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j) :
    ∀ n : ℕ, n ≤ I.T → (∑ r ∈ Icc (1:ℤ) (n:ℤ), charged I d QB QP r) ≤
      ∑ r ∈ Icc (1:ℤ) (n:ℤ), lostUnits I d QP r := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnT
    by_cases hn0 : n = 0
    · subst n; simp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    by_cases hend : charged I d QB QP (m+1) ≤ lostUnits I d QP (m+1)
    · have hpref := ih m (by omega) (by omega)
      simp only [Nat.cast_succ]
      rw [sum_extend _ _ _ (by omega), sum_extend _ _ _ (by omega)]
      exact add_le_add hpref hend
    · have hL : (I.L:ℤ) < m+1 := by
        by_contra hh
        have hc : charged I d QB QP (m+1) = lostUnits I d QP (m+1) := by
          simp [charged, show (m:ℤ)+1 ≤ I.L by omega]
        exact hend (hc.le)
      have hmark : ¬ InTH I d QB QP ((m:ℤ)+1-I.L) := by
        by_contra hh
        have hc : charged I d QB QP (m+1) = 0 := by simp [charged, not_le.mpr hL, hh]
        exact hend (hc ▸ le_max_right _ _)
      have hc : charged I d QB QP (m+1) = lostUnits I d QB (m+1) := by
        simp [charged, not_le.mpr hL, hmark]
      have hpos : 0 < lostUnits I d QB (m+1) := by
        have hPnon : 0 ≤ lostUnits I d QP (m+1) := le_max_right _ _
        rw [hc] at hend
        linarith
      obtain ⟨s, hs, hcharge⟩ := local_charge I d QB QP hd hB hP
        ((m:ℤ)+1-I.L) (by omega) (by omega) hmark (by simpa using hpos)
      have hs1 : 1 ≤ s := by have := mem_Icc.mp hs; omega
      have hsn : s ≤ (m:ℤ)+1 := by have := mem_Icc.mp hs; omega
      have hpref := ih (s-1).toNat (by omega) (by omega)
      have hcast : ((s-1).toNat:ℤ) = s-1 := Int.toNat_of_nonneg (by omega)
      rw [hcast] at hpref
      have hsmall : (∑ r ∈ Icc s ((m:ℤ)+1), charged I d QB QP r) ≤
          ∑ r ∈ Icc s ((m:ℤ)+1), lostUnits I d QB r := by
        apply sum_le_sum
        intro r hr
        exact charge_le I d QB QP r (by have := mem_Icc.mp hr; omega)
      have hcharge' : (∑ r ∈ Icc s ((m:ℤ)+1), lostUnits I d QB r) ≤
          ∑ r ∈ Icc s ((m:ℤ)+1), lostUnits I d QP r := by simpa using hcharge
      simp only [Nat.cast_succ]
      rw [sum_split _ 1 s (m+1) hs1 (by omega), sum_split _ 1 s (m+1) hs1 (by omega)]
      exact add_le_add hpref (le_trans hsmall hcharge')

theorem weighted_charge (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j) :
    (∑ r ∈ Icc (1:ℤ) (I.T:ℤ), I.p r * charged I d QB QP r) ≤
      ∑ r ∈ Icc (1:ℤ) (I.T:ℤ), I.p r * lostUnits I d QP r := by
  exact weighted_prefix I.T _ _ I.p (prefix_charge I d QB QP hd hB hP) I.p_nonneg I.p_anti

open scoped Classical in
theorem solution (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j) :
    (∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter (fun t => ¬ InTH I d QB QP t),
      lostLS I d QB t) ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), lostLS I d QP t := by
  classical
  by_cases hTL : (I.T:ℤ) ≤ I.L
  · have he : Icc (1:ℤ) ((I.T:ℤ)-I.L) = ∅ := Icc_eq_empty_of_lt (by omega)
    simp [he]
  have hLT : (I.L:ℤ)+1 ≤ I.T := by omega
  have hshift : ∀ f : ℤ → ℝ,
      (∑ t ∈ Icc (1:ℤ) ((I.T:ℤ)-I.L), f (t+I.L)) =
        ∑ r ∈ Icc ((I.L:ℤ)+1) (I.T:ℤ), f r := by
    intro f
    apply sum_bij (fun (t : ℤ) ht => t+(I.L:ℤ))
    · intro t ht; simp only [mem_Icc] at ht ⊢; omega
    · intro t ht u hu he; omega
    · intro r hr
      refine ⟨r-I.L, ?_, by ring⟩
      simp only [mem_Icc] at hr ⊢; omega
    · intro t ht; rfl
  have hc := weighted_charge I d QB QP hd hB hP
  rw [sum_split _ 1 (I.L+1) I.T (by omega) (by omega),
    sum_split _ 1 (I.L+1) I.T (by omega) (by omega)] at hc
  have hfirst : (∑ r ∈ Icc (1:ℤ) ((I.L:ℤ)+1-1), I.p r * charged I d QB QP r) =
      ∑ r ∈ Icc (1:ℤ) ((I.L:ℤ)+1-1), I.p r * lostUnits I d QP r := by
    apply sum_congr rfl
    intro r hr
    have hrL : r ≤ I.L := by have := mem_Icc.mp hr; omega
    simp [charged, hrL]
  rw [hfirst] at hc
  have hlate : (∑ r ∈ Icc ((I.L:ℤ)+1) (I.T:ℤ), I.p r * charged I d QB QP r) ≤
      ∑ r ∈ Icc ((I.L:ℤ)+1) (I.T:ℤ), I.p r * lostUnits I d QP r := by linarith
  have hleft : (∑ t ∈ (Icc (1:ℤ) ((I.T:ℤ)-I.L)).filter (fun t => ¬ InTH I d QB QP t), lostLS I d QB t) =
      ∑ r ∈ Icc ((I.L:ℤ)+1) (I.T:ℤ), I.p r * charged I d QB QP r := by
    rw [sum_filter, ← hshift]
    apply sum_congr rfl
    intro t ht
    have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
    simp [lostLS, charged, show ¬ t+(I.L:ℤ) ≤ I.L by omega,
      show t+(I.L:ℤ)-I.L = t by ring]
  rw [hleft]
  change _ ≤ ∑ t ∈ Icc (1:ℤ) ((I.T:ℤ)-I.L), I.p (t+I.L) * lostUnits I d QP (t+I.L)
  rw [hshift (fun r => I.p r * lostUnits I d QP r)]
  exact hlate

#print axioms solution
