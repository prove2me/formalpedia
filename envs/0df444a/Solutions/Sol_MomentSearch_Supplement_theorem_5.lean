-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:08:42.134051+00:00
-- url     : https://prove2.me/submissions/d3add1ac-8b53-40ae-adbf-ce2d1416b31a

import Mathlib
import Theorems.Thm_MomentSearch_kraft_average_depth
import Definitions.Def_MomentSearch_OPT
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_Supplement_cdf
import Definitions.Def_MomentSearch_Supplement_coarseGreedy
open MomentSearch MomentSearch.Supplement
open scoped BigOperators ENNReal

private lemma binary_depth (d a b : ℕ) (hab : a ≤ b) (hs : b + 1 - a ≤ 2 ^ d)
    (t : ℕ) (ha : a ≤ t) (hb : t ≤ b) : queries (binarySearchTree a b hab) t ≤ d := by
  induction d generalizing a b with
  | zero =>
    have he : a = b := by simp only [pow_zero] at hs; omega
    subst b
    rw [binarySearchTree]
    simp [queries]
  | succ d ih =>
    by_cases he : a = b
    · subst b; rw [binarySearchTree]; simp [queries]
    rw [binarySearchTree, dif_neg he]
    have hl : a < (a+b)/2 → (a+b)/2-1+1-a ≤ 2^d := by
      rw [pow_succ] at hs; omega
    have hr : (a+b)/2 < b → b+1-((a+b)/2+1) ≤ 2^d := by
      rw [pow_succ] at hs; omega
    rcases lt_trichotomy t ((a+b)/2) with ht | ht | ht
    · have hav : a < (a+b)/2 := by omega
      have hh := ih a ((a+b)/2-1) (by omega) (hl hav) ha (by omega)
      simp only [queries, if_neg ht.ne, if_pos ht, dif_pos hav]
      omega
    · subst t; simp [queries]
    · have hvb : (a+b)/2 < b := by omega
      have hh := ih ((a+b)/2+1) b (by omega) (hr hvb) (by omega) hb
      simp only [queries, if_neg ht.ne.symm, if_neg (not_lt_of_gt ht), dif_pos hvb]
      omega

private lemma coarse_aux_depth {n : ℕ} (π : Fin n → ℝ) (med : ℕ → ℕ → ℕ)
    (h j d a b : ℕ) (hab : a ≤ b) (hs : b+1-a ≤ 2^d)
    (t : ℕ) (ha : a ≤ t) (hb : t ≤ b) :
    queries (coarseGreedyAux π med h j a b hab) t ≤ h-j+d := by
  rw [coarseGreedyAux]
  split_ifs with he hm
  · subst b; simp [queries]
  · rcases lt_trichotomy t (med a b) with ht | ht | ht
    · have hav : a < med a b := by omega
      have hh := coarse_aux_depth π med h (j+1) d a (med a b-1) (by omega)
        (by omega) t ha (by omega)
      simp only [queries, if_neg ht.ne, if_pos ht, dif_pos hav]
      omega
    · subst t; simp [queries]; omega
    · have hvb : med a b < b := by omega
      have hh := coarse_aux_depth π med h (j+1) d (med a b+1) b (by omega)
        (by omega) t (by omega) hb
      simp only [queries, if_neg ht.ne.symm, if_neg (not_lt_of_gt ht), dif_pos hvb]
      omega
  · exact (binary_depth d a b hab hs t ha hb).trans (by omega)
termination_by b-a

private lemma mass_atom_le {n : ℕ} {π : Fin n → ℝ} (hπ : ∀ i, 0 ≤ π i)
    (a c : ℕ) (t : Fin n) (ha : a ≤ t.val) (hc : t.val < c) :
    π t ≤ massIco π a c := by
  classical
  calc
    π t = (if a ≤ t.val ∧ t.val < c then π t else 0) := by simp [ha, hc]
    _ ≤ massIco π a c := Finset.single_le_sum (f := fun i => if a ≤ i.val ∧ i.val < c then π i else 0)
      (fun i _ => by split_ifs <;> [exact hπ i; rfl]) (Finset.mem_univ t)

private lemma mass_full {n : ℕ} {π : Fin n → ℝ}
    (hπ : π ∈ stdSimplex ℝ (Fin n)) : massIco π 0 n = 1 := by
  simpa [massIco] using hπ.2

private lemma coarse_aux_heavy {n : ℕ} (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (med : ℕ → ℕ → ℕ) (hm : IsMedianRule π med)
    (h j a b : ℕ) (hab : a ≤ b) (hb : b < n)
    (t : Fin n) (ha : a ≤ t.val) (htb : t.val ≤ b)
    (hp : 0 < π t) (hc : massIco π a (b+1) < π t * (2 : ℝ)^(h-j)) :
    π t * (2 : ℝ)^queries (coarseGreedyAux π med h j a b hab) t.val ≤
      2 * massIco π a (b+1) := by
  have hatom := mass_atom_le hπ a (b+1) t ha (by omega)
  have hmass : 0 < massIco π a (b+1) := hp.trans_le hatom
  have hj : j < h := by
    by_contra hnot
    have he : h-j=0 := by omega
    simp only [he, pow_zero, mul_one] at hc
    linarith
  have hmed := hm a b hab hb hmass
  have medlo := hmed.1
  have medhi := hmed.2.1
  rw [coarseGreedyAux]
  by_cases he : a = b
  · simp only [dif_pos he]
    subst b
    simp only [queries, pow_zero, mul_one]
    linarith
  rw [dif_neg he, dif_pos ⟨hj, hmass, hmed.1, hmed.2.1⟩]
  have hexp : (2 : ℝ)^(h-j) = (2 : ℝ)^(h-(j+1))*2 := by
    rw [show h-j = (h-(j+1))+1 by omega, pow_succ]
  rw [hexp] at hc
  rcases lt_trichotomy t.val (med a b) with ht | ht | ht
  · have hav : a < med a b := by omega
    have hs : massIco π a (med a b-1+1) ≤ massIco π a (b+1)/2 := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ med a b)] using hmed.2.2.1
    have hsmall : massIco π a (med a b-1+1) < π t * (2:ℝ)^(h-(j+1)) := by nlinarith
    have hh := coarse_aux_heavy π hπ med hm h (j+1) a (med a b-1) (by omega)
      (by omega) t ha (by omega) hp hsmall
    simp only [queries, if_neg ht.ne, if_pos ht, dif_pos hav, pow_add, pow_one]
    nlinarith
  · simp only [queries, if_pos ht, pow_one]
    linarith
  · have hvb : med a b < b := by omega
    have hs := hmed.2.2.2
    have hsmall : massIco π (med a b+1) (b+1) < π t * (2:ℝ)^(h-(j+1)) := by nlinarith
    have hh := coarse_aux_heavy π hπ med hm h (j+1) (med a b+1) b (by omega)
      hb t (by omega) htb hp hsmall
    simp only [queries, if_neg ht.ne.symm, if_neg (not_lt_of_gt ht), dif_pos hvb,
      pow_add, pow_one]
    nlinarith
termination_by b-a

private lemma mass_split {n : ℕ} (π : Fin n → ℝ) {a c d : ℕ}
    (hac : a ≤ c) (hcd : c ≤ d) :
    massIco π a c + massIco π c d = massIco π a d := by
  unfold massIco
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> first | omega | ring

private lemma median_exists {n : ℕ} (π : Fin n → ℝ) (_hπ : ∀ i, 0 ≤ π i)
    (a b : ℕ) (hab : a ≤ b) (_hb : b < n) (hmass : 0 < massIco π a (b+1)) :
    ∃ m, IsMedian π a b m := by
  let s := {m : ℕ | a ≤ m ∧ m ≤ b ∧ massIco π a (b+1)/2 ≤ massIco π a (m+1)}
  have hs : s.Nonempty := ⟨b, hab, le_rfl, by linarith⟩
  have hmin := Nat.sInf_mem hs
  change a ≤ sInf s ∧ sInf s ≤ b ∧ _ at hmin
  refine ⟨sInf s, hmin.1, hmin.2.1, ?_, ?_⟩
  · by_cases he : sInf s = a
    · have hz : massIco π a a = 0 := by
        simp [massIco, show ∀ i : Fin n, ¬ (a ≤ i.val ∧ i.val < a) from fun i => by omega]
      rw [he, hz]
      linarith
    · by_contra hh
      have hx : sInf s - 1 ∈ s := by
        refine ⟨by omega, by omega, ?_⟩
        rw [Nat.sub_add_cancel (by omega : 1 ≤ sInf s)]
        linarith
      have := Nat.sInf_le hx
      omega
  · have hh := mass_split π (by omega : a ≤ sInf s+1) (by omega : sInf s+1 ≤ b+1)
    linarith [hmin.2.2]

private lemma median_rule_exists {n : ℕ} (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    ∃ med, IsMedianRule π med := by
  classical
  let med : ℕ → ℕ → ℕ := fun a b =>
    if h : a ≤ b ∧ b < n ∧ 0 < massIco π a (b+1) then
      (median_exists π hπ a b h.1 h.2.1 h.2.2).choose else a
  refine ⟨med, ?_⟩
  intro a b hab hb hp
  have hcond : a ≤ b ∧ b < n ∧ 0 < massIco π a (b+1) := ⟨hab, hb, hp⟩
  simp only [med, dif_pos hcond]
  exact (median_exists π hπ a b hab hb hp).choose_spec

private lemma cdf_atom {n : ℕ} (p : Fin n → ℝ) (t : Fin n) :
    p t = cdf p t.val - (if t.val=0 then 0 else cdf p (t.val-1)) := by
  classical
  by_cases ht : t.val = 0
  · simp only [if_pos ht, sub_zero]
    unfold cdf
    rw [Finset.sum_eq_single t]
    · simp
    · intro i _ hi
      have hne : i.val ≠ 0 := by intro he; apply hi; exact Fin.ext (he.trans ht.symm)
      simp [ht, show ¬ i.val ≤ 0 by omega]
    · simp
  · simp only [if_neg ht, cdf, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single t]
    · simp [show ¬ t.val ≤ t.val-1 by omega]
    · intro i _ hi
      have hne : i.val ≠ t.val := fun hh => hi (Fin.ext hh)
      split_ifs <;> first | omega | ring
    · simp

private lemma atom_error {n : ℕ} (p π : Fin n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : kolDist p π ≤ δ) (t : Fin n) : |p t - π t| ≤ 2*δ := by
  have hc (i : Fin n) : |cdf p i.val - cdf π i.val| ≤ δ :=
    (le_ciSup (f := fun i : Fin n => |cdf p i.val - cdf π i.val|)
      (Set.finite_range _).bddAbove i).trans hd
  have ht := hc t
  have hp := cdf_atom p t
  have hπ := cdf_atom π t
  by_cases he : t.val=0
  · simp only [if_pos he] at hp hπ
    rw [hp, hπ]
    simpa using ht.trans (by linarith : δ ≤ 2*δ)
  · have hprev := hc ⟨t.val-1, by have := t.isLt; omega⟩
    simp only [if_neg he] at hp hπ
    rw [abs_le] at ht hprev ⊢
    dsimp at hprev
    constructor <;> linarith

private lemma coarse_depth {n : ℕ} (hn : 2 ≤ n) (π : Fin n → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (med : ℕ → ℕ → ℕ) (t : Fin n) :
    (queries (coarseGreedy π ε med) t.val : ℝ) ≤ 4 * Real.logb 2 n := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ Real.logb 2 n := by
    simpa using Real.logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) hnR
  have hc := coarse_aux_depth π med ⌈ε * Real.logb 2 n⌉₊ 0 (Nat.clog 2 n)
    0 (n-1) (Nat.zero_le _) (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using Nat.le_pow_clog (by norm_num : 1 < 2) n)
    t.val (Nat.zero_le _) (by have := t.isLt; omega)
  have hcR : (queries (coarseGreedy π ε med) t.val : ℝ) ≤
      (⌈ε * Real.logb 2 n⌉₊ : ℝ) + Nat.clog 2 n := by exact_mod_cast hc
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hε.le (by linarith : 0 ≤ Real.logb 2 n))
  have hd := Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.logb 2 n)
  rw [show ⌈Real.logb 2 (n:ℝ)⌉₊ = Nat.clog 2 n from Real.natCeil_logb_natCast 2 n] at hd
  nlinarith

private lemma coarse_pointwise {n : ℕ} (hn : 2 ≤ n) (p π : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hπ : π ∈ stdSimplex ℝ (Fin n))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : kolDist p π ≤ (n : ℝ)^(-ε))
    (med : ℕ → ℕ → ℕ) (hm : IsMedianRule π med) (t : Fin n) (hpt : 0 < p t) :
    (queries (coarseGreedy π ε med) t.val : ℝ) ≤
      (20 / ε) * (1 + Real.logb 2 (1 / p t)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 1 ≤ Real.logb 2 n := by
    have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
    simpa using Real.logb_le_logb_of_le (b:=2) (by norm_num) (by norm_num : (0:ℝ)<2) hnR
  have hple : p t ≤ 1 := by
    calc p t ≤ ∑ i, p i := Finset.single_le_sum (fun i _ => hp.1 i) (Finset.mem_univ t)
         _ = 1 := hp.2
  have hinfo : 0 ≤ Real.logb 2 (1 / p t) :=
    Real.logb_nonneg (by norm_num) ((one_le_div hpt).2 hple)
  have hdepth := coarse_depth hn π ε hε hε1 med t
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hε).2
  by_cases hsmall : ε * Real.logb 2 n < 4
  · nlinarith [mul_le_mul_of_nonneg_left hdepth hε.le]
  have hδpos : 0 < (n:ℝ)^(-ε) := Real.rpow_pos_of_pos hnpos _
  by_cases hheavy : 4 * (n:ℝ)^(-ε) < p t
  · have he := (abs_le.mp (atom_error p π _ hδpos.le hd t)).2
    have hπpos : 0 < π t := by linarith
    have hπδ : (n:ℝ)^(-ε) < π t := by linarith
    have hpowpos : 0 < (n:ℝ)^ε := Real.rpow_pos_of_pos hnpos _
    have hrep : (2:ℝ)^(ε * Real.logb 2 n) = (n:ℝ)^ε := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_logb (by norm_num) (by norm_num) hnpos]
    have hcap : (n:ℝ)^ε ≤ (2:ℝ)^⌈ε * Real.logb 2 n⌉₊ := by
      rw [← hrep, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    have hmul : (n:ℝ)^(-ε) * (n:ℝ)^ε = 1 := by
      rw [Real.rpow_neg hnpos.le, inv_mul_cancel₀ hpowpos.ne']
    have hh : 1 < π t * (2:ℝ)^⌈ε * Real.logb 2 n⌉₊ := by
      have h1 := mul_lt_mul_of_pos_right hπδ hpowpos
      have h2 := mul_le_mul_of_nonneg_left hcap hπpos.le
      nlinarith
    have hroot : massIco π 0 (n-1+1) = 1 := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact mass_full hπ
    have hg := coarse_aux_heavy π hπ.1 med hm ⌈ε * Real.logb 2 n⌉₊ 0 0 (n-1)
      (Nat.zero_le _) (by omega) t (Nat.zero_le _) (by have := t.isLt; omega) hπpos
      (by simpa [hroot] using hh)
    rw [hroot, mul_one] at hg
    change π t * (2:ℝ)^queries (coarseGreedy π ε med) t.val ≤ 2 at hg
    have hpow : 0 ≤ (2:ℝ)^queries (coarseGreedy π ε med) t.val := by positivity
    have hg' : (2:ℝ)^queries (coarseGreedy π ε med) t.val ≤ 4 / p t := by
      apply (le_div_iff₀ hpt).2
      nlinarith [mul_le_mul_of_nonneg_right (show p t ≤ 2 * π t by linarith) hpow]
    have hl := Real.logb_le_logb_of_le (b:=2) (by norm_num) (by positivity) hg'
    have hfour : Real.logb 2 4 = 2 := by
      have hh := Real.logb_pow 2 2 2
      norm_num at hh ⊢
      exact hh
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2), mul_one,
      Real.logb_div (by norm_num) hpt.ne', hfour] at hl
    have hi : Real.logb 2 (1/p t) = -Real.logb 2 (p t) := by
      rw [Real.logb_div one_ne_zero hpt.ne']; simp
    rw [sub_eq_add_neg, ← hi] at hl
    nlinarith [mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (queries (coarseGreedy π ε med) t.val))]
  · have hl := Real.logb_le_logb_of_le (b:=2) (by norm_num) hpt (le_of_not_gt hheavy)
    have hfour : Real.logb 2 4 = 2 := by
      have hh := Real.logb_pow 2 2 2
      norm_num at hh ⊢
      exact hh
    rw [Real.logb_mul (by norm_num) hδpos.ne', hfour,
      Real.logb_rpow_eq_mul_logb_of_pos hnpos] at hl
    have hi : Real.logb 2 (1/p t) = -Real.logb 2 (p t) := by
      rw [Real.logb_div one_ne_zero hpt.ne']; simp
    nlinarith [mul_le_mul_of_nonneg_left hdepth hε.le]

private lemma strategy_kraft {n : ℕ} (hn : 2 ≤ n) (S : Strategy n) :
    ∑ t : Fin n, ((3:ℝ)^queries S t.val)⁻¹ ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact (MomentSearch.kraft_average_depth hn S m (fun t => t) Function.injective_id).1

private lemma entropy_le_cost {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (S : Strategy n) :
    (∑ t : Fin n, p t * Real.logb 2 (1 / p t)) ≤ Real.logb 2 3 * cost p S := by
  have hpoint (t : Fin n) :
      p t * Real.log (1 / p t) ≤
        Real.log 3 * (p t * (queries S t.val : ℝ)) + ((3:ℝ)^queries S t.val)⁻¹ - p t := by
    by_cases hz : p t = 0
    · simp only [hz, zero_mul, sub_zero, mul_zero, zero_add]
      positivity
    have hpt : 0 < p t := lt_of_le_of_ne (hp.1 t) (Ne.symm hz)
    have hw : 0 < ((3:ℝ)^queries S t.val)⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hw hpt)) hpt.le
    rw [Real.log_div hw.ne' hpt.ne', Real.log_inv, Real.log_pow] at hh
    have heq : p t * (((3:ℝ)^queries S t.val)⁻¹ / p t - 1) =
        ((3:ℝ)^queries S t.val)⁻¹ - p t := by field_simp
    rw [heq] at hh
    rw [Real.log_div one_ne_zero hpt.ne', Real.log_one]
    nlinarith
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hpoint t)
  have hk := strategy_kraft hn S
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2] at hs
  have hnat : (∑ t : Fin n, p t * Real.log (1 / p t)) ≤ Real.log 3 * cost p S := by
    change (∑ t : Fin n, p t * Real.log (1 / p t)) ≤ Real.log 3 *
      (∑ t : Fin n, p t * (queries S t.val : ℝ))
    linarith
  calc
    _ = (∑ t : Fin n, p t * Real.log (1 / p t)) / Real.log 2 := by
      simp only [Real.logb, mul_div_assoc, Finset.sum_div]
    _ ≤ (Real.log 3 * cost p S) / Real.log 2 :=
      div_le_div_of_nonneg_right hnat (Real.log_nonneg (by norm_num))
    _ = Real.logb 2 3 * cost p S := by unfold Real.logb; ring

private lemma queries_pos {a b : ℕ} (S : SearchTree a b) (hab : a < b) (t : ℕ) :
    1 ≤ queries S t := by
  cases S with
  | leaf a => omega
  | node v hav hvb hab l r =>
    simp only [queries]
    split_ifs <;> omega

private lemma cost_ge_one {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (S : Strategy n) : 1 ≤ cost p S := by
  rw [← hp.2]
  apply Finset.sum_le_sum
  intro t _
  have hq : (1:ℝ) ≤ queries S t.val := by exact_mod_cast queries_pos S (by omega) t.val
  nlinarith [hp.1 t]

private lemma opt_ge_one {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) : 1 ≤ OPT p := by
  let : Nonempty (Strategy n) := ⟨binarySearchTree 0 (n-1) (Nat.zero_le _)⟩
  exact le_ciInf (fun S => cost_ge_one hn p hp S)

private lemma entropy_opt {n : ℕ} (hn : 2 ≤ n) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) :
    1 + (∑ t : Fin n, p t * Real.logb 2 (1 / p t)) ≤ (1 + Real.logb 2 3) * OPT p := by
  have hL : 0 ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have hden : 0 < 1 + Real.logb 2 3 := by linarith
  have hi : (1 + ∑ t : Fin n, p t * Real.logb 2 (1 / p t)) / (1+Real.logb 2 3) ≤ OPT p := by
    let : Nonempty (Strategy n) := ⟨binarySearchTree 0 (n-1) (Nat.zero_le _)⟩
    apply le_ciInf
    intro S
    apply (div_le_iff₀ hden).2
    have h1 := cost_ge_one hn p hp S
    have h2 := entropy_le_cost hn p hp S
    nlinarith
  have hh := (div_le_iff₀ hden).1 hi
  nlinarith

private lemma coarse_cost {n : ℕ} (hn : 2 ≤ n) (p π : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hπ : π ∈ stdSimplex ℝ (Fin n))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hd : kolDist p π ≤ (n : ℝ)^(-ε))
    (med : ℕ → ℕ → ℕ) (hm : IsMedianRule π med) :
    cost p (coarseGreedy π ε med) ≤ (20 * (1 + Real.logb 2 3)) / ε * OPT p := by
  have hpoint (t : Fin n) : p t * (queries (coarseGreedy π ε med) t.val : ℝ) ≤
      (20 / ε) * (p t + p t * Real.logb 2 (1/p t)) := by
    by_cases hz : p t = 0
    · simp [hz]
    have hpt : 0 < p t := lt_of_le_of_ne (hp.1 t) (Ne.symm hz)
    have hh := mul_le_mul_of_nonneg_left (coarse_pointwise hn p π hp hπ ε hε hε1 hd med hm t hpt) hpt.le
    nlinarith
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hpoint t)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hp.2] at hs
  have hH := mul_le_mul_of_nonneg_left (entropy_opt hn p hp) (by positivity : 0 ≤ 20/ε)
  change cost p (coarseGreedy π ε med) ≤ _ at hs
  calc
    _ ≤ (20 / ε) * (1 + ∑ t : Fin n, p t * Real.logb 2 (1/p t)) := hs
    _ ≤ (20 / ε) * ((1 + Real.logb 2 3) * OPT p) := hH
    _ = _ := by ring

private lemma coarse_collection {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (𝒰 : Set (Set (Fin n → ℝ)))
    (h𝒰 : ∀ U ∈ 𝒰, ∃ π ∈ stdSimplex ℝ (Fin n), U ⊆ kolBall π ((n:ℝ)^(-ε))) :
    approxFactor 𝒰 ≤ ENNReal.ofReal ((20 * (1 + Real.logb 2 3)) / ε) := by
  unfold approxFactor
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  obtain ⟨π, hπ, hsub⟩ := h𝒰 U hU
  obtain ⟨med, hm⟩ := median_rule_exists π hπ.1
  apply (iInf_le _ (coarseGreedy π ε med)).trans
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  obtain ⟨hps, hd⟩ := hsub hp
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (show 0 < OPT p from lt_of_lt_of_le (by norm_num) (opt_ge_one hn p hps))).2
  exact coarse_cost hn p π hps hπ ε hε hε1 hd med hm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ π ∈ stdSimplex ℝ (Fin n), ∀ U : Set (Fin n → ℝ), U.Nonempty →
          U ⊆ kolBall π ((n : ℝ) ^ (-ε)) →
          ∀ med : ℕ → ℕ → ℕ, IsMedianRule π med →
            ∀ p ∈ U, cost p (coarseGreedy π ε med) ≤ C / ε * OPT p) ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∀ 𝒰 : Set (Set (Fin n → ℝ)),
          (∀ U ∈ 𝒰, ∃ π ∈ stdSimplex ℝ (Fin n), U ⊆ kolBall π ((n : ℝ) ^ (-ε))) →
          approxFactor 𝒰 ≤ ENNReal.ofReal (C / ε)) ∧
      (∀ (n : ℕ), 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        approxFactor (kolCollection n ((n : ℝ) ^ (-ε))) ≤ ENNReal.ofReal (C / ε)) := by
  have hc : 0 < 20 * (1 + Real.logb 2 3) := by
    have hh := Real.logb_nonneg (b:=2) (by norm_num) (by norm_num : (1:ℝ) ≤ 3)
    positivity
  refine ⟨20 * (1 + Real.logb 2 3), hc, ?_, ?_, ?_⟩
  · intro n hn ε hε hε1 π hπ U _hUn hsub med hm p hp
    obtain ⟨hps, hd⟩ := hsub hp
    exact coarse_cost hn p π hps hπ ε hε hε1 hd med hm
  · intro n hn ε hε hε1 𝒰 h𝒰
    exact coarse_collection hn ε hε hε1 𝒰 h𝒰
  · intro n hn ε hε hε1
    apply coarse_collection hn ε hε hε1
    rintro U ⟨π, hπ, rfl⟩
    exact ⟨π, hπ, Set.Subset.rfl⟩
