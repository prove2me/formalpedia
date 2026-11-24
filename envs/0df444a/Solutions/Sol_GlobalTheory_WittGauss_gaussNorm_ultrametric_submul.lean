-- Prove2me | solution 1 for GlobalTheory.WittGauss.gaussNorm_ultrametric_submul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:05.260875+00:00
-- url     : https://prove2.me/submissions/ee56f1b3-f231-4d44-9334-129bc00bce72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Theorems.Thm_GlobalTheory_WittGauss_pow_eq
import Theorems.Thm_GlobalTheory_WittGauss_weight_add_trunc
import Theorems.Thm_GlobalTheory_WittGauss_root_pow
import Theorems.Thm_GlobalTheory_WittGauss_pow_root
import Theorems.Thm_GlobalTheory_WittGauss_coeff_eq_of_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
namespace GlobalTheory.WittGauss
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ ∀ x y, N (x * y) ≤ N x * N y := by
  intro l hl R _ _ _ a hb h0 h1 hm ha r hr0 hr1 N hN
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by
    have : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    positivity
  have hle1 : ∀ (x : WittVector l R) (n : ℕ),
      a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ 1 := fun x n =>
    mul_le_one₀ (Real.rpow_le_one (hb _).1 (hb _).2 (hexp n).le) (pow_nonneg hr0.le _)
      (pow_le_one₀ hr0.le hr1.le)
  have hge : ∀ (x : WittVector l R) (n : ℕ),
      a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ N x := fun x n => by
    rw [hN]
    exact le_ciSup (f := fun n : ℕ => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n)
      ⟨1, by rintro _ ⟨m, rfl⟩; exact hle1 x m⟩ n
  have hle : ∀ (x : WittVector l R) (c : ℝ),
      (∀ n, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n ≤ c) → N x ≤ c := fun x c h => by
    rw [hN]; exact ciSup_le h
  have hnn : ∀ x, 0 ≤ N x := fun x =>
    (mul_nonneg (Real.rpow_nonneg (hb _).1 _) (pow_nonneg hr0.le _)).trans (hge x 0)
  have hadd : ∀ x y, N (x + y) ≤ max (N x) (N y) := by
    intro x y
    refine hle _ _ fun n => ?_
    set c := max (N x) (N y) with hc
    have hc0 : 0 ≤ c := (hnn x).trans (le_max_left _ _)
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have key : ∀ z : WittVector l R, N z ≤ c → ∀ i ≤ n, a (z.coeff i) ≤ (c / r ^ n) ^ l ^ i := by
      intro z hz i hi
      rw [← root_pow l i _ (hb (z.coeff i)).1]
      refine pow_le_pow_left₀ (Real.rpow_nonneg (hb _).1 _) ?_ _
      rw [le_div_iff₀ hrn]
      refine le_trans ?_ ((hge z i).trans hz)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hi)
        (Real.rpow_nonneg (hb _).1 _)
    have h := weight_add_trunc a hb h0 h1 hm ha l (c / r ^ n) (by positivity) x y n
      (key x (le_max_left _ _)) (key y (le_max_right _ _))
    rw [← le_div_iff₀ hrn, ← pow_root l n (c / r ^ n) (by positivity)]
    exact Real.rpow_le_rpow (hb _).1 h (hexp n).le
  have hzero : N 0 = 0 := by
    refine le_antisymm (hle _ _ fun n => ?_) (hnn _)
    rw [WittVector.zero_coeff, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hte : ∀ (u : R) (k : ℕ), N (teichmuller l u * (l : WittVector l R) ^ k) ≤ a u * r ^ k := by
    intro u k
    refine hle _ _ fun n => ?_
    by_cases h : n = k
    · subst h
      rw [teichmuller_mul_pow_coeff, pow_eq a h1 hm, pow_root l n _ (hb _).1]
    · rw [teichmuller_mul_pow_coeff_of_ne _ h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
      exact mul_nonneg (hb _).1 (pow_nonneg hr0.le _)
  have hroot : ∀ (x : WittVector l R) (i : ℕ),
      a (((_root_.frobeniusEquiv R l).symm ^ i) (x.coeff i)) * r ^ i ≤ N x := by
    intro x i
    have e : ∀ (i : ℕ) (u : R), (((_root_.frobeniusEquiv R l).symm ^ i) u) ^ l ^ i = u := by
      intro i
      induction i with
      | zero => intro u; simp
      | succ i ih =>
        intro u
        rw [pow_succ', RingAut.mul_apply, pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]
    have := hge x i
    rwa [← e i (x.coeff i), pow_eq a h1 hm, pow_root l i _ (hb _).1] at this
  have hmul : ∀ x y, N (x * y) ≤ N x * N y := by
    intro x y
    refine hle _ _ fun n => ?_
    have hx := dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x n
    have hy := dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y n
    have hxy : ∀ x' y' : WittVector l R, (l : WittVector l R) ^ (n + 1) ∣ x - x' →
        (l : WittVector l R) ^ (n + 1) ∣ y - y' → (x * y).coeff n = (x' * y').coeff n := by
      intro x' y' h h'
      refine coeff_eq_of_dvd l _ _ n ?_
      have : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
      rw [this]
      exact dvd_add (h.mul_right _) (h'.mul_left _)
    rw [hxy _ _ hx hy]
    refine (hge _ n).trans ?_
    have hc : 0 ≤ N x * N y := mul_nonneg (hnn x) (hnn y)
    rw [Finset.sum_mul_sum]
    refine sum_le N hzero hadd _ _ _ hc fun i _ => sum_le N hzero hadd _ _ _ hc fun j _ => ?_
    rw [mul_mul_mul_comm, ← map_mul, ← pow_add]
    refine (hte _ _).trans ?_
    rw [hm, pow_add, mul_mul_mul_comm]
    exact mul_le_mul (hroot x i) (hroot y j) (mul_nonneg (hb _).1 (pow_nonneg hr0.le _)) (hnn x)
  have hneg : ∀ x, N (-x) ≤ N x := fun x => by
    rw [← neg_one_mul]
    refine (hmul _ _).trans ?_
    exact mul_le_of_le_one_left (hnn x) (hle _ _ (hle1 _))
  refine ⟨hadd, fun x => le_antisymm (hneg x) ?_, hmul⟩
  simpa using hneg (-x)
end GlobalTheory.WittGauss
