-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.exists_prime_in_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:38:49.334513+00:00
-- url     : https://prove2.me/submissions/3b673f25-787d-4ceb-9e4c-c1a4a4264495

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_not_summable_class
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_two_le_absNorm
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_summable_of_not_prime_or_le
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_congr
import Theorems.Thm_GlobalTheory_Mem_RayData_lseries_eq_exp_tsum
import Theorems.Thm_GlobalTheory_T_ray_L_nonvanishing_at_one
import Theorems.Thm_GlobalTheory_T_ray_class_partial_zeta_continuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
namespace GlobalTheory.Mem.RayPrimes
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (c : D.G) (N : ℕ), ∃ v : D.Pr, D.cls v.1.asIdeal = c ∧ (Ideal.absNorm v.1.asIdeal).Prime ∧ N < Ideal.absNorm v.1.asIdeal := by
  intro K _ _ _ h2 M hM D c N
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ, hρ, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K h2 M hM D
  choose Z hZd hZ1 _ hZs using hZ
  have hre : ∀ s : ℝ, 1 < s → 1 < (s : ℂ).re := fun s h => by simpa using h
  refine not_summable_class (fun v : D.Pr => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => D.cls v.1.asIdeal) ?_ ?_ (fun s => ∑ x, Z x s)
    (continuous_finsetSum _ fun x _ => (hZd x).continuous) ?_ ?_ c ?_
  · intro s hs
    refine (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.1.congr fun v => ?_
    rw [norm_natCast_cpow_of_pos (by linarith [two_le_absNorm v.1])]
    simp
  · intro χ hχ
    obtain ⟨L, hL, hL1, hL2⟩ := GlobalTheory.T.ray_L_nonvanishing_at_one K h2 M hM D χ hχ
    exact ⟨L, hL.continuous, hL1, fun s hs => by
      rw [hL2 s (hre s hs), (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D χ s (hre s hs)).2.2]⟩
  · simp only [hZ1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by exact_mod_cast hρ.ne')
  · intro s hs
    rw [← (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.2]
    have hco : D.coef 1 = ∑ x, D.cnt x := by
      funext m
      simp [RayData.coef]
    rw [hco, LSeries_sum fun x _ => (hZs x s (hre s hs)).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (hZs x s (hre s hs)).2
  · exact summable_of_not_prime_or_le h2 N (fun v : {v : D.Pr // D.cls v.1.asIdeal = c} => v.1.1)
      (fun i j hij => Subtype.ext (Subtype.ext hij)) fun i hi => hcon i.1 i.2 hi
end GlobalTheory.Mem.RayPrimes
