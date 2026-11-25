-- Prove2me | solution 1 for GlobalTheory.LaurentFrac.exists_frac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:42.774136+00:00
-- url     : https://prove2.me/submissions/c772ea54-0e8c-4368-b6fb-ece224fccc0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdZpowMul
import Theorems.Thm_GlobalTheory_LaurentFrac_prod_zpow_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFrac
namespace GlobalTheory.LaurentFrac
theorem _root_.solution (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (θ : R →+* V) {I : Type} [Fintype I] (s : I → R) (N : I → ℤ) (hs : ∀ i, θ (s i) ≠ 0) :
    ∃ x y : R, θ y ≠ 0 ∧
      (∏ i, algebraMap R (FractionRing R) (s i) ^ N i) * algebraMap R _ y = algebraMap R _ x ∧
      (∏ i, algebraMap V (FractionRing V) (θ (s i)) ^ N i) * algebraMap V _ (θ y)
        = algebraMap V _ (θ x) := by
  refine ⟨∏ i, s i ^ (N i).toNat, ∏ i, s i ^ (-N i).toNat, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [map_pow]
    exact pow_ne_zero _ (hs i)
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    have h : s i ≠ 0 := fun h => hs i (by rw [h, map_zero])
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 h
  · simp only [map_prod, map_pow]
    refine prod_zpow_mul _ N fun i => ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs i)
end GlobalTheory.LaurentFrac
