-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Dens.exists_smul_of_rank_le_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:41:18.716929+00:00
-- url     : https://prove2.me/submissions/8d5b23bb-bde0-4ccb-ab12-bfbadd14b036

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
import Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_eq_algebraMap_of_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
variable {R V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup V] [Module ℂ V] [Module R V]
  [IsScalarTower ℂ R V] [IsSimpleModule R V]
namespace GlobalTheory.ThK.Dbl.Dens
theorem _root_.solution (hV : Module.rank ℂ V ≤ ℵ₀) (φ : Module.End R V) :
    ∃ c : ℂ, ∀ m, φ m = c • m := by
  classical
  by_contra hne
  push Not at hne
  have hnt : Nontrivial V := IsSimpleModule.nontrivial R V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0 := by
    intro p hp h0
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_aeval_eq_zero φ hp h0
    obtain ⟨m, hm⟩ := hne c
    exact hm (by rw [hc, Module.algebraMap_end_apply])
  have hv0 : ∀ p : ℂ[X], aeval φ p v = 0 → p = 0 := by
    intro p hpv
    by_contra hp
    rcases LinearMap.injective_or_eq_zero (aeval φ p) with hinj | h0
    · exact hv (hinj (by rw [hpv, map_zero]))
    · exact htr p hp h0
  have hsurj : ∀ a : ℂ, Function.Surjective (aeval φ (X - C a)) := by
    intro a
    rcases LinearMap.bijective_or_eq_zero (aeval φ (X - C a)) with hb | h0
    · exact hb.2
    · exact absurd h0 (htr _ (Polynomial.X_sub_C_ne_zero a))
  choose w hw using fun a => hsurj a v
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have key : ∀ k ∈ s, aeval φ (∏ j ∈ s, (X - C j)) (w k) = aeval φ (∏ j ∈ s.erase k, (X - C j)) v := by
      intro k hk
      rw [← Finset.prod_erase_mul _ _ hk, map_mul, Module.End.mul_apply, hw]
    have h3 := congrArg (aeval φ (∏ j ∈ s, (X - C j))) hg
    rw [map_sum, map_zero] at h3
    simp only [LinearMap.map_smul_of_tower] at h3
    rw [Finset.sum_congr rfl (fun k hk => by rw [key k hk])] at h3
    have h4 : aeval φ (∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j)) v = 0 := by
      rw [← h3, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hP := hv0 _ h4
    have h5 := congrArg (Polynomial.eval i) hP
    have hz : ∀ k ∈ s.erase i, Polynomial.eval i (C (g k) * ∏ j ∈ s.erase k, (X - C j)) = 0 := by
      intro k hk
      have hki := Finset.ne_of_mem_erase hk
      have him : i ∈ s.erase k := Finset.mem_erase_of_ne_of_mem (Ne.symm hki) hi
      rw [Polynomial.eval_mul, Polynomial.eval_prod, Finset.prod_eq_zero him (by simp), mul_zero]
    rw [Polynomial.eval_finsetSum, ← Finset.sum_erase_add _ _ hi, Finset.sum_eq_zero hz, zero_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_zero] at h5
    have hne2 : ∏ j ∈ s.erase i, Polynomial.eval i (X - C j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hj).symm
    exact (mul_eq_zero.mp h5).resolve_right hne2
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at hc
  exact absurd (hc.trans hV) (not_le.mpr Cardinal.aleph0_lt_continuum)
end GlobalTheory.ThK.Dbl.Dens
