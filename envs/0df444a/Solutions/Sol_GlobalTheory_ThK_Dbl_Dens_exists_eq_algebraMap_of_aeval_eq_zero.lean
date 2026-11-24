-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Dens.exists_eq_algebraMap_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:42.024241+00:00
-- url     : https://prove2.me/submissions/3ea46456-c9b4-4ef0-9654-c06ba9197c57

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD

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
theorem _root_.solution (φ : Module.End R V) {p : ℂ[X]} (hp : p ≠ 0)
    (hφ : aeval φ p = 0) : ∃ c : ℂ, φ = algebraMap ℂ (Module.End R V) c := by
  induction hn : p.natDegree generalizing p with
  | zero =>
    exfalso
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨c, rfl⟩ := hn
    have hc : c ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hnt : Nontrivial V := IsSimpleModule.nontrivial R V
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rw [aeval_C] at hφ
    have h3 := LinearMap.congr_fun hφ v
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply] at h3
    exact hv ((smul_eq_zero.mp h3).resolve_left hc)
  | succ n ih =>
    have hdeg : p.degree ≠ 0 := by
      intro h
      rw [Polynomial.degree_eq_natDegree hp] at h
      norm_cast at h
      omega
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
    have hpq : p = (X - C a) * (p /ₘ (X - C a)) := (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm
    have hq0 : p /ₘ (X - C a) ≠ 0 := by
      intro h
      apply hp
      rw [hpq, h, mul_zero]
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      have h3 := congrArg Polynomial.natDegree hpq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0, Polynomial.natDegree_X_sub_C] at h3
      omega
    rw [hpq, map_mul, map_sub, aeval_X, aeval_C] at hφ
    rcases LinearMap.injective_or_eq_zero (φ - algebraMap ℂ (Module.End R V) a) with hinj | h0
    · apply ih hq0 _ hqdeg
      ext v
      apply hinj
      rw [LinearMap.zero_apply, map_zero]
      exact LinearMap.congr_fun hφ v
    · exact ⟨a, sub_eq_zero.mp h0⟩
end GlobalTheory.ThK.Dbl.Dens
