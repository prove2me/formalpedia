-- Prove2me | solution 1 for GroundTheory.PAdicHodge.minpoly_eq_cyclotomic_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:55.741907+00:00
-- url     : https://prove2.me/submissions/d917c7bb-280b-447d-a3c7-71bc218800fe

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_totient
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_natDegree_minpoly
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_eq_zpow_of_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_zpow_p_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ζ : PadicAlgCl p} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    minpoly ℚ_[p] ζ = cyclotomic (p ^ (k + 1)) ℚ_[p] := by
  have hpos : 0 < p ^ (k + 1) := pow_pos (Fact.out : p.Prime).pos _
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  have hdvd : minpoly ℚ_[p] ζ ∣ cyclotomic (p ^ (k + 1)) ℚ_[p] := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  set d := (minpoly ℚ_[p] ζ).natDegree with hd
  have hφ : 0 < Nat.totient (p ^ (k + 1)) := Nat.totient_pos.2 hpos
  have hd0 : 0 < d := minpoly.natDegree_pos hint

  have hπdeg : (minpoly ℚ_[p] (ζ - 1)).natDegree = d := by
    have : ζ - 1 = ζ - algebraMap ℚ_[p] (PadicAlgCl p) 1 := by rw [map_one]
    rw [this, minpoly.sub_algebraMap, natDegree_comp, natDegree_X_add_C, mul_one]
  have hπ0 : ζ - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := hζ.pow_ne_one_of_pos_of_lt one_ne_zero (Nat.one_lt_pow (Nat.succ_ne_zero k)
      (Fact.out : p.Prime).one_lt)
    exact this (by rw [pow_one, h])
  have hc0 : (minpoly ℚ_[p] (ζ - 1)).coeff 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral _) hπ0
  obtain ⟨z, hz⟩ := exists_norm_eq_zpow_of_ne_zero hc0
  have e1 := norm_pow_natDegree_minpoly (ζ - 1)
  rw [hπdeg, hz] at e1
  have e2 := norm_sub_one_pow_totient hζ

  have key : (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1))) = (p : ℝ) ^ (-(d : ℤ)) := by
    calc (p : ℝ) ^ (z * Nat.totient (p ^ (k + 1)))
        = ((p : ℝ) ^ z) ^ Nat.totient (p ^ (k + 1)) := by rw [zpow_mul, zpow_natCast]
      _ = (‖ζ - 1‖ ^ d) ^ Nat.totient (p ^ (k + 1)) := by rw [e1]
      _ = (‖ζ - 1‖ ^ Nat.totient (p ^ (k + 1))) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((p : ℝ)⁻¹) ^ d := by rw [e2]
      _ = (p : ℝ) ^ (-(d : ℤ)) := by rw [zpow_neg, zpow_natCast, inv_pow]
  have key' := zpow_p_injective (p := p) key
  have hdvdφ : Nat.totient (p ^ (k + 1)) ∣ d := by
    have : ((Nat.totient (p ^ (k + 1)) : ℕ) : ℤ) ∣ (d : ℤ) :=
      ⟨-z, by linear_combination key'⟩
    exact Int.natCast_dvd_natCast.1 this
  have hle1 : Nat.totient (p ^ (k + 1)) ≤ d := Nat.le_of_dvd hd0 hdvdφ
  have hle2 : d ≤ Nat.totient (p ^ (k + 1)) := by
    rw [← natDegree_cyclotomic (p ^ (k + 1)) ℚ_[p]]
    exact natDegree_le_of_dvd hdvd (cyclotomic_ne_zero _ _)
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _) hdvd
    (by rw [natDegree_cyclotomic]; omega)).symm
end GroundTheory.PAdicHodge
