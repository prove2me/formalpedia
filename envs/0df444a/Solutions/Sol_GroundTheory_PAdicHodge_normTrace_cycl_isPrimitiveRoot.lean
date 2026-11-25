-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_cycl_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:54.59192+00:00
-- url     : https://prove2.me/submissions/62d68ced-f115-4fc6-a1e7-fa3693432bb0

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_natDegree_minpoly_cycl_of_adjoin_eq
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_eq_adjoin
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_pow_eq_one_mem_cycl
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) : normTrace (cycl p k) η = 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hint : IsIntegral (cycl p k) η :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) η).tower_top
  have hdeg := natDegree_minpoly_cycl_of_adjoin_eq hk (cycl_eq_adjoin hη).symm
  have hc : η ^ p ∈ cycl p k := pow_eq_one_mem_cycl (by rw [← pow_mul, ← pow_succ']; exact hη.pow_eq_one)
  set f : (cycl p k)[X] := X ^ p - C ⟨η ^ p, hc⟩ with hf
  have hfm : f.Monic := monic_X_pow_sub_C _ (by omega)
  have hfdeg : f.natDegree = p := natDegree_X_pow_sub_C
  have hroot : aeval η f = 0 := by simp [hf]
  have hdvd : minpoly (cycl p k) η ∣ f := minpoly.dvd _ _ hroot
  have heq : f = minpoly (cycl p k) η :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hfm hdvd (by rw [hfdeg, hdeg])
  have hnext : f.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hfdeg, hf, coeff_sub, coeff_X_pow, coeff_C]
    simp only [if_neg (show p - 1 ≠ p by omega), if_neg (show p - 1 ≠ 0 by omega), sub_zero]
  rw [normTrace, normTraceF, ← heq, hnext]
  simp
end GroundTheory.PAdicHodge
