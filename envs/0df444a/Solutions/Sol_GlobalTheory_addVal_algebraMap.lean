-- Prove2me | solution 1 for GlobalTheory.addVal_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:21.888062+00:00
-- url     : https://prove2.me/submissions/08793148-5d73-4539-98fd-02b3b834d526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthBaseChangeQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ramificationIdx_maximalIdeal_pos
import Theorems.Thm_GlobalTheory_addVal_algebraMap_uniformizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsDiscreteValuationRing hiding maximalIdeal
variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]
variable [IsLocalHom (algebraMap R S)]
variable {R}
namespace GlobalTheory
theorem _root_.solution (x : R) :
    addVal S (algebraMap R S x) = addVal R x * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.top_mul]
    exact_mod_cast (ramificationIdx_maximalIdeal_pos R S).ne'
  · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
    rw [addVal_def' u hϖ, map_mul, map_pow, addVal_mul, addVal_pow,
      addVal_algebraMap_uniformizer S hϖ,
      addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S)), zero_add, nsmul_eq_mul]
end GlobalTheory
