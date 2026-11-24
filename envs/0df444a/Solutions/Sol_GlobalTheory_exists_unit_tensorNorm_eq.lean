-- Prove2me | solution 1 for GlobalTheory.exists_unit_tensorNorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:29.661913+00:00
-- url     : https://prove2.me/submissions/099d263a-c4a6-4d77-aa14-f9c84dcc9d93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_exists_unit_smul_eq_of_bijective_toSpanSingleton
import Theorems.Thm_GlobalTheory_tensorNorm_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
variable [SMulDistribClass G A M]
variable {A}
namespace GlobalTheory
theorem _root_.solution [Finite G] (κ : ι ≃ G) {e e' : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e))
    (he' : Function.Bijective (LinearMap.toSpanSingleton A M e')) :
    ∃ u : (FixedPoints.subring A G)ˣ,
      tensorNorm A κ e' = ((u : FixedPoints.subring A G) : A) • tensorNorm A κ e := by
  cases nonempty_fintype G
  obtain ⟨h, rfl⟩ := exists_unit_smul_eq_of_bijective_toSpanSingleton he he'
  refine ⟨Units.mkOfMulEqOne ⟨∏ g : G, g • (h : A), Finset.smul_prod_perm _⟩
    ⟨∏ g : G, g • (↑h⁻¹ : A), Finset.smul_prod_perm _⟩ (Subtype.ext ?_), tensorNorm_smul A κ _ _⟩
  change (∏ g : G, g • (h : A)) * ∏ g : G, g • (↑h⁻¹ : A) = 1
  simp [← Finset.prod_mul_distrib, ← smul_mul']
end GlobalTheory
