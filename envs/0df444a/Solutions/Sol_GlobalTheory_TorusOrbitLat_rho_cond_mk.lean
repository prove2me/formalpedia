-- Prove2me | solution 1 for GlobalTheory.TorusOrbitLat.rho_cond_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:41.971337+00:00
-- url     : https://prove2.me/submissions/0be3dbac-0bdc-433c-ade4-7f44ca8159a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusOrbitLatticeCountBoundedByRho
import Theorems.Thm_GlobalTheory_TorusOrbitLat_isIntegral_inv_mul_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.TorusOrbitLat
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.TorusOrbitLat
theorem _root_.solution (t : B.T) (w : B.A) :
    IsIntegral K.O (((((Quotient.out (QuotientGroup.mk t : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T) : B.T) :
      B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) ↔ IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((intUnits K.O B.A).subgroupOf B.T) t
  rw [hh, Subgroup.coe_mul]
  exact isIntegral_inv_mul_iff _ _ (Subgroup.mem_subgroupOf.mp h.2) w
end GlobalTheory.TorusOrbitLat
