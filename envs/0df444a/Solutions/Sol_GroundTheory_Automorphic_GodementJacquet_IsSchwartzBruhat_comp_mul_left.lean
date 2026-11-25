-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.IsSchwartzBruhat.comp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:33:28.051612+00:00
-- url     : https://prove2.me/submissions/b60db8f2-67ea-42d8-91f7-359f3140ab97

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
namespace IsSchwartzBruhat
theorem _root_.solution {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (a : GL (Fin n) F) : IsSchwartzBruhat fun X => Φ ((a : Matrix (Fin n) (Fin n) F) * X) := by
  let e : Matrix (Fin n) (Fin n) F ≃ₜ Matrix (Fin n) (Fin n) F :=
    { toFun := fun X => (a : Matrix (Fin n) (Fin n) F) * X
      invFun := fun X => ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X
      left_inv := fun X => Units.inv_mul_cancel_left a X
      right_inv := fun X => Units.mul_inv_cancel_left a X
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  exact ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
end IsSchwartzBruhat
end GroundTheory.Automorphic.GodementJacquet
