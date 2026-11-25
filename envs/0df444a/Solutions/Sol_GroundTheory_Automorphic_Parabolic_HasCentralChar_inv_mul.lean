-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.HasCentralChar.inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:59.383794+00:00
-- url     : https://prove2.me/submissions/b8befaf2-67a1-4dba-90dc-15348fac56b1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_mul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_HasCentralChar_one

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
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {U : Type*} [AddCommGroup U] [Module ℂ U]
variable {ρ : Representation ℂ (GL (Fin n) F) U} {ω : GL (Fin n) F → ℂ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
namespace HasCentralChar
theorem _root_.solution (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0)
    {z : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F)) : ω z⁻¹ * ω z = 1 := by
  rw [← h.mul hu (inv_mem hz) hz, inv_mul_cancel, h.one hu]
end HasCentralChar
end GroundTheory.Automorphic.Parabolic
