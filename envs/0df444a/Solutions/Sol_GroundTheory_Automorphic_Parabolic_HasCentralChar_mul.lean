-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.HasCentralChar.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:34.101348+00:00
-- url     : https://prove2.me/submissions/47a35fe3-3e42-4859-915c-920d14ea099b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff

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
    {z z' : GL (Fin n) F} (hz : z ∈ Subgroup.center (GL (Fin n) F))
    (hz' : z' ∈ Subgroup.center (GL (Fin n) F)) : ω (z * z') = ω z * ω z' := by
  have h1 := h _ (mul_mem hz hz') u
  rw [map_mul, Module.End.mul_apply, h z' hz', map_smul, h z hz, smul_smul] at h1
  exact (smul_left_injective ℂ hu h1).symm.trans (mul_comm _ _)
end HasCentralChar
end GroundTheory.Automorphic.Parabolic
