-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.HasCentralChar.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:13.250915+00:00
-- url     : https://prove2.me/submissions/d5a7e2fe-23e1-4fab-b164-a6343d4a0a0b

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
theorem _root_.solution (h : HasCentralChar ρ ω) {u : U} (hu : u ≠ 0) : ω 1 = 1 := by
  have h1 : ω 1 • u = (1 : ℂ) • u := by
    rw [one_smul, ← h 1 (Subgroup.one_mem _) u, map_one, Module.End.one_apply]
  exact smul_left_injective ℂ hu h1
end HasCentralChar
end GroundTheory.Automorphic.Parabolic
