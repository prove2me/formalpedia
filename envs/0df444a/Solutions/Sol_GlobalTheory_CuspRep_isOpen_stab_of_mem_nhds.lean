-- Prove2me | solution 1 for GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:20.895803+00:00
-- url     : https://prove2.me/submissions/df7c7198-4b77-4dbc-b4a6-3b8b73543c2b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsOpenStabilizer
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_IsOpenStabOfMemNhds
import Theorems.Thm_UpperTheory_Reformulated_B_IsOpenStabilizer_isOpen_stab_of_mem_nhds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CuspRep
namespace GlobalTheory.CuspRep
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (v : V)
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsOpen {g : G | ρ g v = v} :=
  UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds ρ v h
end GlobalTheory.CuspRep
