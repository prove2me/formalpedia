-- Prove2me | solution 1 for GlobalTheory.LevDesc.mem_spanQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:41:28.982567+00:00
-- url     : https://prove2.me/submissions/5a180ce3-a7fe-4340-b0a1-22b70c1344a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R O : Type} [Group G] [Field K] [CommRing R] [Algebra K R] [CommRing O] [Algebra O K]
  {C : Submodule K R} [Module O C] [IsScalarTower O K C]
omit [Algebra O K] [IsScalarTower O K C]
namespace GlobalTheory.LevDesc
theorem _root_.solution {N : Submodule O C} {F : C} (hF : F ∈ N) : (F : R) ∈ spanQ N :=
  ⟨F, Submodule.subset_span hF, rfl⟩
end GlobalTheory.LevDesc
