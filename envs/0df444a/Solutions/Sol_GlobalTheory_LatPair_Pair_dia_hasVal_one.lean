-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.dia_hasVal_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:02.865855+00:00
-- url     : https://prove2.me/submissions/b5a6884f-a0af-4b70-b0ea-eb9137b2ee49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
open GlobalTheory.LatPair.Pair
namespace GlobalTheory.LatPair.Pair
theorem _root_.solution {c : 𝓀[k]ˣ} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) {s : 𝒪[k]}
    (hs : residue 𝒪[k] s = (c⁻¹ : 𝓀[k]ˣ)) : (c • P).HasVal (s • e) 1 := by
  rw [dia_hasVal, ← hs]
  exact he.smul s
end GlobalTheory.LatPair.Pair
