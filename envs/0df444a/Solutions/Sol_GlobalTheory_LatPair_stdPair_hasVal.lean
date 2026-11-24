-- Prove2me | solution 1 for GlobalTheory.LatPair.stdPair_hasVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:02.947425+00:00
-- url     : https://prove2.me/submissions/32fa0335-430e-4b7c-96ec-546b060aaec7

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
variable [Fintype n]
namespace GlobalTheory.LatPair
theorem _root_.solution {i : n} {x : n → k} {a : 𝓀[k]} :
    (stdPair k i).HasVal x a ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], residue 𝒪[k] ⟨x i, h i⟩ = a :=
  ⟨fun ⟨h, h'⟩ => ⟨mem_stdLat.1 h, h'⟩, fun ⟨h, h'⟩ => ⟨mem_stdLat.2 h, h'⟩⟩
end GlobalTheory.LatPair
