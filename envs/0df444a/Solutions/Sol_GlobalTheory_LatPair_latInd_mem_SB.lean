-- Prove2me | solution 1 for GlobalTheory.LatPair.latInd_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:06.995821+00:00
-- url     : https://prove2.me/submissions/f874fb4d-667a-4daa-9f34-3995c253c329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Theorems.Thm_GlobalTheory_LatPair_ite_mem_SB
import Theorems.Thm_GlobalTheory_LatPair_isClopen_isCompact_maps

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
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']
namespace GlobalTheory.LatPair
theorem _root_.solution (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k] [L.IsLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_maps S L).1 (isClopen_isCompact_maps S L).2
end GlobalTheory.LatPair
