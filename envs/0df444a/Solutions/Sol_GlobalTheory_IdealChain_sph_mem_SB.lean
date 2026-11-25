-- Prove2me | solution 1 for GlobalTheory.IdealChain.sph_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:41.38213+00:00
-- url     : https://prove2.me/submissions/e40d5c4a-72fd-49e9-b599-7a38e78f1b70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_LatPair_latInd_mem_SB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
omit [DecidableEq ι] [DecidableEq ι']
namespace GlobalTheory.IdealChain
theorem _root_.solution (α : kˣ) {L' : Submodule 𝒪[k] (ι' → k)} {L : Submodule 𝒪[k] (ι → k)} (h' : L'.IsLattice k)
    (h : L.IsLattice k) : sph α L' L ∈ SB (Matrix ι ι' k) := by
  classical
  have : sph α L' L = latInd L' (α • L) := by
    funext x
    rw [sph, latInd]
    refine if_congr (forall₂_congr fun v _ => ?_) rfl rfl
    refine Iff.trans ?_ (Submodule.mem_smul_pointwise_iff_exists _ α L).symm
    exact exists_congr fun w => and_congr_right' eq_comm
  rw [this]
  exact latInd_mem_SB _ _
end GlobalTheory.IdealChain
