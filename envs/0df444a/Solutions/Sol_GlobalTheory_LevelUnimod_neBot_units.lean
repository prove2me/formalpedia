-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.neBot_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:25.856107+00:00
-- url     : https://prove2.me/submissions/74c81be0-16a8-45ee-a322-0b338bdd03dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_neBot_punctured

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution : (Filter.comap (Units.val : kˣ → k) (𝓝 0)).NeBot := by
  haveI := neBot_punctured (k := k)
  refine Filter.comap_neBot fun U hU => ?_
  obtain ⟨x, hx, hx0⟩ := Filter.nonempty_of_mem (inter_mem_nhdsWithin ({0}ᶜ : Set k) hU)
  exact ⟨Units.mk0 x hx, hx0⟩
end GlobalTheory.LevelUnimod
