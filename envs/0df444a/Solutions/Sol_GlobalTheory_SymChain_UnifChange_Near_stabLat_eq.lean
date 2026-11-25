-- Prove2me | solution 1 for GlobalTheory.SymChain.UnifChange.Near.stabLat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:24.936259+00:00
-- url     : https://prove2.me/submissions/ee810ab8-a087-49e7-8d6b-267a52fd5c72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSymDataOfUnifCongr
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_mem_stabLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.SymChain.UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.SymChain.UnifChange
namespace Near
theorem _root_.solution {F G : LatFrame k ι Y} (h : Near F G) : stabLat G.bas = stabLat F.bas := by
  ext g
  have hd := KOne_le_KO h.2
  have e : G.bas⁻¹ * g * G.bas = (F.bas⁻¹ * G.bas)⁻¹ * (F.bas⁻¹ * g * F.bas) * (F.bas⁻¹ * G.bas) := by group
  rw [mem_stabLat, mem_stabLat, e, (KO k Y).mul_mem_cancel_right hd, (KO k Y).mul_mem_cancel_left (inv_mem hd)]
end Near
end GlobalTheory.SymChain.UnifChange
