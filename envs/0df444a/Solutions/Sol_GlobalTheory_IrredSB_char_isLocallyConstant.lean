-- Prove2me | solution 1 for GlobalTheory.IrredSB.char_isLocallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:40.143794+00:00
-- url     : https://prove2.me/submissions/e1a49d51-4621-40df-82ec-79dd213d9e71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_IrredSB_char_eventually_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IrredSB
theorem _root_.solution (ψk : AddChar k Circle) (hψ : Continuous ψk) : IsLocallyConstant ψk := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ht : Filter.Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
    have : Continuous (fun y : k => y - x) := by fun_prop
    simpa using this.tendsto x
  filter_upwards [ht.eventually (char_eventually_one ψk hψ)] with y hy
  have : ψk y = ψk x * ψk (y - x) := by rw [← AddChar.map_add_eq_mul, add_sub_cancel]
  rw [this, hy, mul_one]
end GlobalTheory.IrredSB
