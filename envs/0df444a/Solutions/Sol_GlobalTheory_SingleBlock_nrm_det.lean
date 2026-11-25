-- Prove2me | solution 1 for GlobalTheory.SingleBlock.nrm_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:06.674813+00:00
-- url     : https://prove2.me/submissions/ef379611-359c-483a-8159-36e8a34b642d

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_det_mem_of_mem_glInt
import Theorems.Thm_GlobalTheory_SingleBlock_det_inv_mem_of_mem_glInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution {nrm : AbsoluteValue F ℝ} (hn : IsNormalisedAbs nrm) {n : Type} [Fintype n]
    [DecidableEq n] {g : GL n F} (hg : g ∈ glInt 𝒪[F] n) :
    nrm ((GeneralLinearGroup.det g : Fˣ) : F) = 1 := by
  have h1 := (hn.1 _).2 (det_mem_of_mem_glInt hg)
  have h2 := (hn.1 _).2 (det_inv_mem_of_mem_glInt hg)
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  exact le_antisymm h1 ((inv_le_one₀ (nrm.pos (Units.ne_zero _))).1 h2)
end GlobalTheory.SingleBlock
