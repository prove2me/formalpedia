-- Prove2me | solution 1 for GlobalTheory.PosSemidefShiftByScalar.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:48.004905+00:00
-- url     : https://prove2.me/submissions/9fd2e6a8-2b08-4e07-b986-f5390a89e07d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Theorems.Thm_GlobalTheory_PosSemidefShiftByScalar_exists_pos_mem_HnGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Unitary
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosSemidefShiftByScalar
namespace GlobalTheory.PosSemidefShiftByScalar
theorem _root_.solution : ∀ {N : ℕ} {E : Type} [inst : Field E] (Ψ : Finset (E →+* ℂ)) {Z : GlobalTheory.SW.CM Ψ N N},
    Z ∈ GlobalTheory.SW.Hn Ψ N → ∃ (δ : ℝ), (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ :=
  fun Ψ _ hZ => exists_pos_mem_HnGe Ψ hZ
end GlobalTheory.PosSemidefShiftByScalar
