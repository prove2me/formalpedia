-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.shape_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:02:14.330246+00:00
-- url     : https://prove2.me/submissions/b4d8aa55-e838-47e7-b2b7-c9baadfd8d84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_ph_conj
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_conj
import Theorems.Thm_GlobalTheory_SW_isSB_algebra_haar_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) : Shape (fun x => conj (φ x)) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ φ hs hs).2.2.2.1, conj c, a, S, _, ph_conj hc, quad_conj hf,
    fun x => ?_⟩
  simp only [hφ x]
  split_ifs <;> simp
end GlobalTheory.Phase.ShapeOps
