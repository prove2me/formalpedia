-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.shape_chr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:55:16.87698+00:00
-- url     : https://prove2.me/submissions/64db859f-144a-4ca2-b07b-c56878af557c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_mul
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_affine
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_chr_add
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_exp
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_isSB_mul_chr

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
theorem _root_.solution {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (y : Matrix κ ι ℚ) :
    Shape (fun x => φ x * chr y x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  have hq : Quad S (fun x => chr y (x + a)) := by
    refine quad_affine (fun x _ => mu_exp _) fun x _ x' _ => ?_
    simp only [← chr_add]
    congr 1; abel
  refine ⟨isSB_mul_chr hs y, c, a, S, _, hc, quad_mul hf hq, fun x => ?_⟩
  simp only [hφ x, sub_add_cancel]
  split_ifs <;> simp [mul_assoc]
end GlobalTheory.Phase.ShapeOps
