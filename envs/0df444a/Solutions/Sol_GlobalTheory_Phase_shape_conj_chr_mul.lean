-- Prove2me | solution 1 for GlobalTheory.Phase.shape_conj_chr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:07.348417+00:00
-- url     : https://prove2.me/submissions/50871097-e0a3-4b93-bfea-6038b9a835a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_shape_conj
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_shape_chr
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_shape_mul

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
namespace GlobalTheory.Phase
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) :=
  fun _ _ _ _ _ _ h => ⟨ShapeOps.shape_conj h, ShapeOps.shape_chr h, fun _ h' => ShapeOps.shape_mul h h'⟩
end GlobalTheory.Phase
