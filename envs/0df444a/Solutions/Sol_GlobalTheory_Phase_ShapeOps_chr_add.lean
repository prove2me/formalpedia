-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.chr_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:13.540868+00:00
-- url     : https://prove2.me/submissions/942d5bcb-fa41-461c-abb1-3dfe66dd4120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu

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
theorem _root_.solution (y x x' : Matrix κ ι ℚ) : chr y (x + x') = chr y x * chr y x' := by
  unfold chr
  rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_dotProduct]; rfl
end GlobalTheory.Phase.ShapeOps
