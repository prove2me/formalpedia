-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.intM_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:25:56.053341+00:00
-- url     : https://prove2.me/submissions/ef1aae0f-db49-44a5-a29c-c2acb8709324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_IsMu_mul
import Theorems.Thm_GlobalTheory_Phase_Ph_mul


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
theorem _root_.solution (N : ℕ) {z : Matrix κ ι ℚ} (hz : IntM z) : IntM ((N : ℚ) • z) := fun k i => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_algebraMap (R := ℤ) (x := (N : ℤ)) |>.mul (hz k i) : IsIntegral ℤ (_ * _))
end GlobalTheory.Phase.ShapeOps
