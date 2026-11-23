-- Prove2me | solution 1 for GlobalTheory.SiegelAction.qm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:32.81581+00:00
-- url     : https://prove2.me/submissions/d9c8a02a-92c2-46f8-877c-b381659a0700

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution {α β γ : Type} [Fintype β] (A : Matrix α β ℚ) (B : Matrix β γ ℚ) :
    qm (A * B) = qm A * qm B := by
  ext i j; simp [qm, Matrix.mul_apply]
end GlobalTheory.SiegelAction
