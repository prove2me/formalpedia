-- Prove2me | solution 1 for GlobalTheory.UnRep.SplitRep.mix_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:03.306917+00:00
-- url     : https://prove2.me/submissions/caee878c-e645-400f-bd40-82b8a5310385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
namespace GlobalTheory.UnRep.SplitRep
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (κ : GL (Fin n) R) :
    ((mix ε hε κ)⁻¹).1 = ε • (κ⁻¹).1 + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := rfl
end GlobalTheory.UnRep.SplitRep
