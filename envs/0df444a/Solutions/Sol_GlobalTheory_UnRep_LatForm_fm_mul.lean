-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.fm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:58:12.913682+00:00
-- url     : https://prove2.me/submissions/da48d51c-7a5e-4d1d-b731-e2aab7684cc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) E) : fm F (A * B) = fm F A * fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)
end GlobalTheory.UnRep.LatForm
