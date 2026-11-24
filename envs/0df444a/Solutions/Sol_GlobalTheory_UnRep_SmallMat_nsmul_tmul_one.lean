-- Prove2me | solution 1 for GlobalTheory.UnRep.SmallMat.nsmul_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:24:57.533923+00:00
-- url     : https://prove2.me/submissions/581cc2c3-379c-46e8-8933-b39df27923e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.SmallMat
theorem _root_.solution (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    ((d • a) ⊗ₜ[F] (1 : E) : RA F E) = d • (a ⊗ₜ[F] (1 : E) : RA F E) := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]
end GlobalTheory.UnRep.SmallMat
