-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.one_tmul_natCast_mul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:54.464176+00:00
-- url     : https://prove2.me/submissions/c2db2afe-3238-4b28-b2cd-3d7210b35d53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
import Theorems.Thm_GlobalTheory_UnRep_LatForm_one_tmul_natCast_smul

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
theorem _root_.solution (m : ℕ) (s : 𝓞 E) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((((m : 𝓞 E) * s : 𝓞 E)) : E)) • z =
      m • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z := by
  rw [← one_tmul_natCast_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl
end GlobalTheory.UnRep.LatForm
