-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.one_tmul_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:58:13.786299+00:00
-- url     : https://prove2.me/submissions/273b1ac2-1c22-4d4a-8f4c-ccdd66857c52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
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
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution (m : ℕ) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) • z = m • z := by
  have : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) = (m : RA F E) := by
    have h : (((m : 𝓞 E)) : E) = (m : E) := by simp
    rw [h]
    exact map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) m
  rw [this, Nat.cast_smul_eq_nsmul]
end GlobalTheory.UnRep.LatForm
