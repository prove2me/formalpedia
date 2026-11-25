-- Prove2me | solution 1 for GlobalTheory.HL.EichlerParams.hf_add_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:44.698317+00:00
-- url     : https://prove2.me/submissions/4fff6d82-8c13-4e08-bbe5-fa7f269b207a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianSymplecticBasisLocalExtension
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerParams
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable (L : LocE K R)
namespace GlobalTheory.HL.EichlerParams
theorem _root_.solution {N : ℕ} (Hm : Matrix (Fin N) (Fin N) R) (a b y : Fin N → R) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]
end GlobalTheory.HL.EichlerParams
