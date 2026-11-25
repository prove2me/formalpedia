-- Prove2me | solution 1 for GlobalTheory.HL.EichlerParams.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:57.45208+00:00
-- url     : https://prove2.me/submissions/efc4ffd8-d020-48d0-8dcc-6ea3028e1cce

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
import Theorems.Thm_GlobalTheory_SmulIntegralDenominator_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {ι : Type} [Fintype ι] (f : ι → R) : ∃ e ∈ 𝒪[K], e ≠ 0 ∧ ∀ i, Sm L e⁻¹ (f i) := by
  first
  | exact @_root_.GlobalTheory.SmulIntegralDenominator.main
  | exact _root_.GlobalTheory.SmulIntegralDenominator.main
  | (apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulIntegralDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulIntegralDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulIntegralDenominator.main ..)
end GlobalTheory.HL.EichlerParams
