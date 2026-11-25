-- Prove2me | solution 1 for GlobalTheory.HL.Defect.vE_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:31:26.132463+00:00
-- url     : https://prove2.me/submissions/32bbaeda-c01c-4243-9d09-b0e56b4b2354

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Defect
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (m : ℕ) (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ m * ((u : 𝒪[F]) : F))) = m := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ∀ u : (𝒪[F])ˣ, ((u : 𝒪[F]) : F) ≠ 0 := fun u h => u.ne_zero (Subtype.ext h)
  induction m with
  | zero =>
    have e1 := h1 1 1 one_ne_zero one_ne_zero
    have e2 := h1 _ _ (hu0 u) (hu0 u⁻¹)
    have e3 := (h3 _ (hu0 u)).2 (Subtype.property _)
    have e4 := (h3 _ (hu0 u⁻¹)).2 (Subtype.property _)
    rw [← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one] at e2
    rw [mul_one] at e1
    rw [pow_zero, one_mul]
    omega
  | succ m ih =>
    rw [pow_succ', mul_assoc, h1 _ _ hϖ0 (mul_ne_zero (pow_ne_zero _ hϖ0) (hu0 u)), h2, ih]
    push_cast; ring
end GlobalTheory.HL.Defect
