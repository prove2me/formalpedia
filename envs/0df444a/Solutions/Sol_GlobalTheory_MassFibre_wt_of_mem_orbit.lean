-- Prove2me | solution 1 for GlobalTheory.MassFibre.wt_of_mem_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:39.279741+00:00
-- url     : https://prove2.me/submissions/77f070a8-487e-47f2-a412-f137f42abc55

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
import Theorems.Thm_GlobalTheory_MassFibre_wt_smul

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
open GlobalTheory GlobalTheory.MassFibre
open MulAction
namespace GlobalTheory.MassFibre
theorem _root_.solution {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y]
    {y y' : Y} (h : y' ∈ MulAction.orbit Γ y) : wt Γ y' = wt Γ y := by
  obtain ⟨γ, rfl⟩ := h
  show wt Γ (γ • y) = wt Γ y
  rw [Subgroup.smul_def]
  exact wt_smul Γ γ γ.2 y
end GlobalTheory.MassFibre
