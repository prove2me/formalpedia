-- Prove2me | solution 1 for GlobalTheory.MassFibre.wt_out_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:16:43.945865+00:00
-- url     : https://prove2.me/submissions/7a71fabc-a75a-49d7-8034-811f80846e9f

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
import Theorems.Thm_GlobalTheory_MassFibre_wt_of_mem_orbit

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
theorem _root_.solution {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) :
    wt Γ (Quotient.out (Quotient.mk (MulAction.orbitRel Γ Y) y : MulAction.orbitRel.Quotient Γ Y)) = wt Γ y :=
  wt_of_mem_orbit Γ (Quotient.mk_out (s := MulAction.orbitRel Γ Y) y)
end GlobalTheory.MassFibre
