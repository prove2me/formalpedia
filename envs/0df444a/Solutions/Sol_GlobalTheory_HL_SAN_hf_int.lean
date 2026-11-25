-- Prove2me | solution 1 for GlobalTheory.HL.SAN.hf_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:02.33863+00:00
-- url     : https://prove2.me/submissions/5fa25e7c-9f1c-41cc-8852-474bc8b9f00e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem


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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN
namespace GlobalTheory.HL.SAN
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x y : Fin N → E} (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    hf L Hm x y ∈ L.O :=
  L.O.sum_mem fun i _ => L.O.sum_mem fun j _ =>
    L.O.mul_mem (L.O.mul_mem (hx i) (hI i j)) (GlobalTheory.UnramOrder.cj_mem L (hy j))
end GlobalTheory.HL.SAN
