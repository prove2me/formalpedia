-- Prove2me | solution 1 for GlobalTheory.HL.StTri.hf_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:54:13.407735+00:00
-- url     : https://prove2.me/submissions/1de46e43-64bf-44cd-95c7-0fad17bfadc7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalFrameStabilizerActsUnitriangular
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StTri
namespace GlobalTheory.HL.StTri
theorem _root_.solution {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hf L Hm x (c • y) = L.cj c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.HL.StTri
