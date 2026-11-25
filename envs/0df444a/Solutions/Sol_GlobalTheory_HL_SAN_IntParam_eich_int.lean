-- Prove2me | solution 1 for GlobalTheory.HL.SAN.IntParam.eich_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:23.959164+00:00
-- url     : https://prove2.me/submissions/6b28ee67-2b9f-4a89-a739-672e9c2ff098

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductParamsIntegral
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_SAN_hf_int
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN GlobalTheory.HL.SAN.IntParam
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SAN.IntParam
theorem _root_.solution (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x u v : Fin N → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) (hv : ∀ j, v j ∈ L.O) (j : Fin N) :
    eich L Hm x u s v j ∈ L.O := by
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact L.O.sub_mem (L.O.add_mem (hv j) (L.O.mul_mem (hf_int L hI hv hu) (hx j)))
    (L.O.mul_mem (hf_int L hI hv hx) (L.O.add_mem (hu j) (L.O.mul_mem hs (hx j))))
end GlobalTheory.HL.SAN.IntParam
