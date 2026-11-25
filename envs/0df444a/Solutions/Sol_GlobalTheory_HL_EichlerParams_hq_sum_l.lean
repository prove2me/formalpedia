-- Prove2me | solution 1 for GlobalTheory.HL.EichlerParams.hq_sum_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:47.046916+00:00
-- url     : https://prove2.me/submissions/6c6a07ac-c36b-4804-81d2-0022bc5e8ac9

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.EichlerParams
theorem _root_.solution {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E) {ι : Type} (s : Finset ι) (f : ι → Fin N → E)
    (y : Fin N → E) : hq sig Hm (∑ a ∈ s, f a) y = ∑ a ∈ s, hq sig Hm (f a) y := by
  induction s using Finset.induction_on with
  | empty => simp [hq]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hq_add_l, ih]
end GlobalTheory.HL.EichlerParams
