-- Prove2me | solution 1 for GlobalTheory.HL.EichlerParams.hq_piQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:31:52.7704+00:00
-- url     : https://prove2.me/submissions/e7446ec2-3a2f-4f4d-954f-807fe6398076

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
import Theorems.Thm_GlobalTheory_HL_EichlerParams_hq_sub_l
import Theorems.Thm_GlobalTheory_HL_EichlerParams_hq_sum_l
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
theorem _root_.solution {N r : ℕ} (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E)
    (T : Finset (Fin r)) (w z : Fin N → E) :
    hq sig Hm (piQ sig Hm X Y T w) z = hq sig Hm w z -
      ∑ a ∈ T, (hq sig Hm w (Y a) * hq sig Hm (X a) z + hq sig Hm w (X a) * hq sig Hm (Y a) z) := by
  have e : piQ sig Hm X Y T w = w - ∑ a ∈ T, (hq sig Hm w (Y a) • X a + hq sig Hm w (X a) • Y a) := by
    funext j; simp [piQ, Finset.sum_apply]
  rw [e, hq_sub_l, hq_sum_l]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hq_add_l, hq_smul_l, hq_smul_l]
end GlobalTheory.HL.EichlerParams
