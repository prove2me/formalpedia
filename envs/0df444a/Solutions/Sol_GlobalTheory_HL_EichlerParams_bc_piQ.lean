-- Prove2me | solution 1 for GlobalTheory.HL.EichlerParams.bc_piQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:44.658519+00:00
-- url     : https://prove2.me/submissions/bf5bf257-cebf-4343-b9eb-736ce7091cf6

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
import Theorems.Thm_GlobalTheory_HL_RatExt_rational_extend
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
theorem _root_.solution (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N r : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (X Y : Fin r → Fin N → E) (T : Finset (Fin r)) (w : Fin N → E) :
    A.bc p (piQ sig Hm X Y T w) = piL (A.L p) (Hm.map (A.loc p).ιE) (fun a => A.bc p (X a))
      (fun a => A.bc p (Y a)) T (A.bc p w) := by
  have h5 : ∀ x y : Fin N → E, (A.loc p).ιE (hq sig Hm x y) =
      hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) :=
    fun x y => ((GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm x y).symm
  funext j
  simp only [piQ, piL, Places.bc, map_sub, map_sum, map_add, map_mul, h5]
end GlobalTheory.HL.EichlerParams
