-- Prove2me | solution 1 for GlobalTheory.HL.LocPattern.zh_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:21.037176+00:00
-- url     : https://prove2.me/submissions/da9e2f52-25ed-480a-8aaf-849fee0e5a65

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrame
import Theorems.Thm_GlobalTheory_HL_LocPattern_f_loc
import Theorems.Thm_P2M_GlobalTheory_HL_LocPattern_f__loc_a49800aa5b1b
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.HL.LocPattern
theorem _root_.solution (a b : Fin (r + 1)) : (G.S p).Zh a b =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (b : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
      (A.loc p).ιE (G.Zh a b) := by
  show hf (A.L p) (G.S p).Hm ((G.S p).f' b) ((G.S p).f a) = _
  rw [f_loc, f'_loc, hf_smul_l, hf_smul_r, AlgEquiv.commutes, G.Hm_eq p,
    (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)]
  simp only [GFrames.Zh, Matrix.of_apply]
  ring
end GlobalTheory.HL.LocPattern
