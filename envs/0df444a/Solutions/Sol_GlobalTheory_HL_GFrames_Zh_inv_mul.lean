-- Prove2me | solution 1 for GlobalTheory.HL.GFrames.Zh_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:41.439255+00:00
-- url     : https://prove2.me/submissions/429ff811-268a-4cee-b270-0642c0927e71

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalPairingMatrixInvMulSelf
import Theorems.Thm_GlobalTheory_HL_GFrames_lead_last_eq_det
import Theorems.Thm_GlobalTheory_HL_GFrames_Zh_map_eq
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_PlacesInt_nontrivial_Ep


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GFrames
namespace GlobalTheory.HL.GFrames
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) : G.Zh⁻¹ * G.Zh = 1 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  have hS : IsUnit ((G.S p).Zh.det) := by
    have := (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).2.2.2.1
    rwa [Frames.D, lead_last_eq_det] at this
  have hd : IsUnit (Matrix.diagonal (fun a : Fin (r + 1) =>
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))))).det := by
    rw [Matrix.det_diagonal, ← map_prod]
    exact (IsUnit.prod_univ_iff.2 fun a => ((G.c p).isUnit.pow _)).map (algebraMap (A.loc p).Fp (A.loc p).Ep)
  have hι : IsUnit ((A.loc p).ιE G.Zh.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Zh_map_eq, Matrix.det_mul, Matrix.det_mul]
    exact (hd.mul hS).mul hd
  have hne : G.Zh.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hι
    exact not_isUnit_zero hι
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)
end GlobalTheory.HL.GFrames
