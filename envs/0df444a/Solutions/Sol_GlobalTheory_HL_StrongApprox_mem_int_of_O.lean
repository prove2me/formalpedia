-- Prove2me | solution 1 for GlobalTheory.HL.StrongApprox.mem_int_of_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:53.830681+00:00
-- url     : https://prove2.me/submissions/735cad25-2a7c-48b1-84c0-7617218a3c4e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StrongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
namespace GlobalTheory.HL.StrongApprox
theorem _root_.solution (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (w : (A.loc p).Fp)
    (h : algebraMap (A.loc p).Fp (A.loc p).Ep w ∈ (A.L p).O) : w ∈ 𝒪[(A.loc p).Fp] := by
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  rw [(A.L p).O_def] at h
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] w :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h
  exact Valuation.Integers.mem_of_integral (Valuation.integer.integers (valuation (A.loc p).Fp)) h2
end GlobalTheory.HL.StrongApprox
