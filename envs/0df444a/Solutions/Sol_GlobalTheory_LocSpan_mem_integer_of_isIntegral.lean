-- Prove2me | solution 1 for GlobalTheory.LocSpan.mem_integer_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:03.450226+00:00
-- url     : https://prove2.me/submissions/8ab7a011-443d-493e-a8d5-e0b434c90ffd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIntegersLocalisationIffSumCmData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocSpan
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
omit [StarRing E]
namespace GlobalTheory.LocSpan
theorem _root_.solution {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (a : A.Fp) (h : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep a)) :
    a ∈ 𝒪[A.Fp] := by
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  have h1 : IsIntegral 𝒪[A.Fp] a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).1 h
  exact (Valuation.integer.integers (valuation A.Fp)).mem_of_integral h1
end GlobalTheory.LocSpan
