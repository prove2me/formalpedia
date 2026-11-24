-- Prove2me | solution 1 for GlobalTheory.NormSheafDescent.isLocalization_away_of_eq_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:18:05.088852+00:00
-- url     : https://prove2.me/submissions/91e99a2e-1a5b-47d1-b44d-f2e5b7614f03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFormCoefficientIdealMapLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoeffIdealFamilyMapBasicOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent
namespace GlobalTheory.NormSheafDescent
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (V : X.Opens) (hV : V = X.basicOpen g) (hle : V ≤ U) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    IsLocalization.Away g Γ(X, V) := by
  subst hV
  exact hU.isLocalization_basicOpen g
end GlobalTheory.NormSheafDescent
