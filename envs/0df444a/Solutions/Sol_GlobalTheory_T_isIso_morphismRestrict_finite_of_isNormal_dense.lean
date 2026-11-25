-- Prove2me | solution 1 for GlobalTheory.T.isIso_morphismRestrict_finite_of_isNormal_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:22.470089+00:00
-- url     : https://prove2.me/submissions/664bdb07-3ab1-4bc3-94c0-d963e09a4077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoMorphismRestrictFiniteOfIsNormalDense
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoNearNormalPointOfFiniteBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoMorphismRestrictFiniteOfIsNormalDenseStatement
import Theorems.Thm_GlobalTheory_FiniteBirationalNear_isIso_morphismRestrict_of_isNormal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S T : Scheme.{0}} [IsLocallyNoetherian T] (ν : S ⟶ T) [IsFinite ν] (U V : T.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (V : Scheme.{0}) → Dense (U : Set T) → Dense (ν ⁻¹' (U : Set T)) → IsIso (ν ∣_ U) → IsIso (ν ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal | exact GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal | (intros; apply GlobalTheory.FiniteBirationalNear.isIso_morphismRestrict_of_isNormal <;> assumption)
end _root_.GlobalTheory.T
