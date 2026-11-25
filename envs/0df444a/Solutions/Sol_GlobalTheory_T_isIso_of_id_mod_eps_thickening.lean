-- Prove2me | solution 1 for GlobalTheory.T.isIso_of_id_mod_eps_thickening
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:24.116525+00:00
-- url     : https://prove2.me/submissions/2227e4fd-178c-4d5d-aba9-afdf836a5ecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickeningStatement
import Theorems.Thm_GlobalTheory_isIso_of_id_mod_eps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  first | exact @GlobalTheory.isIso_of_id_mod_eps | exact GlobalTheory.isIso_of_id_mod_eps | (intros; apply GlobalTheory.isIso_of_id_mod_eps <;> assumption)
end _root_.GlobalTheory.T
