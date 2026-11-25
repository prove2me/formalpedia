-- Prove2me | solution 1 for GlobalTheory.T.isProper_inf_ideal_sheaf_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:44.862993+00:00
-- url     : https://prove2.me/submissions/84f7b3cb-0362-4f8c-a7d9-899f80e88608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImage
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImageStatement
import Theorems.Thm_P2M_GlobalTheory_isProper_map_inf_subscheme__35c749836b7f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  first | exact @GlobalTheory.isProper_map_inf_subschemeι | exact GlobalTheory.isProper_map_inf_subschemeι | (intros; apply GlobalTheory.isProper_map_inf_subschemeι <;> assumption)
end _root_.GlobalTheory.T
