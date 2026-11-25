-- Prove2me | solution 1 for GlobalTheory.T.isSmoothAt_of_smooth_mod_ideal_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:53:16.522301+00:00
-- url     : https://prove2.me/submissions/c82f9cfc-502e-4f8b-8a9f-38942f8e68f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowers
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSmoothAtOfSmoothModIdealPowersStatement
import Theorems.Thm_GlobalTheory_SmoothAdic_isSmoothAt_of_smooth_quotient_pow
import Theorems.Thm_GlobalTheory_SmoothLimit_isSmoothAt_of_smooth_quotient_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  first | exact @GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow | exact GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow | (intros; apply GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow <;> assumption)
end _root_.GlobalTheory.T
