-- Prove2me | solution 1 for GlobalTheory.T.curvatureSumWedge_wellDefined_and_deRhamLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:07.663514+00:00
-- url     : https://prove2.me/submissions/15a0c43c-6feb-4e5d-ac66-95dba2ddfe87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CurvatureSumWedgeWellDefinedAndDeRhamLift
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CurvatureSumWedgeWellDefinedAndDeRhamLiftStatement
import Theorems.Thm_GlobalTheory_AbCoh_curvature_wellDefined_and_lift
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), (Closed1 F = ⊤ → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F), ObRel F x u v → ObRel F x u' v' → wsum F u v = wsum F u' v') ∧ ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (u v : Fin n → Glob1 F), ObRel F x u v → wsum F u v = 0 → ∃ c, toO F c = x := by
  first | exact @GlobalTheory.AbCoh.curvature_wellDefined_and_lift | exact GlobalTheory.AbCoh.curvature_wellDefined_and_lift | (intros; apply GlobalTheory.AbCoh.curvature_wellDefined_and_lift <;> assumption)
end _root_.GlobalTheory.T
