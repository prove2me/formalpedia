-- Prove2me | solution 1 for GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:51.900464+00:00
-- url     : https://prove2.me/submissions/f07ae915-9a20-4ba6-9373-59a6e15b52f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorDerivGlobalOneFormEqSumWedge
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorDerivGlobalOneFormEqSumWedgeStatement
import Theorems.Thm_GlobalTheory_AbCoh_dOne_glob_eq_wsum


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  first | exact @GlobalTheory.AbCoh.dOne_glob_eq_wsum | exact GlobalTheory.AbCoh.dOne_glob_eq_wsum | (intros; apply GlobalTheory.AbCoh.dOne_glob_eq_wsum <;> assumption)
end _root_.GlobalTheory.T
