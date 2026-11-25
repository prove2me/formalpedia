-- Prove2me | solution 1 for GlobalTheory.T.isHolTo_fibPt_and_comp_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:18:18.096372+00:00
-- url     : https://prove2.me/submissions/ee3915b3-645b-4274-aa65-f6edd1d8c287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibreStatement
import Theorems.Thm_GlobalTheory_HolFibre_isHolTo_fibPt_and_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) := by
  first | exact @GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | exact GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | (intros; apply GlobalTheory.HolFibre.isHolTo_fibPt_and_comp <;> assumption)
end _root_.GlobalTheory.T
