-- Prove2me | solution 1 for GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:33:54.821239+00:00
-- url     : https://prove2.me/submissions/9a6587ff-65b9-440b-bebe-79314cc21230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupLawJacobianExtensionChangeCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupLawJacobianExtensionChangeCoeffStatement
import Theorems.Thm_GlobalTheory_ChF_changeCoeff_law_lin_extSer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  first | exact @GlobalTheory.ChF.changeCoeff_law_lin_extSer | exact GlobalTheory.ChF.changeCoeff_law_lin_extSer | (intros; apply GlobalTheory.ChF.changeCoeff_law_lin_extSer <;> assumption)
end _root_.GlobalTheory.T
