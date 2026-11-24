-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.pt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:12.895148+00:00
-- url     : https://prove2.me/submissions/8e8c9a52-3327-4bbc-a0d2-c227281a5461

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution {C C' C'' : Type} [CommRing C] [CommRing C'] [CommRing C''] {ρ : R →+* C} {ρ' : R →+* C'}
    {ρ'' : R →+* C''} (f : C →+* C') (h : f.comp ρ = ρ') (g : C' →+* C'') (h' : g.comp ρ' = ρ'')
    (k : C →+* C'') (hk : g.comp f = k) (h'' : k.comp ρ = ρ'') : pt g h' ≫ pt f h = pt k h'' := by
  subst hk
  ext1
  exact (spMap_comp f g).symm
end GlobalTheory.CompanionTheory.AxForm
