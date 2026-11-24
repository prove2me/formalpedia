-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.vanish_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:12.521503+00:00
-- url     : https://prove2.me/submissions/011b10c2-d85f-4780-849c-883373f46f1e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_vanish_map

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
theorem _root_.solution (A : Over (Sp R)) [GrpObj A] (hPar : Par (OAff (A ⊗ A).hom)) (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (p : Ideal R) [p.IsPrime] : ∃ r : R, r ∉ p ∧ r • c = 0 := by
  let B := Localization.AtPrime p
  let G := GlobForm (A ⊗ A).hom
  have k' := vanish_map A hPar c h1 h2 B (B ⊗[R] G) (TensorProduct.mk R B G 1)
  have hl : IsLocalizedModule p.primeCompl (TensorProduct.mk R B G 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl B _).2 (TensorProduct.isBaseChange R G B)
  obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl (TensorProduct.mk R B G 1)).1 k'
  exact ⟨r.1, r.2, hr⟩
end GlobalTheory.CompanionTheory.AxForm
