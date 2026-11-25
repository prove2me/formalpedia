-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.WedgeField.wedge_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:48:13.403867+00:00
-- url     : https://prove2.me/submissions/d17ebd66-82bd-461b-85c6-84a578f926cd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hodge_WedgeField_sqEquiv__Multi_7d7f7aa32a02
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_cup
import Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyTwo_cup


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.WedgeField
namespace GlobalTheory.CompanionTheory.Hodge.WedgeField
theorem _root_.solution {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) (h2 : Function.Bijective m.pull2) (h : Wedge F') : Wedge F := by
  obtain ⟨e, he⟩ := h
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  let E2 : H2 F ≃ₗ[R] H2 F' := LinearEquiv.ofBijective m.pull2 h2
  refine ⟨(sqEquiv E1).trans (e.trans E2.symm), fun a b => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, sqEquiv_ιMulti, he, LinearEquiv.symm_apply_eq]
  exact (m.pullCohomologyTwo_cup a b).symm
end GlobalTheory.CompanionTheory.Hodge.WedgeField
