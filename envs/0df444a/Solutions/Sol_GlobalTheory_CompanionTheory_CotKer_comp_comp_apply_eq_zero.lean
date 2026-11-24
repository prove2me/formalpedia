-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CotKer.comp_comp_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:47.245422+00:00
-- url     : https://prove2.me/submissions/1450d540-696c-4dda-bb72-72e196ef8464

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IdealSquareLeKernelOfSquareZeroMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotKer
namespace GlobalTheory.CompanionTheory.CotKer
theorem _root_.solution {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (a : A)
    (ha : f.hom a = 0) : ((f ≫ g) ≫ h).hom a = 0 := by
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
end GlobalTheory.CompanionTheory.CotKer
