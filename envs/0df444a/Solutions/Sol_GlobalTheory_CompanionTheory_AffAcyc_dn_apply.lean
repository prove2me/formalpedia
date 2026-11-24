-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.dn_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:08.689052+00:00
-- url     : https://prove2.me/submissions/a661710c-39ac-499a-affd-6b9fa7dd1850

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
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
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (z : Cn F n) (c : Fin (n + 2) ⥤ C) :
    dn F n z c = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
      mp F (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))) (z (face i c)) := by
  simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  rfl
end GlobalTheory.CompanionTheory.AffAcyc
