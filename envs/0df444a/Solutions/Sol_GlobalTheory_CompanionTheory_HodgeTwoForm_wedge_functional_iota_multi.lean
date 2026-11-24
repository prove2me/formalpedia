-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.wedge_functional_iota_multi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:00.746808+00:00
-- url     : https://prove2.me/submissions/aeecc7fe-ced4-44fc-9ac9-22a1551c2b19

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (L : Fin n → Module.Dual A M) (i j : Fin n) (a b : M) :
    L2 L i j (exteriorPower.ιMulti A 2 ![a, b]) = L i a * L j b - L j a * L i b := by
  rw [L2, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp
end GlobalTheory.CompanionTheory.HodgeTwoForm
