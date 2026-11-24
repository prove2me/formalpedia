-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.wb_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:07.046813+00:00
-- url     : https://prove2.me/submissions/f2a36c24-f7fd-4090-a34d-f7bd5bc79d08

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_apply
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
theorem _root_.solution (a b : M) : wb (A := A) b a = -wb a b :=
  Subtype.ext (by
    simpa [wb_apply, ExteriorAlgebra.ιMulti_apply] using
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := A) b a))
end GlobalTheory.CompanionTheory.HodgeTwoForm
