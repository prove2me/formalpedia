-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.wd_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:03.097361+00:00
-- url     : https://prove2.me/submissions/8a9b370f-c990-4694-87dd-7e86412de537

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_wd_apply
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (a b : V) : wd (R := R) b a = -wd a b :=
  Subtype.ext (by
    simpa [wd_apply, ExteriorAlgebra.ιMulti_apply] using
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R) b a))
end GlobalTheory.CompanionTheory.HodgeAlt
