-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.ext2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:52.813221+00:00
-- url     : https://prove2.me/submissions/39848c84-e1d0-4d6d-890a-d436027a48ae

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_iota_multi_two_eta
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution {N : Type} [AddCommGroup N] [Module R N] {f g : ⋀[R]^2 V →ₗ[R] N}
    (h : ∀ a b, f (i2 a b) = g (i2 a b)) : f = g :=
  exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ by
    simpa [iota_multi_two_eta] using h (v 0) (v 1))
end GlobalTheory.CompanionTheory.Hodge.LiftO
