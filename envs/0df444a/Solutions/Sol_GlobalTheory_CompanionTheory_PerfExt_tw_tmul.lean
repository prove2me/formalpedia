-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PerfExt.tw_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:33.262173+00:00
-- url     : https://prove2.me/submissions/758d8869-b6df-4470-8920-2d1a70ac3070

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_D2Apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfExt
variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
variable {R R'}
variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]
namespace GlobalTheory.CompanionTheory.PerfExt
theorem _root_.solution (E : R' ⊗[R] N ≃ₗ[R'] Q) (x : M) (n : N) : tw M E (x ⊗ₜ n) = x ⊗ₜ E (1 ⊗ₜ n) := by
  simp [tw]
end GlobalTheory.CompanionTheory.PerfExt
