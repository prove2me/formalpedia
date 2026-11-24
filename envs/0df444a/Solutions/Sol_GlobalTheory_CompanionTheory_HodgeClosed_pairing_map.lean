-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeClosed.pairing_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:14.209069+00:00
-- url     : https://prove2.me/submissions/02558924-f84d-4e76-9e65-ddd567e67495

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeClosed
variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
namespace GlobalTheory.CompanionTheory.HodgeClosed
theorem _root_.solution (v : Fin 2 → Module.Dual R N) (g : M →ₗ[R] N) (t : ⋀[R]^2 M) :
    exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) (exteriorPower.map 2 g t) =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) t := by
  have e : exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) ∘ₗ exteriorPower.map 2 g =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) := by
    apply exteriorPower.linearMap_ext
    ext x
    simp [exteriorPower.pairingDual_ιMulti_ιMulti]
  exact LinearMap.congr_fun e t
end GlobalTheory.CompanionTheory.HodgeClosed
