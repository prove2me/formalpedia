-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeClosed.eq_zero_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:56.980946+00:00
-- url     : https://prove2.me/submissions/5ecffd68-3359-43fa-a729-68f8e68ccce0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedStOfTwoFormCohSt
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeClosed_pairing_map
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
theorem _root_.solution [Module.Finite R M] [Module.Projective R M] (t : ⋀[R]^2 M)
    (h : ∀ v : Fin 2 → Module.Dual R M, exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 v) t = 0) :
    t = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hu : exteriorPower.map 2 g t = 0 := by
    let b := Pi.basisFun R (Fin n)
    refine (b.exteriorPower 2).repr.injective (Finsupp.ext fun s ↦ ?_)
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual, exteriorPower.ιMulti_family]
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact (pairing_map _ g t).trans (h _)
  exact exteriorPower.map_injective f hfg (hu.trans (map_zero _).symm)
end GlobalTheory.CompanionTheory.HodgeClosed
