-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.isLocallyConstant_eta_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:43.803876+00:00
-- url     : https://prove2.me/submissions/307b88e6-3ed6-4f62-8699-cbc17c19eb20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
import Theorems.Thm_GlobalTheory_JR_OrbTest_eta_eq_of_norm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbTest
namespace GlobalTheory.JR.OrbTest
theorem _root_.solution {X F : Type} [TopologicalSpace X] [NormedField F] [IsUltrametricDist F]
    (h : X → F) (hc : Continuous h) (h0 : ∀ x, h x ≠ 0) : IsLocallyConstant (fun x => eta (h x)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : 0 < ‖h x‖ := norm_pos_iff.mpr (h0 x)
  have hev : ∀ᶠ y in 𝓝 x, dist (h y) (h x) < ‖h x‖ := (hc.tendsto x) (Metric.ball_mem_nhds _ hx)
  filter_upwards [hev] with y hy
  apply eta_eq_of_norm_eq
  rw [dist_eq_norm] at hy
  have hy' : ‖h x - h y‖ < ‖h x‖ := by rwa [norm_sub_rev]
  have e1 : ‖h y‖ ≤ max ‖h y - h x‖ ‖h x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h y - h x) (h x)
  have e2 : ‖h x‖ ≤ max ‖h x - h y‖ ‖h y‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (h x - h y) (h y)
  apply le_antisymm
  · exact e1.trans (max_le hy.le le_rfl)
  · rcases le_total ‖h x - h y‖ ‖h y‖ with hh | hh
    · exact e2.trans (max_le hh le_rfl)
    · exact absurd (e2.trans (max_le le_rfl hh)) (not_le.mpr hy')
end GlobalTheory.JR.OrbTest
