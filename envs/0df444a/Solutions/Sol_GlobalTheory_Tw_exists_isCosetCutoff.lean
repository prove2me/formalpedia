-- Prove2me | solution 1 for GlobalTheory.Tw.exists_isCosetCutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:33:52.977157+00:00
-- url     : https://prove2.me/submissions/79774f3a-b032-45f3-a4a1-559517032ad2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_bruhatFunctionExists_closedSubgroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
omit [SecondCountableTopology G]
namespace GlobalTheory.Tw
theorem _root_.solution [LocallyCompactSpace G] [T2Space G] (hT : IsClosed (T : Set G)) [μT.IsHaarMeasure]
    [μT.IsInvInvariant] : ∃ β : G → NNReal, Continuous β ∧ IsCosetCutoff T μT β := by
  obtain ⟨β, hc, h0, -, h1⟩ := GlobalTheory.bruhatFunctionExists_closedSubgroup G T hT μT inferInstance
  have hcont : Continuous fun x => (β x⁻¹).toNNReal := continuous_real_toNNReal.comp (hc.comp continuous_inv)
  refine ⟨fun x => (β x⁻¹).toNNReal, hcont, hcont.measurable, fun x => ?_⟩
  have hi : Integrable (fun h : T => β (x⁻¹ * h)) μT := by
    by_contra hn
    have := h1 x⁻¹
    rw [integral_undef hn] at this
    exact zero_ne_one this
  have h2 := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun h => h0 _)
  rw [h1, ENNReal.ofReal_one, ← lintegral_inv_eq_self] at h2
  rw [h2]
  simp [ENNReal.ofReal]
end GlobalTheory.Tw
