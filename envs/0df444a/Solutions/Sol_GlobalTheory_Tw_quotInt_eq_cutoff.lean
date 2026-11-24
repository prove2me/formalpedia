-- Prove2me | solution 1 for GlobalTheory.Tw.quotInt_eq_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:11.927335+00:00
-- url     : https://prove2.me/submissions/239f11f7-da4b-4059-b180-f7a9e2ff2a7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_Tw_apply_out_mk
import Theorems.Thm_GlobalTheory_Tw_measurable_comp_out
import Theorems.Thm_GlobalTheory_Tw_IsQuotMeasure_eq_map
import Theorems.Thm_GlobalTheory_Tw_isQuotMeasure_quotMeas

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
variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]
namespace GlobalTheory.Tw
theorem _root_.solution (hT : IsClosed (T : Set G)) {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {F : G → ℂ}
    (hm : Measurable F) (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ∫ x, (β x : ℝ) • F x ∂μ := by
  rw [quotInt, (isQuotMeasure_quotMeas hT).eq_map hβ,
    integral_map measurable_quotient_mk''.aemeasurable (measurable_comp_out hm hF).aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hβ.1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [apply_out_mk hF]; rfl)
end GlobalTheory.Tw
