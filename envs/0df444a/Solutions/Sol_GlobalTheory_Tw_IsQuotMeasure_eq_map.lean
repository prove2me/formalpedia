-- Prove2me | solution 1 for GlobalTheory.Tw.IsQuotMeasure.eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:35.424597+00:00
-- url     : https://prove2.me/submissions/f4d86023-6bdd-4b69-b695-91ea599a9d16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff

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
omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
namespace GlobalTheory.Tw
namespace IsQuotMeasure
theorem _root_.solution {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) {β : G → NNReal}
    (hβ : IsCosetCutoff T μT β) :
    ν = (μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T)) := by
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  ext S hS
  have hS' : MeasurableSet (Quotient.mk (QuotientGroup.rightRel T) ⁻¹' S) := measurable_quotient_mk'' hS
  rw [Measure.map_apply measurable_quotient_mk'' hS, withDensity_apply _ hS', ← lintegral_indicator hS',
    hν _ (hb.indicator hS'), ← lintegral_indicator_one hS]
  refine lintegral_congr fun c => ?_
  have hq : ∀ t : T, Quotient.mk (QuotientGroup.rightRel T) (t * c.out) = c := fun t => by
    conv_rhs => rw [← c.out_eq]
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp
  by_cases hc : c ∈ S
  · simp [Set.indicator, hq, hc, hβ.2]
  · simp [Set.indicator, hq, hc]
end IsQuotMeasure
end GlobalTheory.Tw
