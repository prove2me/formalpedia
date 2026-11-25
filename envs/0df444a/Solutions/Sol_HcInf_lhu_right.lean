-- Prove2me | solution 1 for HcInf.lhu_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:09.225666+00:00
-- url     : https://prove2.me/submissions/535bb15d-ca77-4ef6-abcc-a33b9ddf788d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExLHU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace HcInf
theorem _root_.solution (m : Measure G) [m.IsHaarMeasure] (z : G) :
    ∃ r : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → m {x | x * z ∈ B} = r * m B := by
  have hmeas : Measurable (fun x : G => x * z) := measurable_mul_const z
  haveI : (m.map (fun x : G => x * z)).IsMulLeftInvariant := ⟨fun g => by
    rw [Measure.map_map (measurable_const_mul g) hmeas]
    have hc : ((fun x : G => g * x) ∘ fun x => x * z) = (fun x => x * z) ∘ fun x => g * x := by
      funext x; simp [mul_assoc]
    rw [hc, ← Measure.map_map hmeas (measurable_const_mul g), map_mul_left_eq_self]⟩
  haveI : IsFiniteMeasureOnCompacts (m.map (fun x : G => x * z)) := ⟨fun K hK => by
    rw [Measure.map_apply hmeas hK.measurableSet]
    exact ((Homeomorph.mulRight z).isCompact_preimage.2 hK).measure_lt_top⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, m.map (fun x : G => x * z) = c • m :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun B hB => ?_⟩
  show m ((fun x : G => x * z) ⁻¹' B) = _
  rw [← Measure.map_apply hmeas hB, hc, Measure.coe_nnreal_smul_apply]
end HcInf
