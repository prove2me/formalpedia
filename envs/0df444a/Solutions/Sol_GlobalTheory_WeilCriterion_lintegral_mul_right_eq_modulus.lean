-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.lintegral_mul_right_eq_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:31.688877+00:00
-- url     : https://prove2.me/submissions/080ecbb7-ad00-4feb-b5ad-a448f677c87f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) (g : G) :
    ∫⁻ x, f (x * g) ∂μ = (modularCharacterFun g : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by
  rw [← lintegral_map hf (measurable_mul_const g), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl
end GlobalTheory.WeilCriterion
