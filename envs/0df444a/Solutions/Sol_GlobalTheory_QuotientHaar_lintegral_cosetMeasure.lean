-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.lintegral_cosetMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:58.28331+00:00
-- url     : https://prove2.me/submissions/757c64c0-b4ed-4834-be7d-0dc9fb188bda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_mk
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.QuotientHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
namespace GlobalTheory.QuotientHaar
theorem _root_.solution (ν : Measure H) [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) (q : G ⧸ H) :
    ∫⁻ x, f x ∂(cosetMeasure H ν q) = fibreIntegral H ν f q := by
  induction q using QuotientGroup.induction_on with
  | H g => rw [cosetMeasure_mk, lintegral_map hf (measurable_translate H g), fibreIntegral_mk]
end GlobalTheory.QuotientHaar
