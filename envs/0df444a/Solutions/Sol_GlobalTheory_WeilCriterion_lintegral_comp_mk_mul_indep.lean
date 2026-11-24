-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.lintegral_comp_mk_mul_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:51.786283+00:00
-- url     : https://prove2.me/submissions/84492f69-0b4f-41dc-8ae7-c02ae34c5854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_mul_fibre_symm
import Theorems.Thm_GlobalTheory_WeilCriterion_measurable_mk
import Theorems.Thm_GlobalTheory_WeilCriterion_fibre_comp_mk_mul

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
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {φ ψ : G → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1)
    (hψ : Measurable ψ) (hψ1 : ∀ g : G, ∫⁻ h : H, ψ (g * h) ∂ν = 1)
    {F : G ⧸ H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (g : G ⧸ H) * φ g ∂dg = ∫⁻ g, F (g : G ⧸ H) * ψ g ∂dg := by
  have h := lintegral_mul_fibre_symm H hΔ dg ν (f := fun g => F (g : G ⧸ H) * φ g)
    ((hF.comp (measurable_mk H)).mul hφ) hψ
  simp_rw [hψ1, mul_one, fibre_comp_mk_mul H ν hφ hφ1] at h
  exact h
end GlobalTheory.WeilCriterion
