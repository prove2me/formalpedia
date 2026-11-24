-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.isInvariantRadon_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:44.857089+00:00
-- url     : https://prove2.me/submissions/963e6726-585c-478e-94ab-51dbfdc469cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_measurable_mk
import Theorems.Thm_GlobalTheory_WeilCriterion_fibre_comp_mk_mul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
import Theorems.Thm_GlobalTheory_QuotientHaar_existsUnique_haar_of_invariantRadon
import Theorems.Thm_GlobalTheory_exists_bruhat_function_closed_subgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution (hH : IsClosed (H : Set G)) (μ μ' : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) (hμ' : IsInvariantRadon H μ') :
    ∃ c : ℝ≥0, 0 < c ∧ μ' = c • μ := by
  let ν : Measure H := haar
  obtain ⟨φ, hφ, hφ1, -⟩ := GlobalTheory.exists_bruhat_function_closed_subgroup G H hH ν
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ := GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ hμ
  obtain ⟨dg', ⟨hdg', hq'⟩, -⟩ := GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ' hμ'
  refine ⟨haarScalarFactor dg' dg, haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  ext A hA
  have hm : Measurable fun g : G => A.indicator (1 : G ⧸ H → ℝ≥0∞) (g : G ⧸ H) * φ g :=
    ((measurable_one.indicator hA).comp (measurable_mk H)).mul hφ
  have hfib : fibreIntegral H ν (fun g : G => A.indicator (1 : G ⧸ H → ℝ≥0∞) (g : G ⧸ H) * φ g) =
      A.indicator 1 := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [fibreIntegral_mk]
    exact fibre_comp_mk_mul H ν hφ hφ1 _ g
  have h1 := (hq _ hm).2
  have h2 := (hq' _ hm).2
  rw [hfib, lintegral_indicator_one hA] at h1 h2
  rw [Measure.smul_apply, ← h1, ← h2]
  conv_lhs => rw [isMulLeftInvariant_eq_smul dg' dg]
  rw [lintegral_smul_measure]
end GlobalTheory.WeilCriterion
