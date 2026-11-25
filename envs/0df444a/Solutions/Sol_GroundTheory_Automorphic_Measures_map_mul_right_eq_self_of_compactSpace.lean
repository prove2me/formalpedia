-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.map_mul_right_eq_self_of_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:48.917853+00:00
-- url     : https://prove2.me/submissions/bca3e793-d06e-4b3e-822c-166aadd12ae8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] (k : K) :
    map (· * k) μ = μ := by
  have e := isMulLeftInvariant_eq_smul (map (· * k) μ) μ
  have h := congrArg (fun ν : Measure K => ν univ) e
  simp only [map_apply (continuous_mul_const k).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hc : haarScalarFactor (map (· * k) μ) μ = 1 := by
    have := (ENNReal.mul_eq_right (IsOpen.measure_ne_zero μ isOpen_univ univ_nonempty)
      (measure_ne_top μ univ)).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]
end GroundTheory.Automorphic.Measures
