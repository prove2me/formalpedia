-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.integral_mul_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:24.711669+00:00
-- url     : https://prove2.me/submissions/a5519bab-c86d-4db0-bd7b-f22647867c55

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_map_mul_prod_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (K : Subgroup G)
variable {K}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : G → E} (hf : Integrable f μG) :
    μG.real K • ∫ p, ∫ k, f ((p : G) * k) ∂μK ∂μP =
      (μP.real (Subtype.val ⁻¹' (K : Set G)) * μK.real univ) • ∫ g, f g ∂μG := by
  have : LocallyCompactSpace P := hP.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  have : BorelSpace P := Subtype.borelSpace (P : Set G)
  have : BorelSpace K := Subtype.borelSpace (K : Set G)
  have hm : Measurable fun x : P × K => (x.1 : G) * x.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  have key := map_mul_prod_eq_smul P K hP hKo hKc hPK μG μP μK
  set ν := map (fun x : P × K => (x.1 : G) * x.2) (μP.prod μK)
  set d : ℝ≥0∞ := μP (Subtype.val ⁻¹' (K : Set G)) * μK univ with hd_def
  have hc0 : μG K ≠ 0 := hKo.measure_ne_zero μG ⟨1, K.one_mem⟩
  have hcT : μG K ≠ ∞ := hKc.measure_lt_top.ne
  have hPKc : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set P) :=
    hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hdT : d ≠ ∞ := ENNReal.mul_ne_top hPKc.measure_lt_top.ne (measure_ne_top _ _)
  have hν : ν = ((μG K)⁻¹ * d) • μG := by
    rw [mul_smul, ← key, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
  have hfν : Integrable f ν := by
    rw [hν]
    exact hf.smul_measure (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hdT)
  have hfm : Integrable (fun x : P × K => f ((x.1 : G) * x.2)) (μP.prod μK) :=
    (integrable_map_measure hfν.aestronglyMeasurable hm.aemeasurable).1 hfν
  have h1 : ∫ g, f g ∂ν = ∫ p, ∫ k, f ((p : G) * k) ∂μK ∂μP := by
    rw [integral_map hm.aemeasurable hfν.aestronglyMeasurable]
    exact integral_prod _ hfm
  have h2 : ∫ g, f g ∂ν = ((μG K)⁻¹ * d).toReal • ∫ g, f g ∂μG := by
    rw [hν, integral_smul_measure]
  rw [← h1, h2, smul_smul, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc, Measure.real,
    mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hc0, hcT⟩), one_mul, hd_def, ENNReal.toReal_mul]
  rfl
end GroundTheory.Automorphic.Measures
