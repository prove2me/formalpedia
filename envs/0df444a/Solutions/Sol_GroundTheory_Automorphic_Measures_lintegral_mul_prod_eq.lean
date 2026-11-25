-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.lintegral_mul_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:39:04.98248+00:00
-- url     : https://prove2.me/submissions/2fdf2d90-b6af-4b61-9521-537ff14b1438

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_map_mul_prod_eq_smul
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
variable (K : Subgroup G)
variable {K}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] {f : G → ℝ≥0∞} (hf : Measurable f) :
    μG K * ∫⁻ p, ∫⁻ k, f ((p : G) * k) ∂μK ∂μP =
      μP (Subtype.val ⁻¹' (K : Set G)) * μK univ * ∫⁻ g, f g ∂μG := by
  have : LocallyCompactSpace P := hP.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  have : BorelSpace P := Subtype.borelSpace (P : Set G)
  have : BorelSpace K := Subtype.borelSpace (K : Set G)
  have hm : Measurable fun x : P × K => (x.1 : G) * x.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  have h := congrArg (fun μ : Measure G => ∫⁻ g, f g ∂μ)
    (map_mul_prod_eq_smul P K hP hKo hKc hPK μG μP μK)
  simp only [lintegral_smul_measure, smul_eq_mul] at h
  rw [lintegral_map hf hm, lintegral_prod (fun x : P × K => f ((x.1 : G) * x.2))
    (hf.comp hm).aemeasurable] at h
  exact h
end GroundTheory.Automorphic.Measures
