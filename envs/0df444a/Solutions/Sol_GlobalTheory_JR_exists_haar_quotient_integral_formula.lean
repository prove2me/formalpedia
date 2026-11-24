-- Prove2me | solution 1 for GlobalTheory.JR.exists_haar_quotient_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:15.227692+00:00
-- url     : https://prove2.me/submissions/0901ef39-77e1-4628-98dc-b7f0b2ec5af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
import Theorems.Thm_GlobalTheory_JR_integral_inducedMeasure_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (A B C : Type) [Group A] [Group B] [Group C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C] [BorelSpace C] (φ : A →* B) (ψ : B →* C), TopologicalGroup.IsSES φ ψ → ∀ (μB : Measure B) (μC : Measure C), μB.IsHaarMeasure → μC.IsHaarMeasure → ∃ ν : Measure A, ν.IsHaarMeasure ∧ ∀ f : B → ℂ, Continuous f → HasCompactSupport f → ∀ s : C → B, (∀ c, ψ (s c) = c) → ∫ b, f b ∂μB = ∫ c, ∫ a, f (s c * φ a) ∂ν ∂μC := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ψ H μB μC hB hC
  have : LocallyCompactSpace A := H.isClosedEmbedding.locallyCompactSpace
  let ν0 : Measure A := Measure.haar
  set μ := H.inducedMeasure ν0 μC with hμ
  have hsm := Measure.isMulLeftInvariant_eq_smul μB μ
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure μB μ
  set k := Measure.haarScalarFactor μB μ with hk
  refine ⟨k • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hpos.ne', ?_⟩
  intro f hf hfc s hs
  let F : CompactlySupportedContinuousMap B ℂ := ⟨⟨f, hf⟩, hfc⟩
  have h := integral_inducedMeasure_complex H ν0 μC F
  rw [hsm, integral_smul_nnreal_measure]
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def]
  rw [integral_smul]
  congr 1
  refine h.trans ?_
  congr with c
  conv_lhs => rw [← hs c]
  rw [H.pushforward_apply_apply]
  simp only [TopologicalGroup.IsSES.pullback_def]
  rfl
end GlobalTheory.JR
