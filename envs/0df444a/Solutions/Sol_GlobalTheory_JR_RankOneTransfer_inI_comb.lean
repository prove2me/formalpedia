-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.inI_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:57.15474+00:00
-- url     : https://prove2.me/submissions/932834c7-c6e8-4e6c-9fa6-bc21548d7593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KirillovVanishingOfLimitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypMemInducedFourierWeylStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInducedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerWeilRepEventuallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleOrbitalFourierRankOneTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.RankOneTransfer
namespace GlobalTheory.JR.RankOneTransfer
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (Φ₁ Φ₂ : SpecialLinearGroup (Fin 2) A.K → ℂ) (r : ℂ), A.InI Φ₁ → A.InI Φ₂ →
    A.InI (fun g => Φ₁ g + r * Φ₂ g) := by
  intro F E _ _ _ _ A Φ₁ Φ₂ r h₁ h₂
  obtain ⟨⟨U₁, hU₁, i₁⟩, e₁⟩ := h₁
  obtain ⟨⟨U₂, hU₂, i₂⟩, e₂⟩ := h₂
  refine ⟨⟨U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂, fun g k hk => ?_⟩, fun z s g => ?_⟩
  · simp only
    rw [i₁ g k (fun i j => (hk i j).1), i₂ g k (fun i j => (hk i j).2)]
  · simp only
    rw [e₁, e₂]
    ring
end GlobalTheory.JR.RankOneTransfer
