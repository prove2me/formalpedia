-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.psi_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:09:41.970834+00:00
-- url     : https://prove2.me/submissions/8d402ab4-893f-4fe3-8a68-bd43391fbe05

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
theorem _root_.solution {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have : ∀ᶠ x in 𝓝 x₀, ψ x₀ = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    have h1 : ψ (x - x₀) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx.le)
    calc ψ x₀ = ψ x₀ * ψ (x - x₀) := by rw [h1, mul_one]
      _ = ψ (x₀ + (x - x₀)) := (AddChar.map_add_eq_mul ψ _ _).symm
      _ = ψ x := by congr 1; abel
  exact continuousAt_const.congr this
end GlobalTheory.JR.RankOneTransfer
