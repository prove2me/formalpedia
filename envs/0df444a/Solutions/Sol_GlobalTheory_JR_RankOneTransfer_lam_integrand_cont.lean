-- Prove2me | solution 1 for GlobalTheory.JR.RankOneTransfer.lam_integrand_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:27.528843+00:00
-- url     : https://prove2.me/submissions/7ce6cfb0-be46-4d63-9ec1-58e4f85f2fe4

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
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_nS_add
import Theorems.Thm_GlobalTheory_JR_RankOneTransfer_psi_cont

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
theorem _root_.solution {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (a : A.K)
    (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) (hΦ : A.InI Φ) :
    Continuous fun z => Φ (wS A.K * nS z) * A.psiK ψ (-(a * z)) := by
  refine Continuous.mul ?_ ?_
  · obtain ⟨⟨U, hU, hinv⟩, -⟩ := hΦ
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    have hpre : {z : A.K | z - z₀ ∈ U} ∈ 𝓝 z₀ := by
      have ht : Tendsto (fun z : A.K => z - z₀) (𝓝 z₀) (𝓝 0) := by
        simpa using (continuous_id.sub continuous_const).tendsto z₀ (f := fun z : A.K => z - z₀)
      exact ht hU
    have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
    have : ∀ᶠ z in 𝓝 z₀, Φ (wS A.K * nS z₀) = Φ (wS A.K * nS z) := by
      filter_upwards [hpre] with z hz
      have hz' : z = z₀ + (z - z₀) := by abel
      rw [hz', nS_add, ← mul_assoc]
      symm
      apply hinv
      intro i j
      fin_cases i <;> fin_cases j <;> simp [nS, h0, hz]
    exact continuousAt_const.congr this
  · have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact (psi_cont ψ hψ).comp (htr.comp (continuous_const.mul continuous_id).neg)
end GlobalTheory.JR.RankOneTransfer
