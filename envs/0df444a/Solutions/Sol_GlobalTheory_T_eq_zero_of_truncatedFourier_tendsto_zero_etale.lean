-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:57.854809+00:00
-- url     : https://prove2.me/submissions/d192a31d-a0b8-45dc-866f-c8ed7e82c30b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
import Theorems.Thm_GlobalTheory_PlancherelZero_eq_zero_of_tendsto_fourier


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  first | exact @GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier | exact GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier | (intros; apply GlobalTheory.PlancherelZero.eq_zero_of_tendsto_fourier <;> assumption)
end _root_.GlobalTheory.T
