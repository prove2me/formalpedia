-- Prove2me | solution 1 for GlobalTheory.RealWeil.Osc.intw_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:53:04.001886+00:00
-- url     : https://prove2.me/submissions/2ab956b7-3021-4c86-b54a-d5dcefb2e32c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_intw_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution {h : IsHeis (omJ J) ρ} (h' : IsHeis (omJ J) ρ') (hT : ∀ x, T (proj h x) = T x)
    {f : B} (hf : Good h f) (A : B →L[ℂ] B) (hA : ∀ v f, A (ρ v f) = ρ v (A f))
    (hA' : ∀ v f, A (ρ' v f) = ρ' v (A f)) (hAT : ∀ x, A (T x) = T (A x)) :
    intw ρ' T ρ (A f) = A (intw ρ' T ρ f) := by
  rw [intw, intw, ← A.integral_comp_comm (intw_integrable h' hT hf)]
  simp only [hA, hA', hAT]
end GlobalTheory.RealWeil.Osc
