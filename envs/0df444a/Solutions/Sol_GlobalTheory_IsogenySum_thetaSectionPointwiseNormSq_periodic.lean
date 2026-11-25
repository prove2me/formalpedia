-- Prove2me | solution 1 for GlobalTheory.IsogenySum.thetaSectionPointwiseNormSq_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:21.856803+00:00
-- url     : https://prove2.me/submissions/87e13042-bc9a-4695-be64-aa4e13a75345

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_fock_translation_laws


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F (v + γ) = Y.ptN2 1 F v := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := fock_translation_laws U hU 1
  have h := h5 γ F (v + γ)
  rw [add_sub_cancel_right] at h
  unfold GT.ptN2
  rw [← h]
  conv_lhs => rw [← ((h6 Y F).1 hF).2 γ hγ]
  rw [Pi.smul_apply, norm_smul, Y.ka_abs γ hγ, one_mul]
end GlobalTheory.IsogenySum
