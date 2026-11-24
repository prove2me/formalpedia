-- Prove2me | solution 1 for GlobalTheory.HolPeriods.exists_local_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:57.934374+00:00
-- url     : https://prove2.me/submissions/f830f45a-e57e-4ee9-9cb4-6de09f4f8e01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods
namespace GlobalTheory.HolPeriods
theorem _root_.solution {n : ℕ} {U : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {a : Fin n → ℂ} (ha : a ∈ U) (hb : Function.Bijective (fderiv ℂ F a)) :
    ∃ (W : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen W ∧ F a ∈ W ∧ DifferentiableOn ℂ G W ∧
      ∀ w ∈ W, G w ∈ U ∧ F (G w) = w := by
  have han : AnalyticAt ℂ F a := GlobalTheory.SCV.analyticAt_of_differentiableOn hF (hU.mem_nhds ha)
  have hc : ContDiffAt ℂ ⊤ F a := han.contDiffAt
  let f' : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ F a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) hb).toContinuousLinearEquiv
  have hd : HasFDerivAt F (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) a := by
    have : (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F a := by ext1; rfl
    rw [this]; exact han.differentiableAt.hasFDerivAt
  have hinv := hc.to_localInverse hd (by simp)
  have hs := hc.hasStrictFDerivAt' hd (by simp)
  have h1 : ∀ᶠ w in nhds (F a), F (hc.localInverse hd (by simp) w) = w := hs.eventually_right_inverse
  have h2 : ∀ᶠ w in nhds (F a), hc.localInverse hd (by simp) w ∈ U := by
    have := hinv.continuousAt
    rw [ContinuousAt, hc.localInverse_apply_image] at this
    exact this (hU.mem_nhds ha)
  have h3 : ∀ᶠ w in nhds (F a), DifferentiableAt ℂ (hc.localInverse hd (by simp)) w :=
    (hinv.analyticAt.eventually_analyticAt).mono fun w hw => hw.differentiableAt
  obtain ⟨W, hW, hWo, hWa⟩ := eventually_nhds_iff.1 (h1.and (h2.and h3))
  exact ⟨W, _, hWo, hWa, fun w hw => (hW w hw).2.2.differentiableWithinAt,
    fun w hw => ⟨(hW w hw).2.1, (hW w hw).1⟩⟩
end GlobalTheory.HolPeriods
