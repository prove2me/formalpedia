-- Prove2me | solution 1 for GlobalTheory.HCA.dw_continuousFunctional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:24.439012+00:00
-- url     : https://prove2.me/submissions/229ad70a-7053-46c7-98dd-8156eba4e929

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDeriv
import Theorems.Thm_GlobalTheory_HCA_tendsto_diffQuot_dw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)),
    (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) →
    ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by
  intro d U hU B _ _ _ R hR hsm w
  induction w with
  | nil =>
    intro x hx
    exact ⟨⟨(LinearMap.proj x : (E d → ℂ) →ₗ[ℂ] ℂ).comp R, hR x hx⟩, fun u => rfl⟩
  | cons j w ih =>
    intro x hx
    choose! L hL using ih
    let y : ℕ → E d := fun n => x + (1 / ((n : ℝ) + 1)) • ev j
    let g : ℕ → B →L[ℂ] ℂ := fun n => ((n : ℂ) + 1) • (L (y n) - L x)
    have hev : ∀ᶠ n in atTop, y n ∈ U := by
      have hy : Tendsto y atTop (𝓝 x) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (ev j)
        simpa [y] using h0.const_add x
      exact hy (hU.mem_nhds hx)
    have hlim : Tendsto (fun n u => g n u) atTop (𝓝 (fun u => dw (j :: w) (R u) x)) := by
      rw [tendsto_pi_nhds]
      intro u
      refine (tendsto_diffQuot_dw hU (R u) (hsm u) w j hx).congr' ?_
      filter_upwards [hev] with n hn
      simp only [g, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
        hL _ hn, hL _ hx, y]
    exact ⟨continuousLinearMapOfTendsto g hlim, fun u => rfl⟩
end GlobalTheory.HCA
