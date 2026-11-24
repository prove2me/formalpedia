-- Prove2me | solution 1 for GlobalTheory.Published.LogLine.exists_ball_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:46.093122+00:00
-- url     : https://prove2.me/submissions/28c148c5-a373-45ef-a40a-8342bb4cd10b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_Published_LogLine_exists_div_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.LogLine
variable {n : ℕ}
namespace GlobalTheory.Published.LogLine
theorem _root_.solution {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n))
    {a : Fin n → (Fin n → ℂ) → ℂ} (ha : ∀ i, DifferentiableOn ℂ (a i) U)
    (h0 : ∀ i ∈ S, ∀ z ∈ U, z i = 0 → a i z = 0) {c : Fin n → ℂ} (hc : c ∈ U) :
    ∃ r > 0, ball c r ⊆ U ∧ ∃ b : Fin n → (Fin n → ℂ) → ℂ,
      (∀ i, DifferentiableOn ℂ (b i) (ball c r)) ∧
      ∀ i, ∀ z ∈ ball c r, a i z = (if i ∈ S then z i else 1) * b i z := by
  have hev : ∀ᶠ z in 𝓝 c, z ∈ U ∧ ∀ i, c i ≠ 0 → z i ≠ 0 := by
    refine Filter.Eventually.and (hU.mem_nhds hc) (eventually_all.mpr fun i => ?_)
    by_cases h : c i = 0
    · simp [h]
    · exact ((continuous_apply i).continuousAt.eventually_ne h).mono fun z hz _ => hz
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsub : ball c r ⊆ U := fun z hz => (h z hz).1
  refine ⟨r, hr, hsub, ?_⟩
  have : ∀ i, ∃ b : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ b (ball c r) ∧
      ∀ z ∈ ball c r, a i z = (if i ∈ S then z i else 1) * b z := by
    intro i
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      by_cases hci : c i = 0
      · exact exists_div_ball hci ((ha i).mono hsub) fun z hz => h0 i hi z (hsub hz)
      · refine ⟨fun z => a i z * (z i)⁻¹, ((ha i).mono hsub).mul
          (DifferentiableOn.fun_inv (𝕜 := ℂ) (h := fun z : Fin n → ℂ => z i) (by fun_prop)
            fun z hz => (h z hz).2 i hci), fun z hz => ?_⟩
        have := (h z hz).2 i hci
        field_simp
    · exact ⟨a i, (ha i).mono hsub, fun z _ => by simp [hi]⟩
  choose b hb using this
  exact ⟨b, fun i => (hb i).1, fun i => (hb i).2⟩
end GlobalTheory.Published.LogLine
