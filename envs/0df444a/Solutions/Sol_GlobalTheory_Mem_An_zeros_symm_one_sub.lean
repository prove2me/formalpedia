-- Prove2me | solution 1 for GlobalTheory.Mem.An.zeros_symm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:35:09.967989+00:00
-- url     : https://prove2.me/submissions/ac0cbf0f-6e66-4bcd-a7f4-33875967978a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
import Theorems.Thm_GlobalTheory_Mem_An_zsym_eq
import Theorems.Thm_GlobalTheory_Mem_An_zsymFactor_ne_zero
import Theorems.Thm_GlobalTheory_Mem_An_zsymFactor_analyticAt
import Theorems.Thm_GlobalTheory_Mem_An_zsym_analyticAt_LFunction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
theorem _root_.solution : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      ((DirichletCharacter.LFunction χ ρ = 0 ↔ DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0) ∧
        zmult χ ρ = zmult χ⁻¹ (1 - ρ)) := by
  intro q _ χ hχ ρ h0 h1
  have hne := zsymFactor_ne_zero hχ h0 h1
  refine ⟨by rw [zsym_eq hχ h0 h1]; simp [hne], ?_⟩
  have hev : χ.LFunction =ᶠ[𝓝 ρ] zsymFactor χ * (χ⁻¹.LFunction ∘ fun s => 1 - s) := by
    have a : ∀ᶠ s : ℂ in 𝓝 ρ, 0 < s.re := (isOpen_lt continuous_const continuous_re).mem_nhds h0
    have b : ∀ᶠ s : ℂ in 𝓝 ρ, s.re < 1 := (isOpen_lt continuous_re continuous_const).mem_nhds h1
    filter_upwards [a, b] with s a b
    exact zsym_eq hχ a b
  have hρ : 1 - ρ ≠ 1 := by
    intro h; rw [sub_eq_self] at h; subst h; simp at h0
  have hL := zsym_analyticAt_LFunction χ⁻¹ hρ
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) ρ := by fun_prop
  have hf := zsymFactor_analyticAt χ h1
  unfold zmult analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hf (AnalyticAt.comp hL hg),
    hf.analyticOrderAt_eq_zero.2 hne, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by simp)]
end GlobalTheory.Mem.An
