-- Prove2me | solution 1 for GlobalTheory.eventuallyEq_of_weierstrass_system
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.051101+00:00
-- url     : https://prove2.me/submissions/2bae4e82-02c0-45d6-a4e3-7cb27a607b19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {f₁ g₁ f₂ g₂ : ℂ → ℂ} {k z : ℂ}
    (h₁ : ∀ᶠ w in 𝓝 z, HasDerivAt f₁ (g₁ w) w ∧ HasDerivAt g₁ (6 * f₁ w ^ 2 - k) w)
    (h₂ : ∀ᶠ w in 𝓝 z, HasDerivAt f₂ (g₂ w) w ∧ HasDerivAt g₂ (6 * f₂ w ^ 2 - k) w)
    (hf : f₁ z = f₂ z) (hg : g₁ z = g₂ z) : f₁ =ᶠ[𝓝 z] f₂ := by
  have an : ∀ {f g : ℂ → ℂ}, (∀ᶠ w in 𝓝 z, HasDerivAt f (g w) w) → AnalyticAt ℂ f z :=
    fun h ↦ Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (h.mono fun w hw ↦ hw.differentiableAt)
  have a₁ := an (h₁.mono fun _ h ↦ h.1)
  have a₂ := an (h₂.mono fun _ h ↦ h.1)
  have b₁ := an (h₁.mono fun _ h ↦ h.2)
  have b₂ := an (h₂.mono fun _ h ↦ h.2)
  have d₁ : deriv (f₁ - f₂) =ᶠ[𝓝 z] g₁ - g₂ := by
    filter_upwards [h₁, h₂] with w p q using (p.1.sub q.1).deriv
  have d₂ : deriv (g₁ - g₂) =ᶠ[𝓝 z] (fun w ↦ 6 * (f₁ w + f₂ w)) * (f₁ - f₂) := by
    filter_upwards [h₁, h₂] with w p q
    rw [(p.2.sub q.2).deriv]
    simp
    ring
  have key : ∀ n : ℕ, n ≤ analyticOrderAt (f₁ - f₂) z ∧ n ≤ analyticOrderAt (g₁ - g₂) z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← analyticOrderAt_deriv_ge_iff (a₁.sub a₂) (by simp [hf]),
        ← analyticOrderAt_deriv_ge_iff (b₁.sub b₂) (by simp [hg]),
        analyticOrderAt_congr d₁, analyticOrderAt_congr d₂,
        analyticOrderAt_mul (by fun_prop) (a₁.sub a₂)]
      exact ⟨ih.2, ih.1.trans le_add_self⟩
  have := analyticOrderAt_eq_top.mp (ENat.eq_top_iff_forall_ge.mpr fun n ↦ (key n).1)
  filter_upwards [this] with w hw
  simpa [sub_eq_zero] using hw
end GlobalTheory
