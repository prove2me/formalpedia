-- Prove2me | solution 1 for MenuCostPricing.claim_B_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:58:10.704308+00:00
-- url     : https://prove2.me/submissions/45a1fe2f-ef7c-4d2b-ace6-8a67e8189998

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

open MenuCostPricing in
theorem solution {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) (Γ : Finset (Fin T))
    (hΓ : ∀ t ∈ Γ, 1 ≤ t.val) (ŵ : Fin T → ℝ) (α β : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (x : Strategy n L T) (hx : I.APX Γ ŵ α β x) (t : Fin T) :
    1 - (1 + I.wt x t) / (1 + (1 + β) * ŵ t) ≤ α + β := by
  obtain ⟨-, -, hw⟩ := hx
  obtain ⟨hlo, hhi⟩ := hw t
  have hw0 : 0 ≤ I.wt x t := Finset.sum_nonneg (fun j _ => hI.w_nonneg t j _)
  have hŵ : 0 ≤ ŵ t := by nlinarith
  have hD : 0 < 1 + (1 + β) * ŵ t := by nlinarith
  have key : 1 - (α + β) ≤ (1 + I.wt x t) / (1 + (1 + β) * ŵ t) := by
    rw [le_div_iff₀ hD]
    nlinarith [mul_nonneg (add_nonneg hα0 hβ0) hŵ,
      mul_nonneg (mul_nonneg (add_nonneg hα0 hβ0) hβ0) hŵ]
  linarith
