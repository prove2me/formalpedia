-- Prove2me | solution 1 for KellyStochasticNetworks.alpha_fair_drift_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:13:18.168988+00:00
-- url     : https://prove2.me/submissions/d48fb312-0c12-4956-9079-d9fe5a91989a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem af_drift_identity {R : ℕ} (w n ν μ x : Fin R → ℝ) (α : ℝ)
    (hμ : ∀ r, 0 < μ r) (ρ : Fin R → ℝ) (hρ : ∀ r, ρ r = ν r / μ r) :
    (∑ r, (w r / μ r) * ρ r ^ (-α) * n r ^ α * (ν r - μ r * (n r * x r)))
      = ∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - n r * x r) := by
  refine Finset.sum_congr rfl fun r _ => ?_
  have hμ0 : μ r ≠ 0 := (hμ r).ne'
  have hν : ν r = ρ r * μ r := by rw [hρ r, div_mul_cancel₀ _ hμ0]
  rw [hν]; field_simp

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {R : ℕ} (w n ν μ x : Fin R → ℝ) (α : ℝ)
    (hμ : ∀ r, 0 < μ r) (ρ : Fin R → ℝ) (hρ : ∀ r, ρ r = ν r / μ r) :
    (∑ r, (w r / μ r) * ρ r ^ (-α) * n r ^ α * (ν r - μ r * (n r * x r)))
      = ∑ r, w r * ρ r ^ (-α) * n r ^ α * (ρ r - n r * x r) := by
  exact af_drift_identity w n ν μ x α hμ ρ hρ
