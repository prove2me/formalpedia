-- Prove2me | solution 1 for IAFTRL.lemma_C_3
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:06:29.542701+00:00
-- url     : https://prove2.me/submissions/25f179b7-63d7-4588-aec5-54db161da0d6

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost
import Definitions.Def_IAFTRL_allocMass
import Definitions.Def_IAFTRL_GA

import Theorems.Thm_IAFTRL_lemma_C_3_allocation
import Theorems.Thm_IAFTRL_lemma_C_3_cstar_bound

open Matrix IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar) (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀)
    (hΔ : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) :
    (∃ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n ∧
      allocCost arms θ jstar n ≤ 2 * BanditAlgorithm.linearBanditAllocationValue arms (-θ) ∧
      allocMass n ≤ 4 * ((d : ℝ) + GA arms ^ 2) / Δ₀ ^ 2) ∧
    BanditAlgorithm.linearBanditAllocationValue arms (-θ) ≤ 2 * (d : ℝ) / Δ₀ :=
  ⟨lemma_C_3_allocation hd arms hA θ jstar hu Δ₀ hΔ₀ hΔ,
    lemma_C_3_cstar_bound hd arms hA θ jstar hu Δ₀ hΔ₀ hΔ⟩
