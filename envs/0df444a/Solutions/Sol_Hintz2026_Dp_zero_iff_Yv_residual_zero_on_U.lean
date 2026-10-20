-- Prove2me | solution 1 for Hintz2026.Dp_zero_iff_Yv_residual_zero_on_U
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:59:03.543986+00:00
-- url     : https://prove2.me/submissions/1434b6da-8edc-41ed-8598-6cafba61b7fd

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_Dp_v_zero_iff_Yv_residual_zero

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) : (∀ x ∈ U p, (fun j => Dp p (fun z => v z j) x) = 0) ↔ (∀ x ∈ U p, (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = 0) :=
  by
    constructor <;> intro h x hx
    · rw [← Dp_v_zero_iff_Yv_residual_zero p hx v
        (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hv hx j k)]
      exact h x hx
    · rw [Dp_v_zero_iff_Yv_residual_zero p hx v
        (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hv hx j k)]
      exact h x hx

end
