-- Prove2me | solution 1 for Hintz2026.Dp_v_zero_iff_Yv_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:56:26.755094+00:00
-- url     : https://prove2.me/submissions/65f62979-b804-466d-8b82-012921d8dfa3

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_Dp_Yv_add_AYv

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hY : ∀ i j k, DifferentiableAt ℝ (fun u => ((X p (update x k u))ᴴ)⁻¹ i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun j => Dp p (fun z => v z j) x) = 0 ↔ (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = 0 :=
  by
    rw [Dp_Yv_add_AYv p hx v hY hv]
    constructor
    · intro h; rw [h, mulVec_zero]
    · intro h
      have : (X p x)ᴴ *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x)) =
             (X p x)ᴴ *ᵥ 0 := congr_arg ((X p x)ᴴ *ᵥ ·) h
      rwa [mulVec_mulVec, Xstar_mul_inv p hx, one_mulVec, mulVec_zero] at this

end
