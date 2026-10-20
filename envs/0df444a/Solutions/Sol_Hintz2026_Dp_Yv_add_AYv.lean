-- Prove2me | solution 1 for Hintz2026.Dp_Yv_add_AYv
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:11.478745+00:00
-- url     : https://prove2.me/submissions/c5869a3c-3d28-45b1-ae3b-5c53e29b7ace

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hY : ∀ i j k, DifferentiableAt ℝ (fun u => ((X p (update x k u))ᴴ)⁻¹ i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = ((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x) :=
  by
    ext i; simp only [Pi.add_apply]
    rw [Dp_mulVec_entry p (fun z => ((X p z)ᴴ)⁻¹) v x i (fun j k => hY i j k) hv]
    have hDpY : (of fun a b => Dp p (fun z => ((X p z)ᴴ)⁻¹ a b) x) =
        -A p x * ((X p x)ᴴ)⁻¹ := Dplus_XstarInv_eq p hx
    rw [hDpY, neg_mul, mulVec_mulVec]
    simp only [neg_mulVec, Pi.neg_apply]; ring

end
