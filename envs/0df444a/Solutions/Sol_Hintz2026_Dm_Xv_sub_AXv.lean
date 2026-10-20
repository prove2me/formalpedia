-- Prove2me | solution 1 for Hintz2026.Dm_Xv_sub_AXv
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:53:07.869336+00:00
-- url     : https://prove2.me/submissions/4a17487a-0b9d-4b7c-b7fc-0f04ea954dc7

import Definitions.Def_Hintz2026_AnalysisV2

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hX : ∀ i j k, DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) = X p x *ᵥ (fun j => Dm p (fun z => v z j) x) :=
  by
    ext i; simp only [Pi.sub_apply]
    rw [Dm_mulVec_entry p (X p) v x i (fun j k => hX i j k) hv]
    have hDmX : (of fun a b => Dm p (fun z => X p z a b) x) = A p x * X p x :=
      Dminus_X_eq_AX p hx
    rw [hDmX, mulVec_mulVec]; simp [add_sub_cancel_left]

end
