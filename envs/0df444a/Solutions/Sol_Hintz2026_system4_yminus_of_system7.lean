-- Prove2me | solution 1 for Hintz2026.system4_yminus_of_system7
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:09:44.844623+00:00
-- url     : https://prove2.me/submissions/3fc55a93-8fbd-45ac-9a43-ac8e6790526e

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Dp_Yv_add_AYv
import Theorems.Thm_Hintz2026_adjugate_Cmat_eq

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (zp zm : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hzm : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => zm x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h7 : (fun i => Dp p (fun z => zm z i) x) = adjugate (Cmat p sg om mm x) *ᵥ zp x) : (fun j => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ zm z) j) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ zm x) = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x)) :=
  by
    have hres := Dp_Yv_add_AYv p hx zm (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hzm hx j k)
    rw [hres, h7, adjugate_Cmat_eq p sg om mm hx, smul_mulVec, mulVec_smul, mulVec_mulVec,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_Xstar p hx, Matrix.one_mul]
    rw [mulVec_smul, mulVec_mulVec]

end
