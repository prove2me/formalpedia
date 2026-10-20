-- Prove2me | solution 1 for Hintz2026.system4_yplus_of_system7
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:56:21.846401+00:00
-- url     : https://prove2.me/submissions/d12b237c-2b5b-49f2-a70d-6309513e9552

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Dm_Xv_sub_AXv

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) (zp zm : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hzp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => zp x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h7 : (fun i => Dm p (fun z => zp z i) x) = Cmat p sg om mm x *ᵥ zm x) : (fun j => Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ zp z)) j) x) - A p x *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x)) = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ zm x) :=
  by
    -- scalar k⁻¹ pulls out of Dm and of A·(·)
    have hk : ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q_sq_sub_M_sq_ne_zero p
    have hDmk : ∀ j, Dm p (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ * (X p z *ᵥ zp z) j) x
        = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ * Dm p (fun z => (X p z *ᵥ zp z) j) x := by
      intro j; unfold Dm cpd
      simp only [deriv_const_mul_field]; ring
    have hres := Dm_Xv_sub_AXv p hx zp (fun i j k => hX_of_smooth p hx i j k) (fun j k => hv_of_smooth p hzp hx j k)
    -- LHS = k⁻¹ • (Dm(X zp) - A (X zp)) = k⁻¹ • X Dm zp = k⁻¹ • X C zm
    have hL : (fun j => Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ zp z)) j) x)
          - A p x *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x))
        = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • ((fun i => Dm p (fun z => (X p z *ᵥ zp z) i) x) - A p x *ᵥ (X p x *ᵥ zp x)) := by
      ext j; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul]; rw [hDmk]; ring
    rw [hL, hres, h7, mulVec_mulVec]
    -- X C = X k⁻¹ adj(X)(cI-B)(X^H)⁻¹... use Cmat def directly: X * (det • X⁻¹ * M * Yinv) = det • M * Yinv
    unfold Cmat
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, X_mul_inv p hx, Matrix.one_mul,
      det_X p hx, smul_mulVec, smul_smul, inv_mul_cancel₀ hk, one_smul, ← mulVec_mulVec]

end
