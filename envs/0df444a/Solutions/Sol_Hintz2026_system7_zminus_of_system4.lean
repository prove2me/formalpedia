-- Prove2me | solution 1 for Hintz2026.system7_zminus_of_system4
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T15:09:42.975257+00:00
-- url     : https://prove2.me/submissions/3fcaa924-0aa8-481a-b48c-fa63307152bc

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_contDiffOn_Xstar_entry
import Theorems.Thm_Hintz2026_Dp_Xstar_matrix
import Theorems.Thm_Hintz2026_adjugate_Cmat_eq

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026
-- inlined helpers (local source: Atlas/Perturbations/Hintz2026/*.lean at 8d059e0)
variable (p : SubextremalKN)

theorem hXstar_of_smooth {x : Fin 2 -> ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => (X p (update x k u))ᴴ i j) (x k) :=
  differentiableAt_slice p ((contDiffOn_Xstar_entry p i j).of_le le_top) hx k

theorem Dp_Xstar_mulVec {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (y : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (hy : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => y x j) (U p)) :
    (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ y z) i) x) =
    ((X p x)ᴴ * A p x) *ᵥ y x + (X p x)ᴴ *ᵥ (fun j => Dp p (fun z => y z j) x) := by
  ext i
  rw [Dp_mulVec_entry p (fun z => (X p z)ᴴ) y x i
    (fun j k => hXstar_of_smooth p hx i j k) (fun j k => hv_of_smooth p hy hx j k)]
  rw [Dp_Xstar_matrix p hx]
  rfl

end Hintz2026

open Hintz2026 in
theorem solution (p : SubextremalKN) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ) (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p)) (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p)) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (h4 : (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x = (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x) : (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ zplus p yplus x :=
  by
    rw [Dp_Xstar_mulVec p hx yminus hym]
    have hDp : (fun j => Dp p (fun z => yminus z j) x) =
        -(A p x *ᵥ yminus x) + (cscalar p sg om mm x • 1 + Bmat p sg om mm x) *ᵥ yplus x := by
      rw [← h4]; abel
    rw [hDp, mulVec_add, mulVec_neg, mulVec_mulVec, mulVec_mulVec]
    simp only [add_neg_cancel_left]
    unfold zplus
    rw [mulVec_mulVec]
    congr 1
    -- X^H (c*1 + B) = adj(C) adj(X) via adj(C) = k⁻¹ • X^H (cI+B) X and X adj(X) = k • 1
    rw [adjugate_Cmat_eq p sg om mm hx, Matrix.smul_mul, Matrix.mul_assoc, mul_adjugate, det_X p hx,
      Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Q_sq_sub_M_sq_ne_zero p), one_smul]

end
