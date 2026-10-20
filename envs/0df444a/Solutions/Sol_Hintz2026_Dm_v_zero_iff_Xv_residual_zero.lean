-- Prove2me | solution 1 for Hintz2026.Dm_v_zero_iff_Xv_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T13:56:24.664574+00:00
-- url     : https://prove2.me/submissions/7b7f2c27-e21a-44bf-bc62-d1dcf63cc038

import Definitions.Def_Hintz2026_AnalysisV2
import Theorems.Thm_Hintz2026_Dm_Xv_sub_AXv

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026
-- inlined private helpers (de-privatized)
variable (p : SubextremalKN)
theorem mulVec_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsUnit M.det)
    {w : Fin 2 → ℂ} : M *ᵥ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have : M⁻¹ *ᵥ (M *ᵥ w) = M⁻¹ *ᵥ 0 := congr_arg _ h
    rwa [mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec, mulVec_zero] at this
  · intro h; rw [h, mulVec_zero]
end Hintz2026

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 → ℝ} (hx : x ∈ U p) (v : (Fin 2 → ℝ) → Fin 2 → ℂ) (hX : ∀ i j k, DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k)) (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) : (fun j => Dm p (fun z => v z j) x) = 0 ↔ (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) = 0 :=
  by
    rw [Dm_Xv_sub_AXv p hx v hX hv]
    exact (mulVec_eq_zero_iff (X_det_isUnit p hx)).symm

end
