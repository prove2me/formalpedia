-- Prove2me | solution 1 for Hintz2026.Dm_adj_matrix
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:56:19.917255+00:00
-- url     : https://prove2.me/submissions/bb166320-bf53-4c8d-90e7-f349c510701e

import Definitions.Def_Hintz2026_System4
import Theorems.Thm_Hintz2026_Dm_congr

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026
-- inlined helpers (local source: Atlas/Perturbations/Hintz2026/*.lean at 8d059e0)
variable (p : SubextremalKN)

theorem Dm_adj_entry {x : Fin 2 -> ℝ} (hx : x ∈ U p) (i j : Fin 2) :
    Dm p (fun z => adjugate (X p z) i j) x =
    ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * Dm p (fun z => (X p z)⁻¹ i j) x := by
  have heq : Set.EqOn (fun z => adjugate (X p z) i j)
      (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j) (U p) :=
    fun z hz => adj_X_entry_eq p hz i j
  rw [Dm_congr p hx heq]
  unfold Dm cpd
  simp only [deriv_const_mul_field]
  ring

end Hintz2026

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : (of fun a b => Dm p (fun z => adjugate (X p z) a b) x) = -(adjugate (X p x) * A p x) :=
  by
    ext i j
    simp only [of_apply, Dm_adj_entry p hx]
    have h := congr_fun (congr_fun (Dm_Xinv_matrix p hx) i) j
    simp only [of_apply, neg_mul, Matrix.neg_apply] at h
    rw [h, adj_X_eq_const_smul_inv p hx, Matrix.neg_apply, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul]
    ring

end
