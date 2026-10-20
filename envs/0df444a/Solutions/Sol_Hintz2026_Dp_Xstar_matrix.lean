-- Prove2me | solution 1 for Hintz2026.Dp_Xstar_matrix
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-10-19T14:56:16.204973+00:00
-- url     : https://prove2.me/submissions/b0bcdbf9-24f4-4bea-9192-225150ded1f6

import Definitions.Def_Hintz2026_System4

open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

open Hintz2026 in
theorem solution (p : SubextremalKN) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : (of fun a b => Dp p (fun z => (X p z)ᴴ a b) x) = (X p x)ᴴ * A p x :=
  by
    ext i j
    simp only [of_apply]
    have key : ∀ z, (X p z)ᴴ i j = star (X p z j i) := fun z => conjTranspose_apply _ _ _
    simp_rw [key, Dp_eq_star_Dm_star]
    simp only [star_star]
    have h := congr_fun (congr_fun (Dminus_X_eq_AX p hx) j) i
    simp only [of_apply] at h
    rw [h, ← conjTranspose_apply, conjTranspose_mul, A_conjTranspose p hx]

end
