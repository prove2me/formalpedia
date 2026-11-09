-- Prove2me | solution 1 for KarimiPL.ProxCD.eq_62_coord_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T11:42:47.515589+00:00
-- url     : https://prove2.me/submissions/a930ed78-4a11-445e-86c6-d2c4068a1f10

import Mathlib
import Definitions.Def_KarimiPL_ProxCD_sepG
import Definitions.Def_KarimiPL_ProxCD_coordModel

open KarimiPL.ProxCD in
theorem solution {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {gc : Fin d → ℝ → ℝ} {L : ℝ} (hf : Differentiable ℝ f)
    (hcoord : ∀ (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (α : ℝ),
      f (x + EuclideanSpace.single i α) ≤ f x + α * gradient f x i + L / 2 * α ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (t : ℝ) :
    f (x + EuclideanSpace.single i t) + sepG gc (x + EuclideanSpace.single i t) -
        (f x + sepG gc x) ≤ coordModel f gc L i x t := by
  have hterm : ∀ j, gc j ((x + EuclideanSpace.single i t) j) =
      gc j (x j) + (if j = i then gc i (x i + t) - gc i (x i) else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have hsep : sepG gc (x + EuclideanSpace.single i t) =
      sepG gc x + (gc i (x i + t) - gc i (x i)) := by
    unfold sepG
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
  have h := hcoord x i t
  rw [hsep]
  unfold coordModel
  linarith
