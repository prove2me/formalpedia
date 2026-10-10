-- Prove2me | solution 1 for HunterPDE.Shared.iteratedFDeriv_apply_coordinate_list
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:12:21.767571+00:00
-- url     : https://prove2.me/submissions/c4a1681c-4a45-407f-9983-721a3113ca14

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem solution {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (l : List (Fin n)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) :
    iteratedFDeriv ℝ l.length u x (fun j => EuclideanSpace.single (l.get j) 1) =
      iteratedPartial u l x := by
  induction l generalizing x with
  | nil => simp [iteratedFDeriv_zero_apply, iteratedPartial]
  | cons i l ih =>
    have hd := ((hu x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := l.length) (by exact_mod_cast (ENat.natCast_lt_top l.length))
    simp only [List.length_cons]
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun z => iteratedFDeriv ℝ l.length u z
        (fun j => EuclideanSpace.single (l.get j) 1)) =ᶠ[nhds x] iteratedPartial u l :=
      by
        filter_upwards [hs.mem_nhds hx] with z hz
        exact ih hz
    change fderiv ℝ (fun z => iteratedFDeriv ℝ l.length u z
      (fun j => EuclideanSpace.single (l.get j) 1)) x (EuclideanSpace.single i 1) = _
    simpa [Fin.tail, iteratedPartial, partialDeriv] using
      congrArg (fun L => L (EuclideanSpace.single i 1)) (he.fderiv_eq (𝕜 := ℝ))
