-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.coordinate_reindex_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:26:36.80234+00:00
-- url     : https://prove2.me/submissions/a488baac-0559-4511-b233-744c8007a13b

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fin_append_linear_isometry
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) :
    ∃ e : ((Fin m → Real) × Real) ≃ₗᵢ[Real] (Fin (m + 1) → Real),
      (∀ p i, e p (Fin.castSucc i) = p.1 i) ∧
      (∀ p, e p (Fin.last m) = p.2) := by
  obtain ⟨a, ha⟩ :=
    OAI.PiExponent.DeterminantContradiction.fin_append_linear_isometry m
  let c : Real ≃ₗᵢ[Real] (Fin 1 → Real) :=
    { (LinearEquiv.funUnique (Fin 1) Real Real).symm with
      norm_map' := by
        intro x
        simpa [Pi.norm_def] }
  let d : ((Fin m → Real) × Real) ≃ₗᵢ[Real]
      ((Fin m → Real) × (Fin 1 → Real)) :=
    { toLinearEquiv :=
        LinearEquiv.prodCongr (LinearEquiv.refl Real (Fin m → Real)) c.toLinearEquiv
      norm_map' := by
        intro x
        simp [Prod.norm_def, c, Pi.norm_def] }
  refine ⟨d.trans a, ?_⟩
  constructor
  · intro p i
    change a (p.1, fun _ : Fin 1 => p.2) (Fin.castSucc i) = p.1 i
    rw [ha]
    exact Fin.append_left p.1 (fun _ : Fin 1 => p.2) i
  · intro p
    change a (p.1, fun _ : Fin 1 => p.2) (Fin.last m) = p.2
    rw [ha]
    have hidx : Fin.last m = Fin.natAdd m (0 : Fin 1) := by
      apply Fin.ext
      simp
    rw [hidx]
    exact Fin.append_right p.1 (fun _ : Fin 1 => p.2) 0
