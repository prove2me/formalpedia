-- Prove2me | solution 1 for GomoryGroup.Rel.card_factor_group
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:19:43.005992+00:00
-- url     : https://prove2.me/submissions/e99d3d81-8c3c-45ed-a2ab-656c212eb973

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting



namespace GomoryGroup.Rel

open Matrix

theorem card_core {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hB : B.det ≠ 0) :
    Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) ∧
      Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by
  have hinj : Function.Injective (Matrix.mulVecLin B) := by
    intro x y hxy
    have : B.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hB this
    exact sub_eq_zero.mp h2
  let e : (Fin m → ℤ) ≃ₗ[ℤ] LinearMap.range (Matrix.mulVecLin B) :=
    LinearEquiv.ofInjective (Matrix.mulVecLin B) hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range (Matrix.mulVecLin B)) e
  have hcomp : (LinearMap.range (Matrix.mulVecLin B)).subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((e : (Fin m → ℤ) →+ _)) = Matrix.mulVecLin B := by
    ext x : 1
    rfl
  have hd : LinearMap.det (Matrix.mulVecLin B) = B.det := by
    rw [← Matrix.toLin'_apply', LinearMap.det_toLin']
  have hcard : Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by
    rw [← h]
    unfold detD
    rw [hcomp, hd]
  refine ⟨?_, hcard⟩
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  unfold detD
  exact Int.natAbs_ne_zero.mpr hB

end GomoryGroup.Rel

open GomoryGroup.Rel


theorem solution {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (hB : B.det ≠ 0) :
    Finite ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) ∧
      Nat.card ((Fin m → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)) = detD B := by
  exact card_core B hB
