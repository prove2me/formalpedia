-- Prove2me | solution 1 for N25.unitNumerator25_slash
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:33.592751+00:00
-- url     : https://prove2.me/submissions/c93d5b0d-8b78-461e-a7c7-6cf504f35013

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

open UpperHalfPlane ModularForm

open scoped MatrixGroups ModularForm

namespace N25

theorem _root_.solution (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ((fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ) ∣[(36 : ℤ)] A) =
      (fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i (A • τ)) := by
  let D : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant
  let G : ModularForm 𝒮ℒ 36 := (D.mul D).mul D
  have hG (τ : UpperHalfPlane) : G τ = ModularForm.discriminant τ ^ 3 := by
    change (ModularForm.discriminant τ * ModularForm.discriminant τ) *
      ModularForm.discriminant τ = ModularForm.discriminant τ ^ 3
    ring
  have hg := G.slash_action_eq' (A : GL (Fin 2) ℝ) ⟨A, rfl⟩
  funext τ
  have hh := congrFun hg τ
  change ((G : UpperHalfPlane → ℂ) ∣[(36 : ℤ)] A) τ = G τ at hh
  rw [SL_slash_apply, hG, hG] at hh
  rw [SL_slash_apply]
  linear_combination (unitAnalytic25 i (A • τ)) * hh

end N25
