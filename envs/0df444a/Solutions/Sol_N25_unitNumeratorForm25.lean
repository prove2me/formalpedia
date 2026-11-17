-- Prove2me | solution 1 for N25.unitNumeratorForm25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:47.673535+00:00
-- url     : https://prove2.me/submissions/8759d9d0-a4b6-46e7-9110-ab1c52dc1775

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_GammaH25GL_isArithmetic
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_N25_unitAnalytic25_gammaH
import Theorems.Thm_N25_unitAnalytic25_mdifferentiable
import Theorems.Thm_N25_unitNumerator25_slash
import Theorems.Thm_N25_unitNumerator25_bounded_product
import Theorems.Thm_N25_unitNumerator_isIntegralQExp25

set_option autoImplicit false

open UpperHalfPlane ModularForm

open scoped MatrixGroups ModularForm Manifold

namespace N25

/-- The cube of the discriminant clears all cusps of the original unpowered unit. -/
theorem _root_.solution (i : Fin 5) :
    ∃ F : ModularForm GammaH25GL 36,
      (∀ τ : UpperHalfPlane,
        F τ = ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ) ∧
      ModularCurve.IsIntegralQExp F (unitNumeratorSeries25 i) := by
  letI : GammaH25GL.IsArithmetic := GammaH25GL_isArithmetic
  let F : ModularForm GammaH25GL 36 :=
    { toFun := fun τ => ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ
      slash_action_eq' := by
        rintro A ⟨B, hB, rfl⟩
        change ((fun τ : UpperHalfPlane => ModularForm.discriminant τ ^ 3 *
          unitAnalytic25 i τ) ∣[(36 : ℤ)] B) = _
        rw [unitNumerator25_slash]
        funext τ
        rw [unitAnalytic25_gammaH i B hB τ]
      holo' := (CuspForm.discriminant.holo'.pow 3).mul (unitAnalytic25_mdifferentiable i)
      bdd_at_cusps' := by
        intro c hc
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
        obtain ⟨A, rfl⟩ := hc
        rw [OnePoint.IsBoundedAt.smul_iff, OnePoint.isBoundedAt_infty_iff]
        change IsBoundedAtImInfty ((fun τ : UpperHalfPlane =>
          ModularForm.discriminant τ ^ 3 * unitAnalytic25 i τ) ∣[(36 : ℤ)] A)
        rw [unitNumerator25_slash]
        exact unitNumerator25_bounded_product i A }
  exact ⟨F, fun _ => rfl, unitNumerator_isIntegralQExp25 i⟩

end N25
