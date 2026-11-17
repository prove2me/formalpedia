-- Prove2me | solution 1 for N25.jAnalytic_sl_invariant
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:36.527312+00:00
-- url     : https://prove2.me/submissions/81797b3d-a59b-487a-9606-2ccf95c2bc61

import Mathlib

set_option autoImplicit false

open UpperHalfPlane

open scoped MatrixGroups

namespace N25

/-- The analytic j-ratio is invariant under every integral determinant-one matrix. -/
theorem _root_.solution (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ModularForm.E₄ (A • τ) ^ 3 / ModularForm.discriminant (A • τ) =
      ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  have htop : ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
    simp [MonoidHom.range_eq_map]
  let G : ModularForm (⊤ : Subgroup SL(2, ℤ)) 12 :=
    ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) htop
  let H : ModularForm (⊤ : Subgroup SL(2, ℤ)) 12 :=
    ModularForm.mcast rfl (CuspForm.toModularFormₗ CuspForm.discriminant) htop
  change G (A • τ) / H (A • τ) = G τ / H τ
  rw [SlashInvariantForm.slash_action_eqn_SL'' G (Subgroup.mem_top A) τ,
      SlashInvariantForm.slash_action_eqn_SL'' H (Subgroup.mem_top A) τ]
  exact mul_div_mul_left _ _ (zpow_ne_zero (12 : ℤ) (denom_ne_zero A τ))

end N25
