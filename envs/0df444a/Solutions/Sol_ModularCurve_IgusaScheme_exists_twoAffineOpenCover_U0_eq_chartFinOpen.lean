-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fa47e8e8-dcc3-558b-8edb-a34dbcccbb72

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ModularCurve_IgusaScheme_exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ 𝒱 : (IgusaScheme N ℓ).TwoAffineOpenCover, 𝒱.U0 = chartFinOpen N ℓ ∧ 𝒱.U1 = chartInfOpen N ℓ := by
  obtain ⟨f, g, hf, -, -⟩ := ModularCurve.IgusaScheme.exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one N ℓ
  exact ⟨{ U0 := chartFinOpen N ℓ, U1 := chartInfOpen N ℓ,
           isAffineOpen_U0 := isAffineOpen_chartFinOpen N ℓ, isAffineOpen_U1 := isAffineOpen_chartInfOpen N ℓ,
           sup_eq_top := igusaCover N ℓ,
           isAffineOpen_inf := by rw [hf]; exact (isAffineOpen_chartFinOpen N ℓ).basicOpen f }, rfl, rfl⟩

end S_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen (solution)
