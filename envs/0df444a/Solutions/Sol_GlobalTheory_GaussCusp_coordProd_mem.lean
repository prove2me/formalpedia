-- Prove2me | solution 1 for GlobalTheory.GaussCusp.coordProd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:32:47.574293+00:00
-- url     : https://prove2.me/submissions/ba54d6d0-afa5-4fa7-b4cc-36c24dbbf9dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
import Theorems.Thm_GlobalTheory_GaussCusp_pnorm_coordProd_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
open GlobalTheory
open GlobalTheory.GaussCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ζ : E}
namespace GlobalTheory.GaussCusp
theorem _root_.solution (hζ : IsPrimitiveRoot ζ 4) : coordProd ∈ (data hζ).SS 1 := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, 1, fun x _ => pnorm_coordProd_le hζ x⟩, ?_⟩
  · apply Differentiable.differentiableOn
    unfold coordProd
    fun_prop
  · intro x _ b _
    unfold coordProd bchar rmul
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Matrix.mul_apply, mat, mul_comm]
  · intro γ hγ x _
    have h1 : γ = 1 := Subgroup.mem_bot.mp hγ
    subst h1
    have hx : lact 1 x = x := by
      funext τ
      simp [lact, mat]
      rfl
    rw [hx]
    exact (one_mul _).symm
  · rintro ξ ⟨_, h, hne⟩
    exact absurd (eq_zero_of_iso h) hne
end GlobalTheory.GaussCusp
