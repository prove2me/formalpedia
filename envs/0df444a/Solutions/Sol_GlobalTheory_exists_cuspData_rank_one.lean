-- Prove2me | solution 1 for GlobalTheory.exists_cuspData_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:16.976748+00:00
-- url     : https://prove2.me/submissions/b76eb8e4-c371-4675-a648-8e70ca2c1cbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
import Theorems.Thm_GlobalTheory_GaussCusp_coordProd_mem
import Theorems.Thm_GlobalTheory_GaussCusp_one_mem_dom
import Theorems.Thm_GlobalTheory_GaussCusp_nonempty_type

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
namespace GlobalTheory
theorem _root_.solution : ∃ (X : DataX E4 1) (la : Wt X.Ψ 1) (P : Frame X.Ψ 1 → ℂ) (M : ℝ),
    P ∈ X.SS la ∧ la ≠ 0 ∧ (∃ x ∈ X.dom, P x ≠ 0) ∧ 0 < M ∧ X.Λ = X.L' ∧
    (∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E4, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧ ∀ τ : X.Ψ, (γ : Matrix (Fin 1) (Fin 1) E4).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)) := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ E4
  refine ⟨gaussCuspData, 1, GaussCusp.coordProd, 1, GaussCusp.coordProd_mem hζ, ?_,
    ⟨_, GaussCusp.one_mem_dom hζ, by simp [GaussCusp.coordProd]⟩, one_pos, rfl, ?_⟩
  · obtain ⟨τ⟩ := GaussCusp.nonempty_type hζ
    intro h
    exact one_ne_zero (congrFun (congrFun h τ) 0)
  · intro v _ hv b _ _
    rw [GaussCusp.eq_zero_of_iso hv]
    refine ⟨1, Subgroup.one_mem _, rfl, fun τ => ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp [Data.flowMat]
end GlobalTheory
