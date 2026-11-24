-- Prove2me | solution 1 for GlobalTheory.GaussCusp.one_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:09:56.26591+00:00
-- url     : https://prove2.me/submissions/c247f0a4-05b3-475a-ab8e-6c25cf0f5f48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
import Theorems.Thm_GlobalTheory_GaussCusp_dmin_zero
import Theorems.Thm_GlobalTheory_GaussCusp_dmin_one

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
theorem _root_.solution (hζ : IsPrimitiveRoot ζ 4) :
    (fun _ _ _ => 1 : Frame (data hζ).Ψ 1) ∈ (data hζ).dom := by
  intro τ
  refine ⟨by simp [mat], fun i => ?_⟩
  change 0 < psgn 1 i * (dmin 1 _ τ i).re
  fin_cases i
  · change 0 < psgn 1 0 * (dmin 1 _ τ (Fin.castSucc 0)).re
    rw [dmin_zero]; simp [psgn]
  · change 0 < psgn 1 1 * (dmin 1 _ τ (Fin.succ 0)).re
    rw [dmin_one]; simp [psgn, sgn]
end GlobalTheory.GaussCusp
