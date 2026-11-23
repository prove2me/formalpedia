-- Prove2me | solution 1 for GlobalTheory.GaussCusp.dmin_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:32.209805+00:00
-- url     : https://prove2.me/submissions/bdf3440d-6e98-4f35-9674-60542fcbde27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant

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
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 1) (τ : Ψ) :
    dmin (1 : Matrix (Fin 1) (Fin 1) E) x τ (Fin.succ 0) = ((‖x τ 0 0‖ ^ 2 : ℝ) : ℂ) := by
  unfold dmin lminor
  refine (Matrix.det_fin_one _).trans ?_
  change gram τ.1 1 (mat x τ) 0 0 = _
  simp [gram, hermC, col, mat, Complex.mul_conj, Complex.normSq_eq_norm_sq]
end GlobalTheory.GaussCusp
