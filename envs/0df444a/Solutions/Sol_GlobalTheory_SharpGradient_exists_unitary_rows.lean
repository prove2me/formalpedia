-- Prove2me | solution 1 for GlobalTheory.SharpGradient.exists_unitary_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:10.362235+00:00
-- url     : https://prove2.me/submissions/e2582676-a129-4aa2-a2c5-d5f164cae464

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_conj_diag
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
namespace GlobalTheory.SharpGradient
theorem _root_.solution {p q : ℕ} {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    ∃ U : Matrix (Fin p) (Fin p) ℂ, Uᴴ * U = 1 ∧
      -Real.log (1 - Z * Zᴴ).det.re =
        ∑ a, -Real.log (1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b)) := by
  have hH := hZ.1
  have hU : (hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)ᴴ * hH.eigenvectorUnitary = 1 :=
    Unitary.coe_star_mul_self hH.eigenvectorUnitary
  refine ⟨hH.eigenvectorUnitary, hU, ?_⟩
  have hdiag : (hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)ᴴ * (1 - Z * Zᴴ) *
      (hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at this
  have hev : ∀ a, 1 - ∑ b, Complex.normSq
      (((hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)ᴴ * Z) a b) = hH.eigenvalues a := by
    intro a
    rw [← conj_diag _ hU, hdiag]
    simp
  have hd : (1 - Z * Zᴴ).det.re = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  rw [hd, Real.log_prod (fun a _ => (hZ.eigenvalues_pos a).ne'), Finset.sum_neg_distrib]
  simp only [hev]
end GlobalTheory.SharpGradient
