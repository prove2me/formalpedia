-- Prove2me | solution 1 for GlobalTheory.SharpGradient.row_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:49.644228+00:00
-- url     : https://prove2.me/submissions/c21eb596-a87e-4caa-8faf-94ae52b449ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_GlobalTheory_SharpGradient_conj_diag
import Theorems.Thm_GlobalTheory_SharpGradient_posDef_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
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
theorem _root_.solution {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) (a : Fin p) :
    ∑ b, Complex.normSq ((Uᴴ * Z) a b) < 1 := by
  have h : 0 < (Uᴴ * (1 - Z * Zᴴ) * U : Matrix (Fin p) (Fin p) ℂ) a a := (posDef_conj U hU hZ).diag_pos
  have h1 := (Complex.lt_def.1 h).1
  rw [conj_diag U hU] at h1
  simp only [Complex.zero_re] at h1
  linarith
end GlobalTheory.SharpGradient
