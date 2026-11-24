-- Prove2me | solution 1 for GlobalTheory.FramePotential.factor_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:24.625447+00:00
-- url     : https://prove2.me/submissions/82243b5d-150f-4160-8845-76fb30a410cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OneLeMinorOfIsOrth
import Theorems.Thm_GlobalTheory_FramePotential_lminor_mul_upper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bdiag_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dmin_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_upper_of_bor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder
open GlobalTheory GlobalTheory.FramePotential
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FramePotential
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 x : Frame X.Ψ r) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm (rmul x b) τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat (rmul x b) τ) i‖ ^ 2 =
      ‖dmin X.Gm x τ i‖ / ‖lminor ((mat x0 τ)⁻¹ * mat x τ) i‖ ^ 2 := by
  have e : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  rw [FrameDegreeData.dmin_rmul X x hb, e, ← Matrix.mul_assoc,
    lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]
  have hc : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => FrameDegreeData.bdiag_ne X hb τ _
  generalize (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) = c at hc ⊢
  have hc' : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, mul_pow,
    ← mul_div_mul_right ‖dmin X.Gm x τ i‖ _ hc']
  congr 1
  ring
end GlobalTheory.FramePotential
