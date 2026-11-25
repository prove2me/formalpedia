-- Prove2me | solution 1 for GlobalTheory.IntBallMinorOne.norm_det_le_add_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:51:37.416318+00:00
-- url     : https://prove2.me/submissions/ebd6ad15-e603-4f09-b543-508d157abf6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.IntBallMinorOne
theorem _root_.solution {k : ℕ} (P : Matrix (Fin k) (Fin k) ℂ) (hP : P.PosSemidef)
    (v : Fin k → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖P.det‖ ≤ ‖(P + (c : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v))).det‖ := by
  by_cases hu : IsUnit P.det
  · have hPD : P.PosDef := hP.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 hu)
    have hinv : (P⁻¹).PosSemidef := hPD.inv.posSemidef
    have e : (c : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v)) =
        replicateCol (Fin 1) ((c : ℂ) • v) * replicateRow (Fin 1) (star v) := by
      ext i j; simp [Matrix.mul_apply, mul_assoc]
    have h1 : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + replicateRow (Fin 1) (star v) * P⁻¹ *
        replicateCol (Fin 1) ((c : ℂ) • v)).det = 1 + (c : ℂ) * (star v ⬝ᵥ P⁻¹ *ᵥ v) := by
      rw [Matrix.det_fin_one]
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      rw [Finset.sum_comm]
    rw [e]
    erw [det_add_replicateCol_mul_replicateRow (ι := Fin 1) hu]
    rw [norm_mul]
    erw [h1]
    have hre : 0 ≤ (star v ⬝ᵥ P⁻¹ *ᵥ v).re := by
      have := hinv.re_dotProduct_nonneg v
      simpa using this
    have h2 : 1 ≤ ‖(1 : ℂ) + (c : ℂ) * (star v ⬝ᵥ P⁻¹ *ᵥ v)‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith
    have h3 : 0 ≤ ‖P.det‖ := norm_nonneg _
    nlinarith
  · have : P.det = 0 := by simpa using hu
    rw [this, norm_zero]; exact norm_nonneg _
end GlobalTheory.IntBallMinorOne
