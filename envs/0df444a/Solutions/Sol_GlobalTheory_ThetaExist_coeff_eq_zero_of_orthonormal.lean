-- Prove2me | solution 1 for GlobalTheory.ThetaExist.coeff_eq_zero_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:06.093027+00:00
-- url     : https://prove2.me/submissions/86018208-41e1-464e-9214-7757f005f3fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
noncomputable section
open GlobalTheory GlobalTheory.ThetaExist
namespace GlobalTheory.ThetaExist
theorem _root_.solution {C H κ : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : C →L[ℂ] H) (e : κ → C)
    (h : Orthonormal ℂ fun i => T (e i)) {c : κ → ℂ} (hs : HasSum (fun i => c i • e i) 0)
    (k : κ) : c k = 0 := by
  classical
  have h1 := ((innerSL ℂ (T (e k))).comp T).hasSum hs
  simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, map_zero,
    orthonormal_iff_ite.1 h, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
  have h2 : HasSum (fun i => if k = i then c i else 0) (c k) := by
    convert hasSum_ite_eq k (c k) using 2 with i
    by_cases hi : k = i
    · simp [hi]
    · simp [hi, Ne.symm hi]
  exact h2.unique h1
end GlobalTheory.ThetaExist
