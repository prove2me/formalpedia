-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_two_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:21.695004+00:00
-- url     : https://prove2.me/submissions/89fa3eee-1619-4770-a336-44c4a59bf76b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (T : Fin g → ℂ) {p : ℕ} (hp : p ≠ 0) : ∃ c, θ c ≠ 0 ∧ θ (T - p • c) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have hd : Differentiable ℂ fun c : Fin g → ℂ => θ (T - p • c) :=
    hθ.comp ((differentiable_const T).sub (differentiable_id.const_smul p))
  have han : AnalyticOnNhd ℂ (fun c : Fin g → ℂ => θ (T - p • c)) Set.univ :=
    fun x _ => ThetaJet.analyticAt_of_differentiable hd x
  have h := han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const (by
    filter_upwards [(isOpen_ne_fun hθ.continuous continuous_const).mem_nhds hx] with y hy
    exact hcon y hy)
  have h2 := congrFun h ((p : ℂ)⁻¹ • (T - x))
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hp), sub_sub_cancel] at h2
  exact hx h2
end GlobalTheory.ThetaTranslJet
