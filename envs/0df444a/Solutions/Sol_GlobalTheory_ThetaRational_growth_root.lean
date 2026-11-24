-- Prove2me | solution 1 for GlobalTheory.ThetaRational.growth_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:43:34.558082+00:00
-- url     : https://prove2.me/submissions/97d6338d-06d8-4209-abe8-133668bce527

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_ThetaRational_growth_mv
import Theorems.Thm_GlobalTheory_ThetaRational_growth_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E : Type*} {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution (s : Polynomial (MvPolynomial (Fin n) ℂ)) (hs : s.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin n → ℂ) (y : ℂ),
      (s.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  obtain ⟨C, m, hC, h⟩ := growth_finite (ι := Fin s.natDegree) (fun x : Fin n → ℂ => 1 + ‖x‖)
    (fun x => by simp) (fun c x => MvPolynomial.eval x (s.coeff c)) fun c => growth_mv _
  refine ⟨C + 1, m, by positivity, fun x y hy => ?_⟩
  have hm := hs.map (MvPolynomial.eval x)
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hm.ne_zero hy
  have h0 : (0 : ℝ) ≤ C * (1 + ‖x‖) ^ m := by positivity
  have h2 : (s.map (MvPolynomial.eval x)).cauchyBound ≤ ⟨_, h0⟩ + 1 := by
    rw [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one, hs.natDegree_map]
    refine add_le_add ?_ le_rfl
    refine Finset.sup_le fun i hi => ?_
    rw [Polynomial.coeff_map]
    exact h x ⟨i, Finset.mem_range.1 hi⟩
  have h3 : ‖y‖ ≤ C * (1 + ‖x‖) ^ m + 1 := by exact_mod_cast (h1.le.trans h2)
  have h4 : (1 : ℝ) ≤ (1 + ‖x‖) ^ m := one_le_pow₀ (by simp)
  linarith
end GlobalTheory.ThetaRational
