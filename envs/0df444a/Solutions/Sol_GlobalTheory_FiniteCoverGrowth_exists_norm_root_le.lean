-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.exists_norm_root_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:13.674476+00:00
-- url     : https://prove2.me/submissions/85487531-5671-43ae-9519-cac045ac3934

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_exists_norm_eval_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic) :
    ∃ (K : ℝ) (M : ℕ), 0 ≤ K ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ K * (1 + ‖x‖) ^ M := by
  choose K M hK h using fun i : ℕ => exists_norm_eval_le (p.coeff i)
  refine ⟨∑ i ∈ Finset.range p.natDegree, K i + 1, ∑ i ∈ Finset.range p.natDegree, M i,
    add_nonneg (Finset.sum_nonneg fun i _ => hK i) zero_le_one, fun x y hy => ?_⟩
  have hm : (p.map (MvPolynomial.eval x)).Monic := hp.map _
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hm.ne_zero hy
  have h2 : (p.map (MvPolynomial.eval x)).cauchyBound ≤
      ∑ i ∈ Finset.range p.natDegree, ‖MvPolynomial.eval x (p.coeff i)‖₊ + 1 := by
    simp only [Polynomial.cauchyBound, hm.leadingCoeff, nnnorm_one, div_one,
      add_le_add_iff_right, hp.natDegree_map, Finset.sup_le_iff, Polynomial.coeff_map]
    intro i hi
    exact Finset.single_le_sum (f := fun i => ‖MvPolynomial.eval x (p.coeff i)‖₊)
      (fun _ _ => zero_le) hi
  have h3 : ‖y‖ ≤ ∑ i ∈ Finset.range p.natDegree, ‖MvPolynomial.eval x (p.coeff i)‖ + 1 := by
    have := NNReal.coe_le_coe.2 (h1.le.trans h2)
    simpa using this
  have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  refine h3.trans ?_
  rw [add_mul, Finset.sum_mul, one_mul]
  refine add_le_add (Finset.sum_le_sum fun i hi => (h i x).trans ?_) (one_le_pow₀ h0)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h0
    (Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) hi)) (hK i)
end GlobalTheory.FiniteCoverGrowth
