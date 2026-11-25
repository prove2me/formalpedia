-- Prove2me | solution 1 for GlobalTheory.HypChartPf.exp_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:09.404032+00:00
-- url     : https://prove2.me/submissions/a17a397a-44f0-4a34-a998-b9460fdb814c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
import Theorems.Thm_GlobalTheory_HypChartPf_gen_semiconj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
private lemma exp_conjTranspose_mul_mul_exp_of_skew {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ)
    (hU : IsUnit U) (h : U * -X = Xᴴ * U) : (NormedSpace.exp X)ᴴ * U * NormedSpace.exp X = U := by
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have h1 : Xᴴ = U * -X * U⁻¹ := by rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hU]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hdet, h3, Matrix.mul_one]
private lemma exp_opGen_conjTranspose_mul_diagonal_mul (k r : ℕ) (q : TrE k) (u : ℂ) (hu : u ≠ 0) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) *
      NormedSpace.exp (opGen k r q) = Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) := by
  have hsemi := gen_semiconj k r q
  unfold SemiconjBy at hsemi
  have hent : ∀ i j, sgn k r i * -opGen k r q i j = star (opGen k r q j i) * sgn k r j := by
    intro i j
    have := congrFun (congrFun hsemi i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply] at this
  have hz : ∀ i j, sgn k r i = 0 → opGen k r q i j = 0 ∧ opGen k r q j i = 0 := by
    intro i j hi
    unfold sgn at hi
    split_ifs at hi with h1 h2
    · norm_num at hi
    · norm_num at hi
    · unfold opGen
      constructor <;> split_ifs <;> rfl
  apply exp_conjTranspose_mul_mul_exp_of_skew
  · refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    split_ifs with h
    · exact hu
    · exact h
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
    by_cases hi : sgn k r i = 0
    · obtain ⟨h1, h2⟩ := hz i j hi
      simp [h1, h2]
    by_cases hj : sgn k r j = 0
    · obtain ⟨h1, h2⟩ := hz j i hj
      simp [h1, h2]
    simp only [if_neg hi, if_neg hj]
    exact hent i j
end GlobalTheory.HypChartPf
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
namespace GlobalTheory.HypChartPf
theorem _root_.solution (k r : ℕ) (q : TrE k) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (sgn k r) * NormedSpace.exp (opGen k r q) =
      Matrix.diagonal (sgn k r) := by
  have hD : Matrix.diagonal (sgn k r) = (1 / 2 : ℂ) •
      (Matrix.diagonal (fun i => if sgn k r i = 0 then 1 else sgn k r i) +
        Matrix.diagonal (fun i => if sgn k r i = 0 then -1 else sgn k r i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      split_ifs with h <;> [rw [h]; skip] <;> ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    exp_opGen_conjTranspose_mul_diagonal_mul k r q 1 one_ne_zero, exp_opGen_conjTranspose_mul_diagonal_mul k r q (-1) (neg_ne_zero.2 one_ne_zero)]
end GlobalTheory.HypChartPf
