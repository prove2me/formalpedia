-- Prove2me | solution 1 for GlobalTheory.ThetaBound.norm_polyDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:43.403897+00:00
-- url     : https://prove2.me/submissions/4f83198d-33ae-4321-b21b-16da4562ae0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_GlobalTheory_Jet_card_toMultiset_eq_degree
import Theorems.Thm_GlobalTheory_Jet_degree_eq_of_mem_support
import Theorems.Thm_GlobalTheory_Jet_norm_polyDeriv_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
variable {ι : Type} [Fintype ι]
open Classical
namespace GlobalTheory.ThetaBound
theorem _root_.solution (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) F 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  swap
  · exact Jet.norm_polyDeriv_le q hq F hF S hS P a hP
  simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] at hS
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h := Jet.norm_polyDeriv_le 1 le_rfl F hF S (fun v => ?_) P 0 hP
    · simpa using h
    · refine le_trans ?_ (hS v)
      refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
      have := Real.pi_pos
      have : 0 ≤ ((1 : ℕ) : ℝ) * Real.pi * ‖v‖ ^ 2 := by positivity
      linarith
  · have hb : Bornology.IsBounded (Set.range F) := by
      refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt S, ?_⟩
      rintro _ ⟨v, rfl⟩
      exact Real.le_sqrt_of_sq_le (hS v)
    obtain ⟨c, hc⟩ := hF.exists_eq_const_of_bounded hb
    have h0 : polyDeriv P (fun i => EuclideanSpace.single i (1 : ℂ)) F 0 = 0 := by
      unfold polyDeriv
      refine Finset.sum_eq_zero fun m hm => ?_
      have hne : Multiset.card (Finsupp.toMultiset m) ≠ 0 := by
        rw [Jet.card_toMultiset_eq_degree, Jet.degree_eq_of_mem_support hP hm]
        omega
      rw [hc, show Function.const (EuclideanSpace ℂ ι) c = fun _ => c from rfl,
        iteratedFDeriv_const_of_ne hne]
      simp
    rw [h0, norm_zero]
    positivity
end GlobalTheory.ThetaBound
