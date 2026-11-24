-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.exists_form_of_eq_ratio_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:21.154603+00:00
-- url     : https://prove2.me/submissions/4bdf61fa-0bff-4677-97e3-fd15c36fa213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_Model_exists_formOn
import Theorems.Thm_GlobalTheory_ProjSpace_Model_resG_overlap_injective
import Theorems.Thm_GlobalTheory_ProjSpace_formOn_chart_inj
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_resG_formOn
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace GlobalTheory.ProjSpace.Model
variable {R : Type} [CommRing R] {N : ℕ}
namespace GlobalTheory.ProjSpace.Model
theorem _root_.solution {i j : Fin (N + 1)} (hij : j ≠ i) (n : ℕ) {U : (PSpace R N).Opens}
    (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) (hU : U = chart R N i ⊓ chart R N j)
    (u : Γ(PSpace R N, chart R N i)) (v : Γ(PSpace R N, chart R N j))
    (h : resG _ hi u = ratioOn U i hi j ^ n * resG _ hj v) :
    ∃ f, ∃ hf : (f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous n,
      u = formOn (chart R N i) i le_rfl n f hf := by
  obtain ⟨a, F, hF, rfl⟩ := exists_formOn i u
  obtain ⟨b, G, hG, rfl⟩ := exists_formOn j v
  have hH : (F * X i ^ n).IsHomogeneous (a + n) := hF.mul (isHomogeneous_X_pow _ _)
  have hL : (F * X i ^ n * X j ^ b).IsHomogeneous (a + n + b) := hH.mul (isHomogeneous_X_pow _ _)
  have hR : (G * X j ^ n * X i ^ a).IsHomogeneous (a + n + b) := by
    have := (hG.mul (isHomogeneous_X_pow (R := R) j n)).mul (isHomogeneous_X_pow (R := R) i a)
    rwa [show b + n + a = a + n + b by ring] at this
  have key : F * X i ^ n * X j ^ b = G * X j ^ n * X i ^ a := by
    refine (formOn_chart_inj R N i hL hR).1 (resG_overlap_injective i j hi hU ?_)
    rw [resG_formOn, resG_formOn]
    rw [resG_formOn, resG_formOn] at h
    have e1 : formOn U i hi (a + n + b) _ hL = formOn U i hi a F hF * ratioOn U i hi j ^ b := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]; ring
    have e2 : formOn U i hi (a + n + b) _ hR = formOn U i hi b G hG * ratioOn U i hi j ^ n := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]; ring
    rw [e1, e2, h, formOn_eq_ratioOn_pow_mul (hi := hi) hj hG]; ring
  have hmod : (F * X i ^ n).modMonomial (Finsupp.single i a) = 0 := by
    ext m
    by_cases hm : Finsupp.single i a ≤ m
    · rw [coeff_modMonomial_of_le _ hm, coeff_zero]
    · rw [coeff_modMonomial_of_not_le _ hm, coeff_zero]
      have := congrArg (coeff (m + Finsupp.single j b)) key
      rw [X_pow_eq_monomial (n := j) (e := b), X_pow_eq_monomial (n := i) (e := a), coeff_mul_monomial,
        coeff_mul_monomial', if_neg] at this
      · simpa using this
      · intro hle'
        have := hle' i
        simp [hij] at this
        exact hm (Finsupp.single_le_iff.2 this)
  have hdiv := divMonomial_add_modMonomial (F * X i ^ n) (Finsupp.single i a)
  rw [hmod, add_zero, ← X_pow_eq_monomial] at hdiv
  have hf : ((F * X i ^ n).divMonomial (Finsupp.single i a)).IsHomogeneous n := by
    intro m hm
    rw [coeff_divMonomial] at hm
    have := hH hm
    rw [map_add, Finsupp.weight_single] at this
    simpa using this
  refine ⟨_, hf, ?_⟩
  have := congrArg (aeval (R := R) (ratioOn (chart R N i) i le_rfl)) hdiv
  simp only [map_mul, map_pow, aeval_X, ratioOn_self, one_pow, one_mul, mul_one] at this
  rw [formOn_eq_aeval, formOn_eq_aeval, this]
end GlobalTheory.ProjSpace.Model
