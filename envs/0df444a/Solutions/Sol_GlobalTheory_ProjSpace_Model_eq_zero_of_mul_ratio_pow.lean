-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.eq_zero_of_mul_ratio_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:17.901459+00:00
-- url     : https://prove2.me/submissions/f6e34ca9-ef95-466c-b44d-7fe51c21bc0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_Model_exists_formOn
import Theorems.Thm_GlobalTheory_ProjSpace_Model_resG_overlap_injective
import Theorems.Thm_GlobalTheory_ProjSpace_formOn_chart_inj
import Theorems.Thm_GlobalTheory_ProjSpace_formOn_zero
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
theorem _root_.solution {i j : Fin (N + 1)} (hij : j ≠ i) (k : ℕ) {U : (PSpace R N).Opens}
    (hi : U ≤ chart R N i) (hj : U ≤ chart R N j) (hU : U = chart R N i ⊓ chart R N j)
    (u : Γ(PSpace R N, chart R N i)) (v : Γ(PSpace R N, chart R N j))
    (h : resG _ hi u * ratioOn U i hi j ^ (k + 1) = resG _ hj v) : u = 0 := by
  obtain ⟨a, F, hF, rfl⟩ := exists_formOn i u
  obtain ⟨b, G, hG, rfl⟩ := exists_formOn j v
  have hL : (F * X j ^ (k + 1 + b)).IsHomogeneous (a + (k + 1 + b)) := hF.mul (isHomogeneous_X_pow _ _)
  have hR : (G * X i ^ (a + k + 1)).IsHomogeneous (a + (k + 1 + b)) := by
    have := hG.mul (isHomogeneous_X_pow (R := R) i (a + k + 1))
    rwa [show b + (a + k + 1) = a + (k + 1 + b) by ring] at this
  have key : F * X j ^ (k + 1 + b) = G * X i ^ (a + k + 1) := by
    refine (formOn_chart_inj R N i hL hR).1 (resG_overlap_injective i j hi hU ?_)
    rw [resG_formOn, resG_formOn]
    rw [resG_formOn, resG_formOn] at h
    have e1 : formOn U i hi (a + (k + 1 + b)) _ hL =
        formOn U i hi a F hF * ratioOn U i hi j ^ (k + 1) * ratioOn U i hi j ^ b := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X]; ring
    have e2 : formOn U i hi (a + (k + 1 + b)) _ hR = formOn U i hi b G hG := by
      simp only [formOn_eq_aeval, map_mul, map_pow, aeval_X, ratioOn_self]; ring
    rw [e1, e2, h, formOn_eq_ratioOn_pow_mul (hi := hi) hj hG, mul_comm]
  have hF0 : F = 0 := by
    ext m
    by_contra hm
    have hdeg := hF hm
    have hle : m i ≤ a := by
      rw [← hdeg]
      exact Finsupp.le_weight _ (s := i) one_ne_zero m
    have := congrArg (coeff (m + Finsupp.single j (k + 1 + b))) key
    rw [X_pow_eq_monomial, X_pow_eq_monomial, coeff_mul_monomial, coeff_mul_monomial', if_neg] at this
    · exact hm (by simpa using this)
    · intro hle'
      have := hle' i
      simp [Finsupp.single_apply, hij] at this
      omega
  subst hF0
  exact formOn_zero
end GlobalTheory.ProjSpace.Model
