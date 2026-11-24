-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.not_isGen_O1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:36:13.232186+00:00
-- url     : https://prove2.me/submissions/31e46652-9d46-4a1b-9644-f76d27b32305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_Model_eq_zero_of_mul_ratio_pow
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
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
theorem _root_.solution [Nontrivial R] (t : (O1 R (N + 1)).Gen) : ¬ t.IsGen := by
  intro ht
  have h := ht (0 : Fin (N + 2)) (1 : Fin (N + 2))
  have h0 := eq_zero_of_mul_ratio_pow (R := R) (i := (0 : Fin (N + 2))) (j := 1) (by simp) 0
    inf_le_left inf_le_right rfl ((t.s (0 : Fin (N + 2)))⁻¹).val ((t.s (1 : Fin (N + 2)))⁻¹).val (by
      have aux : ∀ {G : Type} [CommGroup G] (a g b : G), a = g * b → a⁻¹ * g = b⁻¹ := by
        rintro G _ a g b rfl; simp
      have h' := aux _ _ _ h
      rw [← map_inv, ← map_inv] at h'
      rw [zero_add, pow_one]
      exact congrArg Units.val h')
  haveI : Nontrivial Γ(PSpace R (N + 1), chart R (N + 1) 0) :=
    (chartAlgEquiv R (N + 1) 0).symm.toEquiv.nontrivial
  exact Units.ne_zero _ h0
end GlobalTheory.ProjSpace.Model
