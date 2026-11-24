-- Prove2me | solution 1 for GlobalTheory.ProjSpace.Model.resG_overlap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:39.648892+00:00
-- url     : https://prove2.me/submissions/4e0695d2-baa4-4ecb-b3c2-39ea7c08f65f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsFormOfEqRatioPowMul
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_isAffineOpen_chart
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
theorem _root_.solution (i j : Fin (N + 1)) {U : (PSpace R N).Opens} (hi : U ≤ chart R N i)
    (hU : U = chart R N i ⊓ chart R N j) : Function.Injective (resG (PSpace R N) hi) := by
  have hb : (PSpace R N).basicOpen (ratio R N i j) = U := basicOpen_ratioOn.trans hU.symm
  subst hb
  have hl := (isAffineOpen_chart R N i).isLocalization_basicOpen (ratio R N i j)
  have hreg : ratio R N i j ∈ nonZeroDivisors _ := by
    by_cases h : j = i
    · subst h; rw [ratio, ratioOn_self]; exact one_mem _
    · rw [← chartAlgEquiv_X R N i ⟨j, h⟩]
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
      obtain ⟨p, rfl⟩ := (chartAlgEquiv R N i).surjective x
      rw [← map_mul, map_eq_zero_iff _ (chartAlgEquiv R N i).injective] at hx
      have : p = 0 := (isRegular_X (n := (⟨j, h⟩ : {k // k ≠ i}))).right (by simpa using hx)
      simp [this]
  exact IsLocalization.injective (M := Submonoid.powers (ratio R N i j))
    Γ(PSpace R N, (PSpace R N).basicOpen (ratio R N i j)) (Submonoid.powers_le.2 hreg)
end GlobalTheory.ProjSpace.Model
