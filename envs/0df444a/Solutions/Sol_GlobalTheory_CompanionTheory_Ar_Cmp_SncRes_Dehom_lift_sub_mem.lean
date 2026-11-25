-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.lift_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:29.107664+00:00
-- url     : https://prove2.me/submissions/dd53004e-e5ac-4c36-bd29-f3c5091dc059

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerFromAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Dehom_ren_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_exists_blockComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_isMultiHomogIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
theorem _root_.solution (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (q : Σ k, ι k) :
    lift p q - renR (Σ k, ι k) (X q) ∈ ideal S p := by
  classical
  obtain ⟨k, i⟩ := q
  unfold lift
  split_ifs with h
  · simp only at h
    subst h
    have hm : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ ReciprocityTheory.AnForm.R.chartIdeal S p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have h2 : renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ ideal S p := ren_mem hm
    have h3 := (ideal S p).neg_mem h2
    rw [map_sub, map_one, neg_sub] at h3
    exact h3
  · have : renR (Σ k, ι k) (X (⟨k, i⟩ : Σ k, ι k)) = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
      simp [renameEquiv_apply]
    rw [this, sub_self]
    exact zero_mem _
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
