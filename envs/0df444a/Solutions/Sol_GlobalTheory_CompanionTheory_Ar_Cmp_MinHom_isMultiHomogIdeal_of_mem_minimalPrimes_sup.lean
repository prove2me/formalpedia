-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:29:33.004363+00:00
-- url     : https://prove2.me/submissions/ffd2db5c-878d-4b96-8275-35a189817cb8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_isMultiHomogIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_mem_minimalPrimes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isMultiHomogIdeal_of_isHomogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
open MvPolynomial ReciprocityTheory.AnForm.R
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
theorem _root_.solution :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by
  intro K _ ι _ P D hP hD Q hQ
  classical
  have toGeo : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), IsMultiHomogIdeal I →
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) I := fun I h => h
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := ℂ) (ι := ι) Q :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_isHomogeneous fun k =>
      ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes _
        ((ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo P hP) k).sup
          (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal (toGeo D hD) k)) hQ
  exact hQ'
end GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
