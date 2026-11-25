-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig.renR_X_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:55:58.115514+00:00
-- url     : https://prove2.me/submissions/3bf40014-4516-4768-a7a5-91dc6072cbb6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRingAltBis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartRegularAtConePoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
theorem _root_.solution (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (k : K) :
    renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ SncRes.ideal S p :=
  Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
