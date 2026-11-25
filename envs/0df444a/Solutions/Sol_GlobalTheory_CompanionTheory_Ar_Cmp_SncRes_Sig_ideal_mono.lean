-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig.ideal_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:51.711677+00:00
-- url     : https://prove2.me/submissions/38dae389-13dc-46fd-88cd-7721177ee9ab

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
theorem _root_.solution {S S' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h : S ≤ S') (p : (k : K) → ι k) :
    SncRes.ideal S p ≤ SncRes.ideal S' p :=
  Ideal.map_mono (sup_le_sup_right h _)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Sig
