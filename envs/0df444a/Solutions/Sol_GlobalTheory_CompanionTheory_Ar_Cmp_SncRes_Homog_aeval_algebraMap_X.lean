-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.aeval_algebraMap_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:34:02.022127+00:00
-- url     : https://prove2.me/submissions/687a5b30-1803-419d-a012-932e0ba94d6d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerInAffineChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {L : Type} [CommRing L] [Algebra ℂ L] [Algebra (MvPolynomial (Σ k, ι k) ℂ) L]
  [IsScalarTower ℂ (MvPolynomial (Σ k, ι k) ℂ) L]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
theorem _root_.solution (g : MvPolynomial (Σ k, ι k) ℂ) :
    aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) g =
      algebraMap (MvPolynomial (Σ k, ι k) ℂ) L g := by
  have : aeval (fun q => algebraMap (MvPolynomial (Σ k, ι k) ℂ) L (X q)) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ) L :=
    MvPolynomial.algHom_ext fun q => by simp
  exact DFunLike.congr_fun this g
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog
