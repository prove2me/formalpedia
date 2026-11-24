-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:48:32.87774+00:00
-- url     : https://prove2.me/submissions/0b2209c2-370d-4c74-bdc1-7290ea03bfef

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerLocal
namespace GlobalTheory.CompanionTheory.KerLocal
theorem _root_.solution :
    ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
      (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) →
      Module.Projective R (LinearMap.ker d) →
      (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) →
      ∀ (p : Ideal R) [p.IsPrime],
        Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.Finite (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧
        Module.finrank (Localization.AtPrime p)
          (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  intro R Q P _ _ _ _ _ d g hfin hproj hrk p _
  have hflat : Module.Flat R (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) p.primeCompl
  let e1 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LinearMap.ker (d.baseChange (Localization.AtPrime p)) :=
    LinearMap.tensorKerEquiv (Localization.AtPrime p) (Localization.AtPrime p) d
  let e2 : Localization.AtPrime p ⊗[R] LinearMap.ker d ≃ₗ[Localization.AtPrime p]
      LocalizedModule p.primeCompl (LinearMap.ker d) :=
    (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl (LinearMap.ker d))).equiv
  have hfree : Module.Free (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] LinearMap.ker d) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.Free.of_equiv e1, Module.Finite.equiv e1, ?_⟩
  rw [← e1.finrank_eq, e2.finrank_eq]
  exact hrk ⟨p, inferInstance⟩
end GlobalTheory.CompanionTheory.KerLocal
