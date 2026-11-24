-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NormPrime.norm_mem_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:54:14.30528+00:00
-- url     : https://prove2.me/submissions/3984faec-8ecb-49ad-b640-b5e26f234453

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NormPrime
namespace GlobalTheory.CompanionTheory.NormPrime
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (e : B) (q : Ideal B) (he : e ∈ q) :
    Algebra.norm A e ∈ q.comap (algebraMap A B) := by
  set χ := (Algebra.lmul A B e).charpoly with hχ
  have h2 : Polynomial.aeval e χ = 0 := by
    apply Algebra.lmul_injective (R := A)
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact LinearMap.aeval_self_charpoly _
  have h3 := congrArg (Polynomial.aeval e) (Polynomial.divX_mul_X_add χ)
  rw [h2, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h3
  have h4 : algebraMap A B (χ.coeff 0) ∈ q := by
    have h5 : algebraMap A B (χ.coeff 0) = -(Polynomial.aeval e χ.divX * e) :=
      eq_neg_of_add_eq_zero_right h3
    rw [h5]
    exact q.neg_mem (q.mul_mem_left _ he)
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_comap.2 h4)
end GlobalTheory.CompanionTheory.NormPrime
