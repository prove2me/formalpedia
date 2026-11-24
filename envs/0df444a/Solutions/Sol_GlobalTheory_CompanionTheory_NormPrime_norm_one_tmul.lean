-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NormPrime.norm_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:53:58.127465+00:00
-- url     : https://prove2.me/submissions/f45a15a3-8a42-4d0e-bbb3-e6af64a10bec

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
open TensorProduct
namespace GlobalTheory.CompanionTheory.NormPrime
theorem _root_.solution {A B K : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] [Field K] [Algebra A K] (e : B) :
    Algebra.norm K ((1 : K) ⊗ₜ[A] e : K ⊗[A] B) = algebraMap A K (Algebra.norm A e) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.CompanionTheory.NormPrime
