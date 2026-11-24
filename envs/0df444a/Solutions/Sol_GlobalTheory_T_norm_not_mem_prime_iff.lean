-- Prove2me | solution 1 for GlobalTheory.T.norm_not_mem_prime_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:37.180076+00:00
-- url     : https://prove2.me/submissions/5cb69bd4-149c-420d-8dd4-7643cfa8924f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIff
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_NormNotMemPrimeIffStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_NormPrime_norm_notMem_iff


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (e : B) (p : Ideal A), p.IsPrime → (Algebra.norm A e ∉ p ↔ ∀ q : Ideal B, q.IsPrime → q.comap (algebraMap A B) = p → e ∉ q) := by
  first | exact @GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff | exact GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff | (intros; apply GlobalTheory.CompanionTheory.NormPrime.norm_notMem_iff <;> assumption)
end _root_.GlobalTheory.T
