-- Prove2me | solution 1 for GlobalTheory.T.not_forall_exists_two_degree_one_primes_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:48.069306+00:00
-- url     : https://prove2.me/submissions/f21766b5-9037-4236-93d6-89308e9a325c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotForallExistsTwoLiesOverAbsNormEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotForallExistsTwoLiesOverAbsNormEqStatement
import Theorems.Thm_GlobalTheory_not_forall_exists_two_liesOver_absNorm_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq | exact GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq | (intros; apply GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq <;> assumption)
end _root_.GlobalTheory.T
