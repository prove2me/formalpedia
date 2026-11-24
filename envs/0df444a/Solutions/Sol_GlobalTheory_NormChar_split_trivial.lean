-- Prove2me | solution 1 for GlobalTheory.NormChar.split_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:38.847186+00:00
-- url     : https://prove2.me/submissions/08469ad8-ae16-4e9a-9bb7-75dcfd4f2fca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotForallExistsTwoLiesOverAbsNormEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOne
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_T_ncard_primesOver_eq_finrank_of_trivial_frobenius
import Theorems.Thm_GlobalTheory_T_not_forall_exists_two_degree_one_primes_over
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.NormChar
namespace GlobalTheory.NormChar
theorem _root_.solution (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M,
      x ^ Ideal.absNorm v.asIdeal - x ∈ P) : Module.finrank K M = 1 := by
  by_contra h1
  have h2 : 1 < Module.finrank K M := by have := Module.finrank_pos (R := K) (M := M); omega
  obtain ⟨T, hT, hc⟩ := GlobalTheory.T.ncard_primesOver_eq_finrank_of_trivial_frobenius K M
  refine GlobalTheory.T.not_forall_exists_two_degree_one_primes_over K M (S ∪ T) (hS.union hT) fun v hv => ?_
  simp only [Set.mem_union, not_or] at hv
  obtain ⟨hn, hN⟩ := hc v hv.2 (h v hv.1)
  rw [← hn] at h2
  have := v.isMaximal
  obtain ⟨P, P', hP, hP', hne⟩ := (Set.one_lt_ncard_iff (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M))).1 h2
  have := hP.2
  have := hP'.2
  exact ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ⟨P', hP'.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P'⟩,
    fun e => hne (congrArg HeightOneSpectrum.asIdeal e), hP.2, hP'.2, hN P hP, hN P' hP'⟩
end GlobalTheory.NormChar
