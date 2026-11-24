-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:34.607941+00:00
-- url     : https://prove2.me/submissions/5cf41f60-a4ea-4221-b8c7-dcf1f3960787

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDomainAndIsIntegrallyClosedAtPrimeTensorFieldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {D C : Type*} [CommRing D]
    [CommRing C] (e : D ≃+* C)
    (h : ∀ (q : Ideal D) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (q : Ideal C) [hq : q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let q' : Ideal D := q.comap (e : D →+* C)
  haveI : q'.IsPrime := Ideal.comap_isPrime _ _
  have H : q'.primeCompl.map e.toMonoidHom = q.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, q', Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e.symm x, by simpa using hx, by simp⟩
  let f : Localization.AtPrime q' ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q') (Localization.AtPrime q) e H
  obtain ⟨h1, h2⟩ := h q'
  exact ⟨f.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv f⟩
end GlobalTheory
