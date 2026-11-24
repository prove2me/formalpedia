-- Prove2me | solution 1 for GlobalTheory.exists_sup_maximalIdeal_pow_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:46:54.343071+00:00
-- url     : https://prove2.me/submissions/183a4a6f-5c70-4be7-a7b8-a9c9b7b56013

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R]
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing R] [IsLocalRing R]
    (J : ℕ → Ideal R) (hJ : Antitone J) (k : ℕ) :
    ∃ m, ∀ m' ≥ m, J m' ⊔ maximalIdeal R ^ k = J m ⊔ maximalIdeal R ^ k := by
  have hdim : Ring.KrullDimLE 0 (R ⧸ maximalIdeal R ^ k) := by
    rw [Ring.krullDimLE_zero_iff]
    intro Q hQ
    have h1 : maximalIdeal R ^ k ≤ Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k)) :=
      fun x hx ↦ by simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    have h2 : maximalIdeal R = Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k)) :=
      (maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.IsPrime.le_of_pow_le h1)
    have h3 : (Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))).IsMaximal :=
      h2 ▸ maximalIdeal.isMaximal R
    have h4 := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (maximalIdeal R ^ k)) Ideal.Quotient.mk_surjective
      (m := Q.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))) (by simpa using h1)
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h4
  have hart : IsArtinianRing (R ⧸ maximalIdeal R ^ k) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_artinian.2 hart
    ⟨fun n ↦ OrderDual.toDual ((J n).map (Ideal.Quotient.mk (maximalIdeal R ^ k))),
      fun a b hab ↦ Ideal.map_mono (hJ hab)⟩
  refine ⟨m, fun m' hm' ↦ ?_⟩
  have h : (J m).map (Ideal.Quotient.mk (maximalIdeal R ^ k)) =
      (J m').map (Ideal.Quotient.mk (maximalIdeal R ^ k)) := hm m' hm'
  have := congrArg (Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ k))) h
  simpa [Ideal.comap_map_quotientMk, sup_comm] using this.symm
end GlobalTheory
