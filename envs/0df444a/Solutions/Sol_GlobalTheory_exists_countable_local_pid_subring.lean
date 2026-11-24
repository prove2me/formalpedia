-- Prove2me | solution 1 for GlobalTheory.exists_countable_local_pid_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:06.268936+00:00
-- url     : https://prove2.me/submissions/6b6150c8-931c-4fc3-aec0-e577a9cf4dae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCountableLocalPidSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] (S : Set R) (hS : S.Countable) :
    ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀),
      Countable R₀ ∧ S ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ Module.FaithfullyFlat R₀ R := by
  classical
  let K := FractionRing R
  let K₀ : Subfield K := Subfield.closure (algebraMap R K '' S)
  let R₀ : Subring R := K₀.toSubring.comap (algebraMap R K)
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ x : R, x ∈ R₀ ↔ algebraMap R K x ∈ K₀ := fun x => Iff.rfl
  have hdvd : ∀ a b : R₀, (a : R) ∣ (b : R) → a ∣ b := by
    rintro a b ⟨c, hc⟩
    by_cases ha : (a : R) = 0
    · have : b = 0 := Subtype.ext (by rw [hc, ha]; simp)
      rw [this]; exact dvd_zero _
    · have ha' : algebraMap R K a ≠ 0 := fun h => ha (hinj (by simpa using h))
      have hcm : c ∈ R₀ := by
        rw [hmem]
        have : algebraMap R K c = algebraMap R K b / algebraMap R K a := by
          rw [hc, map_mul, mul_div_cancel_left₀ _ ha']
        rw [this]
        exact K₀.div_mem ((hmem _).1 b.2) ((hmem _).1 a.2)
      exact ⟨⟨c, hcm⟩, Subtype.ext hc⟩
  have hloc : IsLocalHom R₀.subtype := ⟨fun a ha => by
    rw [isUnit_iff_dvd_one] at ha ⊢
    exact hdvd a 1 ha⟩
  have hlr : IsLocalRing R₀ := RingHom.domain_isLocalRing R₀.subtype
  have hpid : IsPrincipalIdealRing R₀ := ⟨fun I => by
    obtain ⟨M, ⟨a, haI, rfl⟩, hM⟩ := set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian R R)
      {J : Ideal R | ∃ a : R₀, a ∈ I ∧ Ideal.span {(a : R)} = J} ⟨_, 0, I.zero_mem, rfl⟩
    refine ⟨⟨a, le_antisymm (fun b hb => ?_) ?_⟩⟩
    · change b ∈ Ideal.span {a}
      rw [Ideal.mem_span_singleton]
      apply hdvd
      rcases ValuationRing.dvd_total (a : R) (b : R) with h | h
      · exact h
      · have h1 : Ideal.span {(a : R)} ≤ Ideal.span {(b : R)} :=
          Ideal.span_singleton_le_span_singleton.mpr h
        have h2 := hM _ ⟨b, hb, rfl⟩
        exact Ideal.span_singleton_le_span_singleton.mp (eq_of_le_of_not_lt h1 h2).ge
    · exact (Ideal.span_singleton_le_iff_mem I).mpr haI⟩
  have hK : Countable K₀ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max _).trans (max_le ?_ le_rfl)
    rw [Cardinal.mk_le_aleph0_iff]
    exact (hS.image _).to_subtype
  have hc : Countable R₀ := by
    let f : R₀ → K₀ := fun x => ⟨algebraMap R K x, (hmem _).1 x.2⟩
    have : Function.Injective f := fun x y h =>
      Subtype.ext (hinj (congrArg Subtype.val h))
    exact this.countable
  refine ⟨R₀, hlr, hpid, hc, fun x hx => Subfield.subset_closure ⟨x, hx, rfl⟩, hloc, ?_⟩
  have : IsLocalHom (algebraMap R₀ R) := hloc
  have : Module.Flat R₀ R := inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom
end GlobalTheory
