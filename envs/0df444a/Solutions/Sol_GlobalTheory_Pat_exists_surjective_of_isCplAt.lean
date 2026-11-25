-- Prove2me | solution 1 for GlobalTheory.Pat.exists_surjective_of_isCplAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:34.820137+00:00
-- url     : https://prove2.me/submissions/90ef934b-dba2-4ddc-9d8f-93e6fe21e1d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompletionUniqueUpToIsoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveOfIsCplAt
import Theorems.Thm_GlobalTheory_Pat_flat_quotientMap_map
import Theorems.Thm_GlobalTheory_Pat_PhiFin_of_surjective
import Theorems.Thm_GlobalTheory_T_completion_unique_up_to_iso
import Theorems.Thm_GlobalTheory_isAdicComplete_map_of_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Pat
namespace GlobalTheory.Pat
theorem _root_.solution : ∀ (R R' S S' : Type) [CommRing R] [IsNoetherianRing R] [CommRing R'] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (π : R →+* R') (q' : Ideal R') [q'.IsPrime] (φ : R →+* S) (φ' : R' →+* S'), Function.Surjective π → IsCplAt (q'.comap π) φ → IsCplAt q' φ' → ∃ θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = φ'.comp π ∧ Function.Surjective θ ∧ RingHom.ker θ = (RingHom.ker π).map φ := by
  intro R R' S S' _ _ _ _ _ _ _ π q' _ φ φ' hπ h h'
  set J : Ideal S := (RingHom.ker π).map φ with hJ
  have hJm : J ≤ maximalIdeal S := by
    rw [h.max_eq]
    exact Ideal.map_mono (Ideal.ker_le_comap π)
  have hJt : J ≠ ⊤ := fun ht => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (ht ▸ hJm))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
  haveI : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI := h.noeth
  haveI := h.complete
  let ε : R' ≃+* R ⧸ RingHom.ker π := (RingHom.quotientKerEquivOfSurjective hπ).symm
  let ψ : R' →+* S ⧸ J :=
    (Ideal.quotientMap J φ Ideal.le_comap_map).comp (ε : R' →+* R ⧸ RingHom.ker π)
  have hψ : ∀ r, ψ (π r) = Ideal.Quotient.mk J (φ r) := by
    intro r
    have : ε (π r) = Ideal.Quotient.mk _ r := by
      apply ε.symm.injective
      simp [ε]
    simp [ψ, this]
  have hψ' : ψ.comp π = (Ideal.Quotient.mk J).comp φ := RingHom.ext hψ
  have hm : maximalIdeal (S ⧸ J) = (maximalIdeal S).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hmc : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S := by
    rw [hm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.2 hJm]
  have hc : IsCplAt q' ψ :=
    { noeth := inferInstance
      complete := by
        have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal S) (S ⧸ J)
        rwa [show algebraMap S (S ⧸ J) = Ideal.Quotient.mk J from rfl, ← hm] at this
      flat := (RingHom.Flat.of_bijective ε.bijective).comp (flat_quotientMap_map φ h.flat _)
      max_eq := by
        rw [hm, h.max_eq, Ideal.map_map, ← hψ', ← Ideal.map_map, Ideal.map_comap_of_surjective π hπ]
      comap_eq := by
        ext x
        obtain ⟨r, rfl⟩ := hπ x
        rw [Ideal.mem_comap, hψ, ← Ideal.mem_comap, hmc, ← Ideal.mem_comap, h.comap_eq, Ideal.mem_comap]
      res := by
        intro s
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
        obtain ⟨a, b, hb, hab⟩ := h.res s
        refine ⟨π a, π b, hb, ?_⟩
        rw [hψ, hψ, ← map_mul, ← map_sub, ← Ideal.mem_comap, hmc]
        exact hab }
  obtain ⟨e, he⟩ := GlobalTheory.T.completion_unique_up_to_iso R' (S ⧸ J) S' q' ψ φ' hc h'
  have hs : Function.Surjective ((e : S ⧸ J →+* S').comp (Ideal.Quotient.mk J)) :=
    e.surjective.comp Ideal.Quotient.mk_surjective
  refine ⟨(e : S ⧸ J →+* S').comp (Ideal.Quotient.mk J), IsLocalHom.of_surjective _ hs, ?_, hs, ?_⟩
  · rw [RingHom.comp_assoc, ← hψ', ← RingHom.comp_assoc, he]
  · ext s
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
end GlobalTheory.Pat
