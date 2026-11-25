-- Prove2me | solution 1 for GlobalTheory.PlaceTransport.intValuation_comap_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:39.188813+00:00
-- url     : https://prove2.me/submissions/7b93c338-bfbd-4797-9c4f-a6d27c4b3aff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinitePlaceValuationCompRingEquiv
import Theorems.Thm_GlobalTheory_PlaceTransport_eq_of_forall_le_exp_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.PlaceTransport
namespace GlobalTheory.PlaceTransport
theorem _root_.solution {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hfx : f x ≠ 0 := by simpa using hx
  refine eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx)
    (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x)
    (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n
  have hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R) := fun J =>
    (Ideal.map_comap_of_equiv f.symm).symm
  rw [hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]
  rfl
end GlobalTheory.PlaceTransport
