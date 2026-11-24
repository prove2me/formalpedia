-- Prove2me | solution 1 for GlobalTheory.DedekindSmooth.exists_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:09:19.452805+00:00
-- url     : https://prove2.me/submissions/f6f068d8-cde3-4589-87f3-ee592875a493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DedekindSmooth
open Polynomial IsLocalRing
namespace GlobalTheory.DedekindSmooth
theorem _root_.solution (B : Type) [CommRing B] [IsDedekindDomain B] (q : Ideal B) [q.IsPrime]
    (hq : q ≠ ⊥) : ∃ t ∈ q, t ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq
    (Localization.AtPrime q)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨t, s⟩, h⟩ := IsLocalization.surj q.primeCompl π
  have hs : IsUnit (algebraMap B (Localization.AtPrime q) s) := IsLocalization.map_units _ s
  have hm : maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
    simp only at h
    rw [← h, Ideal.span_singleton_mul_right_unit hs, hπ.maximalIdeal_eq]
  refine ⟨t, ?_, ?_, hm⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, hm]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    simp only [map_zero] at h
    exact mul_ne_zero hπ.ne_zero hs.ne_zero h
end GlobalTheory.DedekindSmooth
