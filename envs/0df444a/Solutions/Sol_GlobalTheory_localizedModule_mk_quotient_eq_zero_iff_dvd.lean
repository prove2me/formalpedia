-- Prove2me | solution 1 for GlobalTheory.localizedModule_mk_quotient_eq_zero_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:06.25497+00:00
-- url     : https://prove2.me/submissions/24400bd8-6889-4a6c-81ef-5797bd43205f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePrimesDvdOfDvdMulLocalization

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
theorem _root_.solution {R : Type} [CommRing R] (M : Submonoid R)
    (s c : R) :
    LocalizedModule.mkLinearMap M (R ⧸ Ideal.span {s}) (Ideal.Quotient.mk _ c) = 0 ↔
      algebraMap R (Localization M) s ∣ algebraMap R (Localization M) c := by
  rw [IsLocalizedModule.eq_zero_iff M, ← Ideal.mem_span_singleton, ← Set.image_singleton,
    ← Ideal.map_span, IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  have key : ∀ m : R, m • (Ideal.Quotient.mk (Ideal.span {s}) c) = 0 ↔
      m * c ∈ Ideal.span {s} := by
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    rfl
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, m.2, (key m).1 hm⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, hm⟩, (key m).2 h⟩
end GlobalTheory
