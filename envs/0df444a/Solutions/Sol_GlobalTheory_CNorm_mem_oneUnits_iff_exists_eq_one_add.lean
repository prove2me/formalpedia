-- Prove2me | solution 1 for GlobalTheory.CNorm.mem_oneUnits_iff_exists_eq_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:53.915192+00:00
-- url     : https://prove2.me/submissions/17b46be1-452d-4a29-a606-6165197a6ba3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  unfold oneUnits
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 ↔ _
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [← hx]; ring⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx]; ring⟩
end GlobalTheory.CNorm
