-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.unit_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:45.882747+00:00
-- url     : https://prove2.me/submissions/abd37f76-0a58-4749-8233-95201d72488d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution [IsLocalRing O] {β : O} (hβ : ¬IsUnit β) {a y : O} (ha : IsUnit a)
    (hy : β ∣ y) (z : O) : IsUnit (a - z * y) := by
  have hm : z * y ∈ IsLocalRing.maximalIdeal O := by
    obtain ⟨t, rfl⟩ := hy
    exact Ideal.mul_mem_left _ z
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hβ)))
  by_contra h
  have h2 : a - z * y ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have h3 : a ∈ IsLocalRing.maximalIdeal O := by simpa using Ideal.add_mem _ h2 hm
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h3) ha
end GlobalTheory.UnipotentBorder
