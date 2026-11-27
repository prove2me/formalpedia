-- Prove2me | solution 1 for GlobalTheory.locPullback_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:27.816367+00:00
-- url     : https://prove2.me/submissions/590b42d0-bd24-4d05-962c-6776f3d317d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMkOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalizationPreservesRingPullbackSquare

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
theorem _root_.solution {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (s : A) [IsLocalization.Away s LA] (φ : A →+* R)
    [IsLocalization.Away (φ s) LR] (Φ : LA →+* LR)
    (hΦ : Φ.comp (algebraMap A LA) = (algebraMap R LR).comp φ)
    (x : LR) (a₀ : A) (r : R) (j k e : ℕ) (he : j + k = e)
    (hx : x * algebraMap R LR (φ s ^ k) = algebraMap R LR r) (ha : φ a₀ = r * φ s ^ j) :
    Φ (IsLocalization.mk' LA a₀ (⟨s ^ e, e, rfl⟩ : Submonoid.powers s)) = x := by
  subst he
  have hΦ' : ∀ y, Φ (algebraMap A LA y) = algebraMap R LR (φ y) := fun y => RingHom.congr_fun hΦ y
  have hs := IsLocalization.mk'_spec LA a₀ (⟨s ^ (j + k), j + k, rfl⟩ : Submonoid.powers s)
  have h2 := congrArg Φ hs
  simp only [map_mul, hΦ'] at h2
  rw [ha, map_pow] at h2
  apply (IsLocalization.map_units LR (⟨φ s ^ (j + k), j + k, rfl⟩ : Submonoid.powers (φ s))).mul_left_inj.mp
  show _ * algebraMap R LR (φ s ^ (j + k)) = x * algebraMap R LR (φ s ^ (j + k))
  rw [h2, map_mul, ← hx, pow_add, map_mul]
  ring
end GlobalTheory
