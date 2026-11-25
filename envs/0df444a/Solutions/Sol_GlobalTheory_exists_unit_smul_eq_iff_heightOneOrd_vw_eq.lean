-- Prove2me | solution 1 for GlobalTheory.exists_unit_smul_eq_iff_heightOneOrd_vw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:12:48.40581+00:00
-- url     : https://prove2.me/submissions/87703106-ef59-4028-a294-658cd65ad72a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_exists_smul_eq_iff_heightOneOrd_vw_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ u : Aˣ, u • y = x) ↔ ∀ (p : Ideal A) [p.IsPrime] (hp : p.height = 1),
      heightOneOrd_vw p hp x = heightOneOrd_vw p hp y := by
  constructor
  · rintro ⟨u, hu⟩ p _ hp
    have hu' : ((u⁻¹ : Aˣ) : A) • x = y := by rw [← hu, ← Units.smul_def, inv_smul_smul]
    exact le_antisymm
      ((exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hy hx).mp ⟨_, hu'⟩ p hp)
      ((exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hx hy).mp ⟨u, hu⟩ p hp)
  · intro h
    obtain ⟨a, ha⟩ := (exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hx hy).mpr
      fun p _ hp => (h p hp).ge
    obtain ⟨b, hb⟩ := (exists_smul_eq_iff_heightOneOrd_vw_le (A := A) hy hx).mpr
      fun p _ hp => (h p hp).le
    have hab : a * b = 1 := by
      apply IsFractionRing.injective A K
      apply mul_right_cancel₀ hx
      rw [← Algebra.smul_def, mul_smul, hb, ha, map_one, one_mul]
    exact ⟨Units.mkOfMulEqOne a b hab, ha⟩
end GlobalTheory
