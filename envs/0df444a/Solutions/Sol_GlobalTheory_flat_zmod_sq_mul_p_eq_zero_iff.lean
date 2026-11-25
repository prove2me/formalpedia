-- Prove2me | solution 1 for GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:32.054211+00:00
-- url     : https://prove2.me/submissions/b0684cca-004e-4665-9aa8-acc9a44dad20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlatModPSquaredTorsion
import Theorems.Thm_GlobalTheory_zmod_sq_dvd_of_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B]
    (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  intro p hp B _ φ hφ w
  letI : Algebra (ZMod (p ^ 2)) B := φ.toAlgebra
  have hflat : Module.Flat (ZMod (p ^ 2)) B := hφ
  have hsmul : ∀ (r : ZMod (p ^ 2)) (b : B), r • b = φ r * b := fun r b => by
    rw [Algebra.smul_def]; rfl
  have hpB : φ (p : ZMod (p ^ 2)) = (p : B) := map_natCast φ p
  constructor
  · intro hw
    have hsum : ∑ i : Unit, (fun _ => (p : ZMod (p ^ 2))) i • (fun _ => w) i = 0 := by
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [hsmul, hpB, hw]
    have htr := @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (ZMod (p ^ 2)) B _ _ _ hflat Unit _ _ _ hsum
    obtain ⟨k, a, y, hy, ha⟩ := htr
    have ha' : ∀ j, (p : ZMod (p ^ 2)) * a () j = 0 := fun j => by
      simpa only [Finset.univ_unique, Finset.sum_singleton] using ha j
    choose c hc using fun j => zmod_sq_dvd_of_mul_eq_zero p (a () j) (ha' j)
    refine ⟨∑ j, φ (c j) * y j, ?_⟩
    have hw : w = ∑ j, a () j • y j := hy ()
    rw [hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsmul, hc j, map_mul, hpB, mul_assoc]
  · rintro ⟨v, rfl⟩
    have h2 : (((p ^ 2 : ℕ) : ZMod (p ^ 2))) = 0 := ZMod.natCast_self _
    have : ((p ^ 2 : ℕ) : B) = 0 := by
      rw [← map_natCast φ, h2, map_zero]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_two, this, zero_mul]
end GlobalTheory
