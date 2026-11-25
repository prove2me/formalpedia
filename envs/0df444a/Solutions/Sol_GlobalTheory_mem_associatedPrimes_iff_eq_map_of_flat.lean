-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_iff_eq_map_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:25.771934+00:00
-- url     : https://prove2.me/submissions/cf712c06-8a8e-4750-a790-72fadd6ae404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_of_flat
import Theorems.Thm_GlobalTheory_ker_includeRight_fiber

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] (q : Ideal B) [hq : q.IsPrime]
    [NoZeroDivisors ((q.under A).Fiber B)] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      q = (q.under A).map (algebraMap A B) := by
  rw [mem_associatedPrimes_iff_of_flat (A := A), and_congr_right_iff,
    ← ker_includeRight_fiber (q.under A)]
  intro _
  constructor
  · rintro ⟨Q, ⟨hQ, x, hx⟩, h⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hQ.ne_top (by simp [hx])
    have : Q = ⊥ := by
      rw [eq_bot_iff, hx]
      rintro y ⟨n, hn⟩
      simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot, mul_eq_zero, hx0,
        or_false] at hn
      exact eq_zero_of_pow_eq_zero hn
    rw [RingHom.ker_eq_comap_bot, ← this, h]
  · intro h
    have : Nontrivial ((q.under A).Fiber B) := by
      refine ⟨1, 0, fun h1 ↦ hq.ne_top ?_⟩
      rw [Ideal.eq_top_iff_one, h, RingHom.mem_ker, map_one, h1]
    have := NoZeroDivisors.to_isDomain ((q.under A).Fiber B)
    refine ⟨⊥, ⟨Ideal.isPrime_bot, 1, ?_⟩, by rw [← RingHom.ker_eq_comap_bot, ← h]⟩
    rw [eq_comm, eq_bot_iff]
    rintro y ⟨n, hn⟩
    simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot, mul_one] at hn
    exact eq_zero_of_pow_eq_zero hn
end GlobalTheory
