-- Prove2me | solution 1 for GlobalTheory.finite_of_isClosed_torusZariski_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:04.173805+00:00
-- url     : https://prove2.me/submissions/fc230672-2a96-407c-8997-7f31c011235b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Theorems.Thm_GlobalTheory_finite_setOf_pow_eq_one_torus
import Theorems.Thm_GlobalTheory_exists_zpow_eq_one_of_isClosed_torusZariski

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]
variable [IsDomain R]
namespace GlobalTheory
theorem _root_.solution [Module.Finite ℤ X] {n : ℕ} (h2 : 2 ≤ n)
    [HasEnoughRootsOfUnity R n] {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    (hn : ∀ s ∈ H, s ^ n = 1 → s = 1) : Finite H ∧ (Nat.card H).Coprime n := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨r, hr, hrH⟩ := exists_zpow_eq_one_of_isClosed_torusZariski hH hn
  have hr0 : r.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    rintro rfl
    have := Int.natAbs_dvd_natAbs.2 hr
    simp only [Int.natAbs_natCast, zero_sub, Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one,
      Nat.dvd_one] at this
    omega
  have hfin : Finite H := (finite_setOf_pow_eq_one_torus (R := R) (X := X) hr0).subset
    (t := (H : Set (Multiplicative X →* Rˣ))) fun s hs => pow_natAbs_eq_one.2 (hrH s hs)
  refine ⟨hfin, Nat.coprime_of_dvd fun p hp hpH hpn => ?_⟩
  haveI := Fact.mk hp
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' p hpH
  have h1 : s ^ n = 1 := orderOf_dvd_iff_pow_eq_one.1 (hs ▸ hpn)
  have h3 : s = 1 := Subtype.ext (hn s s.2 (congrArg Subtype.val h1))
  rw [h3, orderOf_one] at hs
  exact hp.one_lt.ne hs
end GlobalTheory
