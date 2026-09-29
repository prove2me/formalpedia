-- Prove2me | solution 1 for Ideal.ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c425f622-8cc0-5de1-99fd-b871db730252

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [Module.Finite A B] [Module.IsTorsionFree A B] [Module.Finite C B] [Module.IsTorsionFree C B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) (hp : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [IsGaloisGroup (MulAction.stabilizer G P) C B] :
    p.ramificationIdx' (P.under C) = 1 ∧ p.inertiaDeg' (P.under C) = 1 := by
  classical
  set S : Subgroup G := MulAction.stabilizer G P with hS
  set q : Ideal C := P.under C with hq

  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  haveI : q.IsMaximal := Ideal.IsMaximal.under C P
  haveI hPq : P.LiesOver q := ⟨rfl⟩
  haveI : q.LiesOver p := ⟨by rw [hq, Ideal.under_under]; exact Ideal.LiesOver.over⟩
  have hqbot : q ≠ ⊥ := by
    intro h
    apply hPbot
    exact Ideal.eq_bot_of_comap_eq_bot (by simpa [hq, Ideal.under_def] using h)
  have hCB : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have hAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hmapq : Ideal.map (algebraMap C B) q ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hCB]
  have hmapp : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    rwa [Ne, Ideal.map_eq_bot_iff_of_injective hAB]
  have hmapq_le : Ideal.map (algebraMap C B) q ≤ P := Ideal.map_le_of_le_comap le_rfl

  have h1 : Nat.card S = p.ramificationIdxIn B * p.inertiaDegIn B := by
    have hG := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G p P, ← MulAction.index_stabilizer,
      ← (MulAction.stabilizer G P).index_mul_card] at hG
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hG).symm

  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q B S

  have h3 : (q.primesOver B).ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨P, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, hPq⟩, fun Q hQ => ?_⟩⟩
    haveI := Ideal.isPretransitive_of_isGaloisGroup q S (B := B)
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq S (⟨P, inferInstance, hPq⟩ : q.primesOver B) ⟨Q, hQ⟩
    have hσ' : (σ : G) • P = Q := by
      have := congrArg Subtype.val hσ
      exact this
    rw [← hσ']
    exact σ.2
  rw [h3, one_mul, h1, Ideal.ramificationIdxIn_eq_ramificationIdx q P S, Ideal.inertiaDegIn_eq_inertiaDeg q P S,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P G, Ideal.inertiaDegIn_eq_inertiaDeg p P G] at h2
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (p := q) (q := P) hqbot,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := q) (q := P),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := p) (q := P)] at h2

  have he : p.ramificationIdx' P = p.ramificationIdx' q * q.ramificationIdx' P :=
    Ideal.ramificationIdx_algebra_tower hmapq hmapp hmapq_le
  have hf : p.inertiaDeg' P = p.inertiaDeg' q * q.inertiaDeg' P := Ideal.inertiaDeg_algebra_tower p q P
  have he' : q.ramificationIdx' P ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmapq inferInstance hmapq_le
  have hf' : q.inertiaDeg' P ≠ 0 := Ideal.inertiaDeg_ne_zero q P

  rw [he, hf] at h2
  have hprod : p.ramificationIdx' q * p.inertiaDeg' q = 1 := by
    have h' : q.ramificationIdx' P * q.inertiaDeg' P * (p.ramificationIdx' q * p.inertiaDeg' q) =
        q.ramificationIdx' P * q.inertiaDeg' P * 1 := by
      rw [mul_one]
      calc q.ramificationIdx' P * q.inertiaDeg' P * (p.ramificationIdx' q * p.inertiaDeg' q)
          = p.ramificationIdx' q * q.ramificationIdx' P * (p.inertiaDeg' q * q.inertiaDeg' P) := by ring
        _ = q.ramificationIdx' P * q.inertiaDeg' P := h2.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero he' hf')) h'
  exact ⟨Nat.eq_one_of_mul_eq_one_right hprod, Nat.eq_one_of_mul_eq_one_left hprod⟩

end S_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
end P2MW
export P2MW.S_Ideal_ramificationIdx_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer (solution)
