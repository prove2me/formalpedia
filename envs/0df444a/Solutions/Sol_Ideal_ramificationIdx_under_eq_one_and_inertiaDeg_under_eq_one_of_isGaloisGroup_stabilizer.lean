-- Prove2me | solution 1 for Ideal.ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/38931471-019e-5274-ae0d-203ab8bfd93f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer

set_option autoImplicit false

universe u

open scoped Pointwise

theorem solution
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
    [Algebra A C] [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A B] [Algebra B C] [IsScalarTower A B C] [Module.Finite B C] [Module.IsTorsionFree B C]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G A C]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal C) [P.IsMaximal] [P.LiesOver p]
    [IsGaloisGroup ↥(MulAction.stabilizer G P) B C] :
    Ideal.ramificationIdx' p (P.under B) = 1 ∧ Ideal.inertiaDeg' p (P.under B) = 1 := by
  classical
  set q : Ideal B := P.under B with hq
  have hinjAC : Function.Injective (algebraMap A C) := FaithfulSMul.algebraMap_injective A C
  have hinjBC : Function.Injective (algebraMap B C) := FaithfulSMul.algebraMap_injective B C
  have hinjAB : Function.Injective (algebraMap A B) := by
    intro a b h
    apply hinjAC
    rw [IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_apply A B C, h]

  haveI : Algebra.IsIntegral B C := Algebra.IsIntegral.of_finite B C
  haveI hqmax : q.IsMaximal := Ideal.IsMaximal.under B P
  haveI : P.LiesOver q := ⟨rfl⟩
  haveI : q.LiesOver p := by
    constructor
    rw [hq, Ideal.under_under]
    exact Ideal.LiesOver.over
  have hq0 : q ≠ ⊥ := by
    intro h0
    apply hp
    have : q.under A = p := (Ideal.LiesOver.over (p := p) (P := q)).symm
    rw [← this, h0]
    exact Ideal.comap_bot_of_injective _ hinjAB

  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p C G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G, Ideal.inertiaDegIn_eq_inertiaDeg p P G,
    ← Algebra.IsInvariant.orbit_eq_primesOver A C G p P, ← MulAction.index_stabilizer] at h1
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := P) hp,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := p) (q := P)] at h1
  have hD1 : Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P = Nat.card ↥(MulAction.stabilizer G P) := by
    have hidx := (MulAction.stabilizer G P).index_mul_card
    have hne : (MulAction.stabilizer G P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
    rw [h1, hidx]

  have hPO : q.primesOver C = {P} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
    intro Q hQ
    haveI := hQ.1
    haveI := hQ.2
    obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup q P Q ↥(MulAction.stabilizer G P)
    rw [← hσ]
    show ((σ : G) • P) = P
    exact σ.2
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q C ↥(MulAction.stabilizer G P)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx q P ↥(MulAction.stabilizer G P),
    Ideal.inertiaDegIn_eq_inertiaDeg q P ↥(MulAction.stabilizer G P), hPO, Set.ncard_singleton, one_mul] at h2
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (p := q) (q := P) hq0,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := q) (q := P)] at h2

  have he := Ideal.ramificationIdx_algebra_tower (p := p) (P := q) (Q := P)
    (by rw [Ne, Ideal.map_eq_bot_iff_of_injective hinjBC]; exact hq0)
    (by rw [Ne, Ideal.map_eq_bot_iff_of_injective hinjAC]; exact hp)
    (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hf := Ideal.inertiaDeg_algebra_tower p q P

  have hne : Ideal.ramificationIdx' q P * Ideal.inertiaDeg' q P ≠ 0 := by
    rw [h2]; exact Nat.card_pos.ne'
  have h3 : Ideal.ramificationIdx' p P * Ideal.inertiaDeg' p P =
      Ideal.ramificationIdx' q P * Ideal.inertiaDeg' q P := hD1.trans h2.symm
  rw [he, hf] at h3
  have hprod : (Ideal.ramificationIdx' p q * Ideal.inertiaDeg' p q) *
      (Ideal.ramificationIdx' q P * Ideal.inertiaDeg' q P) =
      1 * (Ideal.ramificationIdx' q P * Ideal.inertiaDeg' q P) := by
    calc (Ideal.ramificationIdx' p q * Ideal.inertiaDeg' p q) * (Ideal.ramificationIdx' q P * Ideal.inertiaDeg' q P)
        = (Ideal.ramificationIdx' p q * Ideal.ramificationIdx' q P) * (Ideal.inertiaDeg' p q * Ideal.inertiaDeg' q P) := by ring
      _ = 1 * (Ideal.ramificationIdx' q P * Ideal.inertiaDeg' q P) := by rw [h3, one_mul]
  have h11 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) hprod
  exact ⟨Nat.eq_one_of_mul_eq_one_right h11, Nat.eq_one_of_mul_eq_one_left h11⟩

end S_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
end P2MW
export P2MW.S_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer (solution)
