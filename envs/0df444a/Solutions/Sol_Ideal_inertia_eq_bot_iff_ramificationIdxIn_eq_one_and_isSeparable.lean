-- Prove2me | solution 1 for Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/53225cc5-e410-520b-a936-e068f03181f4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable

set_option autoImplicit false

open scoped Pointwise

namespace P2mInertiaTrivial

attribute [local instance] Ideal.Quotient.field

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  {p : Ideal A} (P : Ideal B)

theorem ramificationIdxIn_mul_inertiaDegIn_eq_card_stabilizer (hpb : p ≠ ⊥) [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] :
    p.ramificationIdxIn B * p.inertiaDegIn B = Nat.card (MulAction.stabilizer G P) := by
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G
  have h2 : (p.primesOver B).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hr : (p.primesOver B).ncard ≠ 0 := IsDedekindDomain.primesOver_ncard_ne_zero p B
  exact mul_left_cancel₀ hr (h1.trans h2.symm)

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B] in

theorem card_stabilizer_eq_card_inertia_mul_card_aut [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) := by
  have hq : Nat.card (MulAction.stabilizer G P ⧸ (P.inertia G).subgroupOf (MulAction.stabilizer G P))
      = Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← hq, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem inertia_eq_bot_iff (hpb : p ≠ ⊥) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] :
    P.inertia G = ⊥ ↔ p.ramificationIdxIn B = 1 ∧ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
  have hef := ramificationIdxIn_mul_inertiaDegIn_eq_card_stabilizer G P hpb
  have hDI := card_stabilizer_eq_card_inertia_mul_card_aut G P (p := p)
  have hf : p.inertiaDegIn B = Module.finrank (A ⧸ p) (B ⧸ P) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p P G, Ideal.inertiaDeg_eq_of_isMaximal p P]
  have he0 : p.ramificationIdxIn B ≠ 0 := Ideal.ramificationIdxIn_ne_zero G
  haveI : Module.Finite (A ⧸ p) (B ⧸ P) := inferInstance
  have hfpos : 0 < Module.finrank (A ⧸ p) (B ⧸ P) := Module.finrank_pos
  have haut_le : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) ≤ Module.finrank (A ⧸ p) (B ⧸ P) := by
    have h := AlgEquiv.card_le (F := A ⧸ p) (K := B ⧸ P)
    rwa [← Nat.card_eq_fintype_card] at h
  have hnormal : Normal (A ⧸ p) (B ⧸ P) := Ideal.Quotient.normal (A := A) G p P
  constructor
  · intro hI
    have hI1 : Nat.card (P.inertia G) = 1 := by rw [hI]; simp
    rw [hI1, one_mul] at hDI

    have hle : p.ramificationIdxIn B * Module.finrank (A ⧸ p) (B ⧸ P) ≤
        1 * Module.finrank (A ⧸ p) (B ⧸ P) := by
      rw [one_mul, ← hf, hef, hDI, hf]; exact haut_le
    have he1 : p.ramificationIdxIn B ≤ 1 := Nat.le_of_mul_le_mul_right hle hfpos
    have he : p.ramificationIdxIn B = 1 := by omega
    refine ⟨he, ?_⟩
    have hcard : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) = Module.finrank (A ⧸ p) (B ⧸ P) := by
      rw [← hDI, ← hef, he, one_mul, hf]
    haveI : IsGalois (A ⧸ p) (B ⧸ P) := IsGalois.of_card_aut_eq_finrank _ _ hcard
    infer_instance
  · rintro ⟨he, hsep⟩
    haveI : IsGalois (A ⧸ p) (B ⧸ P) := ⟨⟩
    have hcard : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) = Module.finrank (A ⧸ p) (B ⧸ P) :=
      IsGalois.card_aut_eq_finrank _ _
    have h : Nat.card (P.inertia G) * Module.finrank (A ⧸ p) (B ⧸ P) =
        1 * Module.finrank (A ⧸ p) (B ⧸ P) := by
      rw [← hcard, ← hDI, ← hef, he, hf, hcard]
    have h1 : Nat.card (P.inertia G) = 1 := Nat.eq_of_mul_eq_mul_right hfpos h
    exact Subgroup.eq_bot_of_card_eq (P.inertia G) h1

end P2mInertiaTrivial

theorem solution
    {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    P.inertia G = ⊥ ↔ p.ramificationIdxIn B = 1 ∧ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) :=
  P2mInertiaTrivial.inertia_eq_bot_iff G P hpb

end S_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
end P2MW
export P2MW.S_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable (solution)
