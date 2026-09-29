-- Prove2me | solution 1 for Ideal.isSeparable_quotient_of_forall_prime_not_dvd_card_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/15059324-5860-5992-ac5b-8a1e9aff7af9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia

set_option autoImplicit false

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field in
theorem solution
    {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (hI : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : R ⧸ p) = 0 → ¬ ℓ ∣ Nat.card ↥(P.inertia G)) :
    Algebra.IsSeparable (R ⧸ p) (S ⧸ P) := by
  classical
  haveI hnormal : Normal (R ⧸ p) (S ⧸ P) := Ideal.Quotient.normal (A := R) G p P
  haveI : Module.Finite R (S ⧸ P) := inferInstance
  haveI hfin : Module.Finite (R ⧸ p) (S ⧸ P) := Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ P)
  haveI : FiniteDimensional (R ⧸ p) (S ⧸ P) := hfin

  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have h2 : (p.primesOver S).ncard * Nat.card ↥(MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hN : (p.primesOver S).ncard ≠ 0 := IsDedekindDomain.primesOver_ncard_ne_zero p S
  have hD : Nat.card ↥(MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
    refine mul_right_injective₀ hN ?_
    dsimp only
    rw [h2, ← h1]

  have hDI : Nat.card ↥(MulAction.stabilizer G P) = Nat.card ↥(P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) := by
    have hidx : Subgroup.index _ = _ := Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
    rw [← hidx, ← ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv]
    rfl

  have hA : Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) = Field.finSepDegree (R ⧸ p) (S ⧸ P) := by
    rw [Field.finSepDegree_eq_of_isAlgClosed (R ⧸ p) (S ⧸ P) (AlgebraicClosure (S ⧸ P))]
    exact (Nat.card_congr (Normal.algHomEquivAut (R ⧸ p) (AlgebraicClosure (S ⧸ P)) (S ⧸ P))).symm

  have hf : p.inertiaDegIn S = Module.finrank (R ⧸ p) (S ⧸ P) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p P G, Ideal.inertiaDeg_eq_of_isMaximal p P]
  have hsi := Field.finSepDegree_mul_finInsepDegree (R ⧸ p) (S ⧸ P)

  have hIe : Nat.card ↥(P.inertia G) = p.ramificationIdxIn S * Field.finInsepDegree (R ⧸ p) (S ⧸ P) := by
    have hs0 : Field.finSepDegree (R ⧸ p) (S ⧸ P) ≠ 0 := NeZero.ne _
    apply mul_left_injective₀ hs0

    calc Nat.card ↥(P.inertia G) * Field.finSepDegree (R ⧸ p) (S ⧸ P)
        = Nat.card ↥(MulAction.stabilizer G P) := by rw [hDI, hA]
      _ = p.ramificationIdxIn S * (Field.finSepDegree (R ⧸ p) (S ⧸ P) * Field.finInsepDegree (R ⧸ p) (S ⧸ P)) := by
          rw [hD, hf, hsi]
      _ = p.ramificationIdxIn S * Field.finInsepDegree (R ⧸ p) (S ⧸ P) * Field.finSepDegree (R ⧸ p) (S ⧸ P) := by ring
  have hdvd : Field.finInsepDegree (R ⧸ p) (S ⧸ P) ∣ Nat.card ↥(P.inertia G) := ⟨p.ramificationIdxIn S, by rw [hIe, mul_comm]⟩

  rw [isSeparable_iff_finInsepDegree_eq_one]
  obtain ⟨c, hc⟩ := CharP.exists (R ⧸ p)
  rcases CharP.char_is_prime_or_zero (R ⧸ p) c with hprime | h0
  · haveI : ExpChar (R ⧸ p) c := ExpChar.prime hprime
    obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (R ⧸ p) (S ⧸ P) c
    rcases n with _ | m
    · simpa using hn
    · exfalso
      apply hI c hprime (CharP.cast_eq_zero (R ⧸ p) c)
      exact dvd_trans (hn ▸ dvd_pow_self c (Nat.succ_ne_zero m) : c ∣ Field.finInsepDegree (R ⧸ p) (S ⧸ P)) hdvd
  · subst h0
    haveI : CharZero (R ⧸ p) := CharP.charP_to_charZero (R ⧸ p)
    obtain ⟨n, hn⟩ := finInsepDegree_eq_pow (R ⧸ p) (S ⧸ P) 1
    simpa using hn

end S_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia
end P2MW
export P2MW.S_Ideal_isSeparable_quotient_of_forall_prime_not_dvd_card_inertia (solution)
