-- Prove2me | solution 1 for IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dae83d97-98c2-5122-b4d1-78bde00b59b3

import Mathlib
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet
import Theorems.Thm_ExtCitation_LocalLevel_exists_eq_pow_card_pow_of_mem_rootSet
import Theorems.Thm_IntermediateField_exists_frobenius_adjoin_rootsOfUnity_padic
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField ExtCitation.LocalLevel
open Polynomial

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N) :
    Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
      = orderOf ((Nat.card (IsLocalRing.ResidueField (Rw q K)) : ZMod (q ^ N - 1))) := by
  classical
  have hq : q.Prime := Fact.out
  have hm : 0 < q ^ N - 1 := by
    have : 1 < q ^ N := Nat.one_lt_pow hN.ne' hq.one_lt
    omega
  haveI : NeZero (q ^ N - 1) := ⟨hm.ne'⟩
  haveI : NeZero ((q ^ N - 1 : ℕ) : PadicAlgCl q) := ⟨by exact_mod_cast hm.ne'⟩
  have hndvd : ¬ q ∣ q ^ N - 1 := by
    intro h
    have h1 : q ∣ q ^ N := dvd_pow_self q hN.ne'
    have : q ∣ q ^ N - (q ^ N - 1) := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self (by omega)] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  obtain ⟨ζ₀, hζ₀'⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (q ^ N - 1) (PadicAlgCl q))
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hm).ne')
  have hζ₀ : IsPrimitiveRoot ζ₀ (q ^ N - 1) := (Polynomial.isRoot_cyclotomic_iff).1 hζ₀'
  have hint : IsIntegral K ζ₀ := IsIntegral.of_pow hm (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)
  rw [IntermediateField.finrank_adjoin_rootsOfUnity_eq_card_rootSet (q ^ N - 1) hm ζ₀ hζ₀]
  set Q := Nat.card (IsLocalRing.ResidueField (Rw q K)) with hQdef
  set d := orderOf ((Q : ℕ) : ZMod (q ^ N - 1)) with hd

  obtain ⟨φ, a, ha, hcard, hφ⟩ := IntermediateField.exists_frobenius_adjoin_rootsOfUnity_padic q K N hN
  have hQa : Q = q ^ a := hcard
  have hQcop : Q.Coprime (q ^ N - 1) := by
    rw [hQa]; exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq).2 hndvd)
  let u := ZMod.unitOfCoprime Q hQcop
  have hu : ((u : ZMod (q ^ N - 1))) = (Q : ZMod (q ^ N - 1)) := ZMod.coe_unitOfCoprime Q hQcop
  have hdu : d = orderOf u := by rw [hd, ← hu, orderOf_units]
  have hd0 : 0 < d := by rw [hdu]; exact orderOf_pos u

  have hpoweq : ∀ s t : ℕ, ζ₀ ^ s = ζ₀ ^ t ↔ s ≡ t [MOD q ^ N - 1] := by
    suffices key : ∀ s t : ℕ, s ≤ t → (ζ₀ ^ s = ζ₀ ^ t ↔ s ≡ t [MOD q ^ N - 1]) by
      intro s t
      rcases le_total s t with hst | hts
      · exact key s t hst
      · rw [eq_comm, key t s hts]; exact ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
    intro s t hst
    rw [Nat.modEq_iff_dvd' hst, ← hζ₀.pow_eq_one_iff_dvd]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hst
    rw [Nat.add_sub_cancel_left, pow_add]
    constructor
    · intro h
      have h' : ζ₀ ^ s * ζ₀ ^ c = ζ₀ ^ s * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel₀ (pow_ne_zero _ (hζ₀.ne_zero hm.ne')) h'
    · intro h; rw [h, mul_one]
  have hpowζ : ∀ i j : ℕ, ζ₀ ^ (Q ^ i) = ζ₀ ^ (Q ^ j) ↔ ((Q : ZMod (q ^ N - 1))) ^ i = ((Q : ZMod (q ^ N - 1))) ^ j := by
    intro i j
    rw [hpoweq, ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_pow]

  have hζL : ζ₀ ∈ IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} :=
    IntermediateField.subset_adjoin K _ hζ₀.pow_eq_one
  set x₀ : IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} := ⟨ζ₀, hζL⟩ with hx₀
  have hφpow : ∀ i : ℕ, (((φ ^ i) x₀ : IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) : PadicAlgCl q)
      = ζ₀ ^ (Q ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, AlgEquiv.one_apply, pow_zero, pow_one]
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, hφ _ (by rw [ih, ← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]),
        ih, ← pow_mul, ← hQa, ← pow_succ]
  have hx₀root : Polynomial.aeval x₀ (minpoly K ζ₀) = 0 := by
    have hval : (IntermediateField.val _) x₀ = ζ₀ := rfl
    have key := Polynomial.aeval_algHom_apply
      (IntermediateField.val (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) x₀ (minpoly K ζ₀)
    rw [hval, minpoly.aeval] at key
    exact (map_eq_zero_iff _ (IntermediateField.val _).injective).1 key.symm
  have hroots_pow : ∀ i : ℕ, ζ₀ ^ (Q ^ i) ∈ (minpoly K ζ₀).rootSet (PadicAlgCl q) := by
    intro i
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have e1 : ζ₀ ^ (Q ^ i) = ((IntermediateField.val _).comp (φ ^ i).toAlgHom) x₀ := (hφpow i).symm
    rw [e1, Polynomial.aeval_algHom_apply, hx₀root, map_zero]

  have hlow : d ≤ Fintype.card ((minpoly K ζ₀).rootSet (PadicAlgCl q)) := by
    let ρ : Fin d → (minpoly K ζ₀).rootSet (PadicAlgCl q) := fun i => ⟨ζ₀ ^ (Q ^ (i : ℕ)), hroots_pow i⟩
    have hρ : Function.Injective ρ := by
      intro i j hij
      have h1 : ζ₀ ^ (Q ^ (i : ℕ)) = ζ₀ ^ (Q ^ (j : ℕ)) := congrArg Subtype.val hij
      rw [hpowζ, ← hu] at h1
      have := pow_injOn_Iio_orderOf (x := (u : ZMod (q ^ N - 1)))
        (show (i : ℕ) ∈ Set.Iio (orderOf (u : ZMod (q ^ N - 1))) by rw [orderOf_units, ← hdu]; exact i.2)
        (show (j : ℕ) ∈ Set.Iio (orderOf (u : ZMod (q ^ N - 1))) by rw [orderOf_units, ← hdu]; exact j.2) h1
      exact Fin.ext this
    simpa using Fintype.card_le_of_injective ρ hρ

  have hup : Fintype.card ((minpoly K ζ₀).rootSet (PadicAlgCl q)) ≤ d := by
    let ρ : Fin d → (minpoly K ζ₀).rootSet (PadicAlgCl q) := fun i => ⟨ζ₀ ^ (Q ^ (i : ℕ)), hroots_pow i⟩
    have hρ : Function.Surjective ρ := by
      intro t
      obtain ⟨i, hi⟩ := ExtCitation.LocalLevel.exists_eq_pow_card_pow_of_mem_rootSet q K (q ^ N - 1) hndvd ζ₀ hζ₀ t t.2
      refine ⟨⟨i % d, Nat.mod_lt _ hd0⟩, Subtype.ext ?_⟩
      change ζ₀ ^ (Q ^ (i % d)) = (t : PadicAlgCl q)
      rw [hi, hpowζ, hd, pow_mod_orderOf]
    simpa using Fintype.card_le_of_surjective ρ hρ
  exact le_antisymm hup hlow

end S_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
end P2MW
export P2MW.S_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf (solution)
