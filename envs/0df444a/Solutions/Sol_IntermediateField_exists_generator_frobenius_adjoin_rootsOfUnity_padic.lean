-- Prove2me | solution 1 for IntermediateField.exists_generator_frobenius_adjoin_rootsOfUnity_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/62a2291f-3c74-586e-885e-7a2fe29ac40d

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_IntermediateField_exists_frobenius_adjoin_rootsOfUnity_padic
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open Polynomial
open ExtCitation.LocalLevel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N)
    [FiniteDimensional K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] [Normal K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})] :
    ∃ φ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}),
      (∀ σ, σ ∈ Subgroup.zpowers φ) ∧
      ∃ a : ℕ, 0 < a ∧ ∀ ζ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}),
        (ζ : PadicAlgCl q) ^ (q ^ N - 1) = 1 → (φ ζ : PadicAlgCl q) = (ζ : PadicAlgCl q) ^ (q ^ a) := by
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
  obtain ⟨φ, a, ha, hcard, hφ⟩ := IntermediateField.exists_frobenius_adjoin_rootsOfUnity_padic q K N hN
  refine ⟨φ, ?_, a, ha, hφ⟩

  have hdeg := IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf q K N hN
  rw [hcard] at hdeg
  haveI : IsGalois K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := IsGalois.mk
  have hcardG : Nat.card ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) ≃ₐ[K] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) = orderOf ((q ^ a : ℕ) : ZMod (q ^ N - 1)) := by
    rw [IsGalois.card_aut_eq_finrank, hdeg]

  obtain ⟨ζ₀, hζ₀'⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (q ^ N - 1) (PadicAlgCl q))
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hm).ne')
  have hζ₀ : IsPrimitiveRoot ζ₀ (q ^ N - 1) := (Polynomial.isRoot_cyclotomic_iff).1 hζ₀'
  have hζL : ζ₀ ∈ (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := IntermediateField.subset_adjoin K _ hζ₀.pow_eq_one
  let x₀ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := ⟨ζ₀, hζL⟩
  have hφpow : ∀ i : ℕ, (((φ ^ i) x₀ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ζ₀ ^ ((q ^ a) ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, AlgEquiv.one_apply, pow_zero, pow_one]
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, hφ _ (by rw [ih, ← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow]),
        ih, ← pow_mul, ← pow_succ]

  have hcop : (q ^ a).Coprime (q ^ N - 1) := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq).2 hndvd)
  let u := ZMod.unitOfCoprime (q ^ a) hcop
  have hu : ((u : ZMod (q ^ N - 1))) = ((q ^ a : ℕ) : ZMod (q ^ N - 1)) := ZMod.coe_unitOfCoprime _ hcop
  have hord_le : orderOf ((q ^ a : ℕ) : ZMod (q ^ N - 1)) ≤ orderOf φ := by

    have h1 : (((φ ^ orderOf φ) x₀ : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) : PadicAlgCl q) = ζ₀ := by rw [pow_orderOf_eq_one, AlgEquiv.one_apply]
    rw [hφpow] at h1
    have h2 : ((q ^ a : ℕ) : ZMod (q ^ N - 1)) ^ orderOf φ = 1 := by
      have h3 : ζ₀ ^ ((q ^ a) ^ orderOf φ - 1) = 1 := by
        have hle : 1 ≤ (q ^ a) ^ orderOf φ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero a hq.ne_zero))
        have h4 : ζ₀ ^ ((q ^ a) ^ orderOf φ - 1) * ζ₀ = ζ₀ := by
          rw [← pow_succ, Nat.sub_add_cancel hle, h1]
        have h5 : ζ₀ ^ ((q ^ a) ^ orderOf φ - 1) * ζ₀ = 1 * ζ₀ := by rw [one_mul]; exact h4
        exact mul_right_cancel₀ (hζ₀.ne_zero hm.ne') h5
      rw [hζ₀.pow_eq_one_iff_dvd] at h3
      have h6 : (((q ^ a) ^ orderOf φ - 1 : ℕ) : ZMod (q ^ N - 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h3
      have hle : 1 ≤ (q ^ a) ^ orderOf φ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero a hq.ne_zero))
      have := congrArg (fun z : ZMod (q ^ N - 1) => z + 1) h6
      simp only [zero_add] at this
      rw [← Nat.cast_pow, ← this, Nat.cast_sub hle, Nat.cast_one, sub_add_cancel]
    have hpos : 0 < orderOf φ := orderOf_pos φ
    exact Nat.le_of_dvd hpos (orderOf_dvd_of_pow_eq_one h2)
  have htop : Subgroup.zpowers φ = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hcardG]
    exact hord_le
  intro σ
  rw [htop]
  exact Subgroup.mem_top σ

end S_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic
end P2MW
export P2MW.S_IntermediateField_exists_generator_frobenius_adjoin_rootsOfUnity_padic (solution)
