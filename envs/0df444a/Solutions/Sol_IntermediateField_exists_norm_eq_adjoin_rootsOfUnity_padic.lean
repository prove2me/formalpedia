-- Prove2me | solution 1 for IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1fb6b858-b26d-5c79-a1e8-53d773707d3a

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_IntermediateField_finiteDimensional_normal_adjoin_rootsOfUnity_padic
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Theorems.Thm_ExtCitation_LocalLevel_residue_injOn_rootsOfUnity
import Theorems.Thm_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open Polynomial
open ExtCitation.LocalLevel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (N : ℕ) (hN : 0 < N)
    (x : (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})) (hx : x ≠ 0) :
    ∃ y : K, ‖(x : PadicAlgCl q)‖ = ‖((y : PadicAlgCl q))‖ := by
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

  obtain ⟨hFD, -⟩ := IntermediateField.finiteDimensional_normal_adjoin_rootsOfUnity_padic q K N hN
  haveI := hFD
  let Lw : IntermediateField ℚ_[q] (PadicAlgCl q) :=
    (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).restrictScalars ℚ_[q]
  haveI : FiniteDimensional ℚ_[q] Lw := by
    change FiniteDimensional ℚ_[q] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})
    exact FiniteDimensional.trans ℚ_[q] K _
  have hKL : K ≤ Lw := fun z hz => by
    change z ∈ IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}
    have : z = algebraMap K (PadicAlgCl q) ⟨z, hz⟩ := rfl
    rw [this]
    exact IntermediateField.algebraMap_mem _ _

  obtain ⟨e, f, he, hf, -, hcardκ, -⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q K
  obtain ⟨e', f', ι, hιval, he', hf', hιmax, hcardL, hdeg⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q K Lw hKL
  haveI : Finite (IsLocalRing.ResidueField (Rw q K)) := ExtCitation.LocalLevel.finite_residueField_Rw q K
  haveI : Finite (IsLocalRing.ResidueField (Rw q Lw)) := ExtCitation.LocalLevel.finite_residueField_Rw q Lw
  letI : Fintype (IsLocalRing.ResidueField (Rw q K)) := Fintype.ofFinite _
  letI : Fintype (IsLocalRing.ResidueField (Rw q Lw)) := Fintype.ofFinite _
  haveI hιloc : IsLocalHom ι := by
    refine ⟨fun z hz => ?_⟩
    by_contra hnu
    have hzm : z ∈ IsLocalRing.maximalIdeal (Rw q K) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have : ι z ∈ IsLocalRing.maximalIdeal (Rw q Lw) ^ e' := by
      rw [← hιmax]; exact Ideal.mem_map_of_mem ι hzm
    exact (IsLocalRing.mem_maximalIdeal _).1 (Ideal.pow_le_self he'.ne' this) hz
  let rL := IsLocalRing.residue (Rw q Lw)
  let iota : IsLocalRing.ResidueField (Rw q K) →+* IsLocalRing.ResidueField (Rw q Lw) := IsLocalRing.ResidueField.map ι
  letI : Algebra (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw)) := iota.toAlgebra

  have hQ1 : 1 < Nat.card (IsLocalRing.ResidueField (Rw q K)) := by rw [hcardκ]; exact Nat.one_lt_pow hf.ne' hq.one_lt
  have hPA3 := IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf q K N hN
  have htower : Module.finrank ℚ_[q] Lw
      = Module.finrank ℚ_[q] K * Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) := by
    change Module.finrank ℚ_[q] (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) = _
    rw [Module.finrank_mul_finrank]
  have hK0 : 0 < Module.finrank ℚ_[q] K := Module.finrank_pos
  have hef : e' * f' = orderOf ((Nat.card (IsLocalRing.ResidueField (Rw q K)) : ℕ) : ZMod (q ^ N - 1)) := by
    rw [← hPA3]
    apply Nat.eq_of_mul_eq_mul_left hK0
    rw [← hdeg, htower]

  obtain ⟨ζ₀, hζ₀'⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (q ^ N - 1) (PadicAlgCl q))
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hm).ne')
  have hζ₀ : IsPrimitiveRoot ζ₀ (q ^ N - 1) := (Polynomial.isRoot_cyclotomic_iff).1 hζ₀'
  have hζL : ζ₀ ∈ Lw := IntermediateField.subset_adjoin K _ hζ₀.pow_eq_one
  have hnorm1 : ‖ζ₀‖ = 1 := by
    have h := congrArg norm hζ₀.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h
  have hmemRw : ∀ (z : Lw), z ∈ Rw q Lw ↔ ‖(z : PadicAlgCl q)‖ ≤ 1 := fun z => by
    change ((z : PadicAlgCl q)) ∈ padicIntegers q ↔ _
    rw [mem_padicIntegers_iff]
    rfl
  let j : Rw q Lw →+* PadicAlgCl q := (algebraMap Lw (PadicAlgCl q)).comp (Rw q Lw).toSubring.subtype
  have hj : ∀ z : Rw q Lw, j z = ((z : Lw) : PadicAlgCl q) := fun _ => rfl
  have hjinj : Function.Injective j := fun y₁ y₂ h12 => Subtype.ext (Subtype.ext h12)
  let y₀ : Rw q Lw := ⟨⟨ζ₀, hζL⟩, (hmemRw _).2 (by change ‖ζ₀‖ ≤ 1; rw [hnorm1])⟩
  have hy₀ : j y₀ = ζ₀ := rfl
  have hy₀m : y₀ ^ (q ^ N - 1) = 1 := hjinj (by rw [map_pow, hy₀, hζ₀.pow_eq_one, map_one])
  have hzbar : IsPrimitiveRoot (rL y₀) (q ^ N - 1) := by
    refine IsPrimitiveRoot.mk_of_lt (rL y₀) hm (by rw [← map_pow, hy₀m, map_one]) (fun l hl hlm hl1 => ?_)
    rw [← map_pow, ← map_one rL] at hl1
    have h1 := ExtCitation.LocalLevel.residue_injOn_rootsOfUnity q Lw (q ^ N - 1) hndvd (y₀ ^ l) 1
      (by rw [← pow_mul, mul_comm, pow_mul, hy₀m, one_pow]) (one_pow _) hl1
    have h2 : ζ₀ ^ l = 1 := by
      have := congrArg j h1
      rwa [map_pow, hy₀, map_one] at this
    exact hζ₀.pow_ne_one_of_pos_of_lt hl.ne' hlm h2
  have hQF : Fintype.card (IsLocalRing.ResidueField (Rw q K)) = Nat.card (IsLocalRing.ResidueField (Rw q K)) :=
    (Nat.card_eq_fintype_card).symm
  have hcop : (Fintype.card (IsLocalRing.ResidueField (Rw q K))).Coprime (q ^ N - 1) := by
    rw [hQF, hcardκ]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hq).2 hndvd)
  obtain ⟨hdegbar, -⟩ := minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot _ _ (q ^ N - 1) (rL y₀) hzbar hcop
  rw [← orderOf_units, ZMod.coe_unitOfCoprime, hQF] at hdegbar

  have hintbar : IsIntegral (IsLocalRing.ResidueField (Rw q K)) (rL y₀) := .of_finite _ _
  have hdvd : orderOf ((Nat.card (IsLocalRing.ResidueField (Rw q K)) : ℕ) : ZMod (q ^ N - 1)) ∣ Module.finrank (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw)) := by
    rw [← hdegbar, ← IntermediateField.adjoin.finrank hintbar]
    exact ⟨_, (Module.finrank_mul_finrank (IsLocalRing.ResidueField (Rw q K))
      (IntermediateField.adjoin (IsLocalRing.ResidueField (Rw q K)) {rL y₀}) (IsLocalRing.ResidueField (Rw q Lw))).symm⟩
  have hfinrankL : Module.finrank (IsLocalRing.ResidueField (Rw q K)) (IsLocalRing.ResidueField (Rw q Lw)) = f' := by
    have h1 := Module.card_eq_pow_finrank (K := IsLocalRing.ResidueField (Rw q K)) (V := IsLocalRing.ResidueField (Rw q Lw))
    rw [hQF, ← Nat.card_eq_fintype_card, hcardL] at h1
    exact (Nat.pow_right_injective hQ1 h1).symm
  rw [hfinrankL] at hdvd
  have hdle : orderOf ((Nat.card (IsLocalRing.ResidueField (Rw q K)) : ℕ) : ZMod (q ^ N - 1)) ≤ f' := Nat.le_of_dvd hf' hdvd
  have he1 : e' = 1 := by
    have : e' * f' ≤ 1 * f' := by rw [one_mul, hef]; exact hdle
    have := Nat.le_of_mul_le_mul_right this hf'
    omega

  haveI hDVRK : IsDiscreteValuationRing (Rw q K) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q K
  haveI hDVRL : IsDiscreteValuationRing (Rw q Lw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Lw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Rw q K)
  have hspanK : IsLocalRing.maximalIdeal (Rw q K) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hspanL : IsLocalRing.maximalIdeal (Rw q Lw) = Ideal.span {ι ϖ} := by
    rw [← pow_one (IsLocalRing.maximalIdeal (Rw q Lw)), ← he1, ← hιmax, hspanK, Ideal.map_span, Set.image_singleton]
  have hϖL : Irreducible (ι ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hspanL

  have hunit : ∀ u : (Rw q Lw)ˣ, ‖(((u : Rw q Lw) : Lw) : PadicAlgCl q)‖ = 1 := fun u => by
    have ha : ‖(((u : Rw q Lw) : Lw) : PadicAlgCl q)‖ ≤ 1 := (hmemRw _).1 (u : Rw q Lw).2
    have hb : ‖((((u⁻¹ : (Rw q Lw)ˣ) : Rw q Lw) : Lw) : PadicAlgCl q)‖ ≤ 1 := (hmemRw _).1 ((u⁻¹ : (Rw q Lw)ˣ) : Rw q Lw).2
    have hmul : ‖(((u : Rw q Lw) : Lw) : PadicAlgCl q)‖ * ‖((((u⁻¹ : (Rw q Lw)ˣ) : Rw q Lw) : Lw) : PadicAlgCl q)‖ = 1 := by
      rw [← norm_mul, ← hj, ← hj, ← map_mul, u.mul_inv, map_one, norm_one]
    apply le_antisymm ha
    calc (1 : ℝ) = _ := hmul.symm
      _ ≤ ‖(((u : Rw q Lw) : Lw) : PadicAlgCl q)‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := mul_one _
  have hϖval : (((ι ϖ : Rw q Lw) : Lw) : PadicAlgCl q) = ((ϖ : K) : PadicAlgCl q) := hιval ϖ
  have hdec : ∀ z : Lw, z ≠ 0 → ‖(z : PadicAlgCl q)‖ ≤ 1 →
      ∃ n : ℕ, ‖(z : PadicAlgCl q)‖ = ‖((ϖ : K) : PadicAlgCl q)‖ ^ n := by
    intro z hz hz1
    have hr : (⟨z, (hmemRw z).2 hz1⟩ : Rw q Lw) ≠ 0 := fun h => hz (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖL
    refine ⟨n, ?_⟩
    have := congrArg (fun r : Rw q Lw => ‖j r‖) hu
    rw [map_mul, map_pow, norm_mul, norm_pow, hj, hj, hj, hunit, one_mul, hϖval] at this
    exact this

  have hxval : ((x : PadicAlgCl q)) ≠ 0 := fun h => hx (Subtype.ext h)
  let xw : Lw := ⟨(x : PadicAlgCl q), x.2⟩
  by_cases hx1 : ‖(x : PadicAlgCl q)‖ ≤ 1
  · obtain ⟨n, hn⟩ := hdec xw (fun h => hxval (congrArg Subtype.val h)) hx1
    refine ⟨(ϖ : K) ^ n, ?_⟩
    change ‖(x : PadicAlgCl q)‖ = ‖algebraMap K (PadicAlgCl q) (((ϖ : Rw q K) : K) ^ n)‖
    rw [map_pow]
    change _ = ‖(((ϖ : Rw q K) : K) : PadicAlgCl q) ^ n‖
    rw [norm_pow, ← hn]
  · have hxi1 : ‖((xw⁻¹ : Lw) : PadicAlgCl q)‖ ≤ 1 := by
      change ‖((x : PadicAlgCl q))⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx1))
    obtain ⟨n, hn⟩ := hdec xw⁻¹ (inv_ne_zero (fun h => hxval (congrArg Subtype.val h))) hxi1
    refine ⟨((ϖ : K) ^ n)⁻¹, ?_⟩
    have hn' : ‖((x : PadicAlgCl q))‖⁻¹ = ‖((ϖ : K) : PadicAlgCl q)‖ ^ n := by
      rw [← norm_inv]; exact hn
    change ‖(x : PadicAlgCl q)‖ = ‖algebraMap K (PadicAlgCl q) ((((ϖ : Rw q K) : K) ^ n)⁻¹)‖
    rw [map_inv₀, map_pow]
    change _ = ‖((((ϖ : Rw q K) : K) : PadicAlgCl q) ^ n)⁻¹‖
    rw [norm_inv, norm_pow, ← hn', inv_inv]

end S_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic
end P2MW
export P2MW.S_IntermediateField_exists_norm_eq_adjoin_rootsOfUnity_padic (solution)
