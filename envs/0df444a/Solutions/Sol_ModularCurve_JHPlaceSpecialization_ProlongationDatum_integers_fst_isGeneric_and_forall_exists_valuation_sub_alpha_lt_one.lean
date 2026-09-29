-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/702107fe-6dce-5d8c-bd73-2d5673cceb4f

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_residue_alpha_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

namespace IDENTS

theorem coeffMap_algebraMap' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    coeffMap f (algebraMap R (LaurentSeries R) a) = algebraMap S (LaurentSeries S) (f a) := by
  change coeffMap f (HahnSeries.ofPowerSeries ℤ R (PowerSeries.C a)) = HahnSeries.ofPowerSeries ℤ S (PowerSeries.C (f a))
  rw [coeffMap_ofPowerSeries, PowerSeries.map_C]

set_option synthInstance.maxHeartbeats 800000 in
open Polynomial in
theorem coeffMap_aeval_jqModC_eq_coe_aeval (A : ValuationSubring (AlgebraicClosure ℚ)) (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (P : Polynomial ↥A) :
    coeffMap A.subtype (Polynomial.aeval (jqModC ↥A) P) = ((Polynomial.aeval x (P.map A.subtype) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => rw [map_add, map_add, Polynomial.map_add, map_add, h₁, h₂]; rfl
  | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow, coeffMap_jqModC,
        coeffMap_algebraMap']
      rw [show (((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (A.subtype a) * x ^ n : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
          = ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (A.subtype a) : LaurentSeries (AlgebraicClosure ℚ)) * ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ^ n
          from rfl, hx]
      rfl

theorem coeffMap_residue_aeval_jqModC (A : ValuationSubring (AlgebraicClosure ℚ)) (P : Polynomial ↥A) :
    coeffMap (IsLocalRing.residue ↥A) (Polynomial.aeval (jqModC ↥A) P) = Polynomial.aeval (jqModC (ResidueField ↥A)) (P.map (IsLocalRing.residue ↥A)) := by
  induction P using Polynomial.induction_on' with
  | add P₁ P₂ h₁ h₂ => simp only [map_add, Polynomial.map_add, h₁, h₂]
  | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow, coeffMap_jqModC, coeffMap_algebraMap']

end IDENTS

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :

    ((∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ Rpd.R₁.integers ↔ c ∈ A) ∧
        (∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
          Polynomial.aeval x (Q.map A.subtype) ∈ Rpd.R₁.integers ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ Rpd.R₁.integers)) ∧

    (∀ g : ↥(xHFunctionFieldBar M H), g ∈ Rpd.R₁.integers → ∃ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (α u : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers ∧ Rpd.R₁.integers.valuation (g - α u) < 1) := by
  classical
  refine ⟨⟨fun c => Rpd.R₁.algebraMap_mem_iff c, ?_⟩, ?_⟩
  ·
    intro Q hQ
    set y : LaurentSeries ↥A := Polynomial.aeval (jqModC ↥A) Q with hy
    have hyx : coeffMap A.subtype y = ((Polynomial.aeval x (Q.map A.subtype) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) :=
      IDENTS.coeffMap_aeval_jqModC_eq_coe_aeval A M H x hx Q
    have hmemF : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := by rw [hyx]; exact (Polynomial.aeval x (Q.map A.subtype)).2
    obtain ⟨hint, hres⟩ := Rpd.residue₁_coeffMap y hmemF
    have heq : (⟨coeffMap A.subtype y, hmemF⟩ : ↥(xHFunctionFieldBar M H)) = Polynomial.aeval x (Q.map A.subtype) := Subtype.ext hyx

    have hred : coeffMap (IsLocalRing.residue ↥A) y = Polynomial.aeval (jqModC (ResidueField ↥A)) (Q.map (IsLocalRing.residue ↥A)) :=
      IDENTS.coeffMap_residue_aeval_jqModC A Q
    have hne : Rpd.R₁.residue ⟨⟨coeffMap A.subtype y, hmemF⟩, hint⟩ ≠ 0 := by
      intro h0
      have := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (z : LaurentSeries (ResidueField ↥A))) h0
      simp only [ZeroMemClass.coe_zero] at this
      rw [hres, hred] at this
      exact (ModularCurve.transcendental_jqModC (ResidueField ↥A)) ⟨Q.map (IsLocalRing.residue ↥A), hQ, this⟩
    have hunit : IsUnit (⟨⟨coeffMap A.subtype y, hmemF⟩, hint⟩ : Rpd.R₁.integers) := Rpd.R₁.isUnit_of_residue_ne_zero hne

    have hint' : (Polynomial.aeval x (Q.map A.subtype) : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers := heq ▸ hint
    refine ⟨hint', ?_⟩
    obtain ⟨u, hu⟩ := hunit
    have hval : ((u : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)) = Polynomial.aeval x (Q.map A.subtype) := by
      rw [hu]; exact heq
    have hinv : (((u⁻¹ : (Rpd.R₁.integers)ˣ) : Rpd.R₁.integers) : ↥(xHFunctionFieldBar M H)) = (Polynomial.aeval x (Q.map A.subtype))⁻¹ := by
      rw [← hval]
      symm
      apply inv_eq_of_mul_eq_one_left
      have h1 : ((u⁻¹ : (Rpd.R₁.integers)ˣ) : Rpd.R₁.integers) * (u : Rpd.R₁.integers) = 1 := u.inv_mul
      have h2 := congrArg (fun z : Rpd.R₁.integers => (z : ↥(xHFunctionFieldBar M H))) h1
      simp only [Subring.coe_mul, OneMemClass.coe_one] at h2
      exact h2
    rw [← hinv]
    exact ((u⁻¹ : (Rpd.R₁.integers)ˣ) : Rpd.R₁.integers).2
  ·
    intro g hg
    obtain ⟨v, hv, hres⟩ := ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_residue_alpha_eq p M H hpM hpM2 A hA θ α hα_coe Psp Rpd
      (Rpd.R₁.residue ⟨g, hg⟩)
    refine ⟨v, hv, ?_⟩
    have hker : (⟨g, hg⟩ - ⟨α v, hv⟩ : Rpd.R₁.integers) ∈ RingHom.ker Rpd.R₁.residue := by
      rw [RingHom.mem_ker, map_sub, hres, sub_self]
    rw [Rpd.R₁.ker_residue] at hker
    exact (ValuationSubring.valuation_lt_one_iff Rpd.R₁.integers (⟨g, hg⟩ - ⟨α v, hv⟩)).mp hker

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one (solution)
