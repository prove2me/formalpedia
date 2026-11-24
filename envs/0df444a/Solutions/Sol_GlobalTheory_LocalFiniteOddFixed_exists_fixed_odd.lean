-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.exists_fixed_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:26:02.050887+00:00
-- url     : https://prove2.me/submissions/e755ce75-2986-46b1-ac6b-f50589abdf69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_isLocalRing_of_finite
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_odd_of_involution
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_val_of_span_eq
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_exists_conj_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
open GlobalTheory.UnitLemma
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L]
    [IsScalarTower K.O K.E L] [Module.Finite K.E L] (τ : L →+* L) (hτ : ∀ x, τ (τ x) = x)
    (hc : ∀ e : K.E, τ (algebraMap K.E L e) = algebraMap K.E L (K.c e)) :
    ∃ y : L, y ≠ 0 ∧ τ y = y ∧ K.eta (Algebra.norm K.E y) = -1 := by
  obtain ⟨c, hcO⟩ := exists_conj_int K
  have hτO : ∀ x : K.O, τ (algebraMap K.O L x) = algebraMap K.O L (c x) := by
    intro x
    rw [IsScalarTower.algebraMap_apply K.O K.E L, hc, ← hcO, ← IsScalarTower.algebraMap_apply]
  let R := integralClosure K.O L
  haveI : Module.Finite K.O R := IsIntegralClosure.finite K.O K.E L R
  haveI : IsDedekindDomain R := IsIntegralClosure.isDedekindDomain K.O K.E L R
  haveI : IsLocalRing R := isLocalRing_of_finite K.O R
  have injL : Function.Injective (algebraMap K.O L) := by
    rw [IsScalarTower.algebraMap_eq K.O K.E L]
    exact (algebraMap K.E L).injective.comp (IsFractionRing.injective K.O K.E)
  have injR : Function.Injective (algebraMap K.O R) := by
    intro x y h
    apply injL
    rw [IsScalarTower.algebraMap_apply K.O R L, h, ← IsScalarTower.algebraMap_apply]
  haveI : FaithfulSMul K.O R := (faithfulSMul_iff_algebraMap_injective _ _).2 injR
  haveI : Module.IsTorsionFree K.O R := inferInstance
  have hnf : ¬ IsField R := fun h =>
    IsDiscreteValuationRing.not_isField K.O
      ((Algebra.IsIntegral.isField_iff_isField injR).2 h)
  haveI : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 2 0).1 ‹IsDedekindDomain R›
  have hint : ∀ x : R, τ (x : L) ∈ R := by
    intro x
    exact IsIntegral.map_of_comp_eq c τ (by ext z; simp [hτO]) x.2
  let t : R →+* R := RingHom.codRestrict (τ.comp (algebraMap R L)) R hint
  have ht : ∀ x : R, ((t x : R) : L) = τ x := fun x => rfl
  have htt : ∀ x, t (t x) = x := fun x => Subtype.ext (by rw [ht, ht, hτ])
  have htO : ∀ x : K.O, t (algebraMap K.O R x) = algebraMap K.O R (c x) :=
    fun x => Subtype.ext (hτO x)
  haveI : IsLocalHom t := ⟨fun x hx => by simpa [htt] using hx.map t⟩
  haveI : IsLocalHom (algebraMap K.O R) := inferInstance
  obtain ⟨a, b, hab, hnm⟩ := K.c_res
  have hb : c a = b := IsFractionRing.injective K.O K.E (by rw [hcO, hab])
  have hδ : algebraMap K.O R a - t (algebraMap K.O R a) ∉ IsLocalRing.maximalIdeal R := by
    rw [htO, hb, ← map_sub]
    intro h
    apply (IsLocalRing.mem_maximalIdeal _).1 h
    exact (IsLocalRing.notMem_maximalIdeal.1 hnm).map _

  have hunif : ∃ p : R, t p = p ∧ IsLocalRing.maximalIdeal R = Ideal.span {p} := by
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hm : IsLocalRing.maximalIdeal R = Ideal.span {p} := hp.maximalIdeal_eq
    have hpm : t p ∈ Ideal.span {p} := by
      rw [← hm]
      exact map_nonunit t p ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hpm
    have key : ∀ s : R, s + t s * u ∉ IsLocalRing.maximalIdeal R →
        ∃ p : R, t p = p ∧ IsLocalRing.maximalIdeal R = Ideal.span {p} := by
      intro s hs
      refine ⟨s * p + t (s * p), by rw [map_add, htt, add_comm], ?_⟩
      have : s * p + t (s * p) = (s + t s * u) * p := by rw [map_mul, ← hu]; ring
      rw [this, hm, Ideal.span_singleton_mul_left_unit (IsLocalRing.notMem_maximalIdeal.1 hs)]
    by_cases h1 : 1 + t 1 * u ∈ IsLocalRing.maximalIdeal R
    · refine key (algebraMap K.O R a) fun h2 => hδ ?_
      rw [map_one, one_mul] at h1
      have := Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ (t (algebraMap K.O R a)) h1)
      convert this using 1
      ring
    · exact key 1 h1
  obtain ⟨p, htp, hm⟩ := hunif
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field R (by rw [hm]; simp)
  haveI : (IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal K.O) := inferInstance
  haveI : CharZero K.O := RingHom.charZero (algebraMap K.O K.E)
  haveI : PerfectField (FractionRing K.O) := inferInstance
  set f := (IsLocalRing.maximalIdeal R).inertiaDeg K.O with hf
  have hN : Ideal.span {Algebra.intNorm K.O R p} = IsLocalRing.maximalIdeal K.O ^ f := by
    rw [← Ideal.relNorm_singleton, ← hm]
    exact Ideal.relNorm_eq_pow_of_isMaximal _ _
  have hval : val K.O (Algebra.norm K.E (p : L)) = f := by
    have := Algebra.algebraMap_intNorm (A := K.O) (K := K.E) (L := L) (B := R) p
    rw [← val_of_span_eq (E := K.E) K.O _ f hN, this]
    rfl
  have hf' : f = Module.finrank (IsLocalRing.ResidueField K.O) (IsLocalRing.ResidueField R) := by
    rw [hf, Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal K.O)]
    rfl
  haveI : Module.Finite (IsLocalRing.ResidueField K.O) (IsLocalRing.ResidueField R) :=
    inferInstance
  haveI : Finite (IsLocalRing.ResidueField R) :=
    Module.finite_of_finite (IsLocalRing.ResidueField K.O)
  have hcard : Nat.card (IsLocalRing.ResidueField R) = (K.q ^ 2) ^ f := by
    rw [hf', ← K.card_res]
    exact Module.natCard_eq_pow_finrank
  have hodd : Odd f := by
    refine odd_of_involution (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField.map t) ?_
      K.q f hcard (IsLocalRing.residue R (algebraMap K.O R a)) ?_ ?_
    · intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue, htt]
    · haveI := Fintype.ofFinite (IsLocalRing.ResidueField K.O)
      have h1 := FiniteField.pow_card (IsLocalRing.residue K.O a)
      rw [← Nat.card_eq_fintype_card, K.card_res] at h1
      rw [← IsLocalRing.ResidueField.map_residue (algebraMap K.O R), ← map_pow, h1]
    · rw [IsLocalRing.ResidueField.map_residue]
      intro h
      apply hδ
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  refine ⟨p, fun h => hp0 (Subtype.ext h), by rw [← ht, htp], ?_⟩
  unfold UQ.eta
  rw [hval, zpow_natCast, hodd.neg_one_pow]
end GlobalTheory.LocalFiniteOddFixed
