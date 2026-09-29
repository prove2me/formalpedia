-- Prove2me | solution 1 for IsDiscreteValuationRing.valuationSubring_eq_of_finrank_le_finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0c5d5a41-d0f9-5b83-9ce7-4e830b7e2b3b

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_valuationSubring_eq_of_finrank_le_finrank_residueField

set_option autoImplicit false

namespace UniqValAux

theorem mem_of_isIntegral {O E : Type*} [CommRing O] [Field E] [Algebra O E]
    (V : ValuationSubring E) (hOV : ∀ x : O, algebraMap O E x ∈ V)
    {y : E} (hy : IsIntegral O y) : y ∈ V := by
  let φ : O →+* ↥V := (algebraMap O E).codRestrict V.toSubring hOV
  have hy' : IsIntegral ↥V y := by
    obtain ⟨q, hq, hqy⟩ := hy
    refine ⟨q.map φ, hq.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hqy
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := E)).mp hy'
  rw [← hz]
  exact z.2

theorem not_mem_nonunits_of_isUnit {O E : Type*} [CommRing O] [Field E] [Algebra O E]
    (V : ValuationSubring E) (hOV : ∀ x : O, algebraMap O E x ∈ V) {x : O} (hx : IsUnit x) :
    algebraMap O E x ∉ V.nonunits := by
  obtain ⟨u, rfl⟩ := hx
  intro hmem
  have hunit : IsUnit (⟨algebraMap O E ↑u, hOV ↑u⟩ : ↥V) :=
    (Units.map ((algebraMap O E).codRestrict V.toSubring hOV : O →* ↥V) u).isUnit
  have hmem' := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨algebraMap O E ↑u, hOV ↑u⟩)).mp hmem
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmem') hunit

theorem inv_not_mem_of_mem_nonunits {E : Type*} [Field E] (V : ValuationSubring E) {x : E}
    (hx : x ∈ V.nonunits) (hx0 : x ≠ 0) : x⁻¹ ∉ V := by
  intro hinv
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have hle : V.valuation x⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hinv
  have : V.valuation (x * x⁻¹) < 1 := by
    rw [map_mul]
    calc V.valuation x * V.valuation x⁻¹ ≤ V.valuation x * 1 := mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact hx
  rw [mul_inv_cancel₀ hx0, map_one] at this
  exact lt_irrefl _ this

end UniqValAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (W : ValuationSubring F) (hW : W ≠ ⊤) (hOW : ∀ x : O, algebraMap O F x ∈ W)
    (hmW : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ W.nonunits)

    [Algebra O ↥W] (halg : ∀ x : O, ((algebraMap O ↥W x : ↥W) : F) = algebraMap O F x)
    [Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥W)]
    (hres : ∀ x : O, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥W)
      (IsLocalRing.residue O x) = IsLocalRing.residue ↥W (algebraMap O ↥W x))
    (hf : Module.finrank E F ≤ Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥W)) :
    ∀ W' : ValuationSubring F, W' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ W') →
      (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ W'.nonunits) → W' = W := by
  classical
  intro W' hW' hOW' hmW'

  haveI : IsDedekindDomain ↥(integralClosure O F) := integralClosure.isDedekindDomain O E F
  haveI : Module.Finite O ↥(integralClosure O F) := IsIntegralClosure.finite O E F ↥(integralClosure O F)
  haveI : IsFractionRing ↥(integralClosure O F) F := integralClosure.isFractionRing_of_finite_extension E F
  have hRW : ∀ r : ↥(integralClosure O F), algebraMap _ F r ∈ W := fun r => UniqValAux.mem_of_isIntegral W hOW r.2
  have hRW' : ∀ r : ↥(integralClosure O F), algebraMap _ F r ∈ W' := fun r => UniqValAux.mem_of_isIntegral W' hOW' r.2
  obtain ⟨v, hWeq, hv⟩ := ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem W hRW hW
  haveI hvp : v.asIdeal.IsPrime := v.isPrime
  haveI hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot

  have hmO : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O ↔ algebraMap O F x ∈ W.nonunits := fun x =>
    ⟨hmW x, fun hx => by
      by_contra hx'
      exact UniqValAux.not_mem_nonunits_of_isUnit W hOW ((IsLocalRing.notMem_maximalIdeal).mp hx') hx⟩
  haveI hover : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal O) := by
    refine ⟨?_⟩
    ext x
    rw [Ideal.mem_comap, hv, hmO, IsScalarTower.algebraMap_apply O ↥(integralClosure O F) F]

  have hd : Module.finrank E F ≤ (IsLocalRing.maximalIdeal O).inertiaDeg' v.asIdeal := by
    rw [Ideal.inertiaDeg_algebraMap]
    haveI hloc : IsLocalization.AtPrime ↥(v.valuationSubringAtPrime F) v.asIdeal := inferInstance
    have hkerW : ∀ r : ↥(integralClosure O F), r ∈ v.asIdeal ↔
        algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) r ∈ IsLocalRing.maximalIdeal ↥(v.valuationSubringAtPrime F) := fun r => by
      rw [hv r, hWeq, ← ValuationSubring.coe_mem_nonunits_iff]; rfl

    subst hWeq
    let ψ : ↥(integralClosure O F) ⧸ v.asIdeal →+* IsLocalRing.ResidueField ↥(v.valuationSubringAtPrime F) :=
      Ideal.Quotient.lift v.asIdeal ((IsLocalRing.residue ↥(v.valuationSubringAtPrime F)).comp (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F)))
        (fun r hr => by
          rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
          exact (hkerW r).mp hr)
    have hψmk : ∀ r : ↥(integralClosure O F), ψ (Ideal.Quotient.mk v.asIdeal r) =
        IsLocalRing.residue _ (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) r) := fun r => Ideal.Quotient.lift_mk _ _ _
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hψmk, IsLocalRing.residue_eq_zero_iff] at hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hkerW r).mpr hx)
    have hψsurj : Function.Surjective ψ := by
      intro z
      obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl w
      obtain ⟨t, i, hi, hti⟩ := hvmax.exists_inv (show (s : ↥(integralClosure O F)) ∉ v.asIdeal from s.2)
      refine ⟨Ideal.Quotient.mk _ (a * t), ?_⟩
      rw [hψmk, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      have hu : IsUnit (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) (s : ↥(integralClosure O F))) := IsLocalization.map_units _ s
      have hmk : IsLocalization.mk' ↥(v.valuationSubringAtPrime F) a s * algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) (s : ↥(integralClosure O F)) = algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) a :=
        IsLocalization.mk'_spec ↥(v.valuationSubringAtPrime F) a s
      have key : algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) (s : ↥(integralClosure O F)) * (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) (a * t) - IsLocalization.mk' ↥(v.valuationSubringAtPrime F) a s) =
          algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) ((s : ↥(integralClosure O F)) * (a * t) - a) := by
        rw [map_sub, map_mul (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F)) (s : ↥(integralClosure O F)) (a * t), mul_sub,
          mul_comm (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) (s : ↥(integralClosure O F))) (IsLocalization.mk' ↥(v.valuationSubringAtPrime F) a s), hmk]
      rw [← Ideal.unit_mul_mem_iff_mem _ hu, key]
      refine (hkerW _).mp ?_
      have h1 : t * (s : ↥(integralClosure O F)) = 1 - i := eq_sub_of_add_eq hti
      have h2 : (s : ↥(integralClosure O F)) * (a * t) - a = -(a * i) := by
        rw [mul_comm (s : ↥(integralClosure O F)) (a * t), mul_assoc, h1, mul_sub, mul_one, sub_sub_cancel_left]
      rw [h2]
      exact v.asIdeal.neg_mem (v.asIdeal.mul_mem_left a hi)
    let jW : (↥(integralClosure O F) ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField ↥(v.valuationSubringAtPrime F) := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
    have hliftO : ∀ a ∈ IsLocalRing.maximalIdeal O, IsLocalRing.residue O a = 0 :=
      fun a ha => (IsLocalRing.residue_eq_zero_iff a).mpr ha
    let iO₀ : (O ⧸ IsLocalRing.maximalIdeal O) →+* IsLocalRing.ResidueField O :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (IsLocalRing.residue O) hliftO
    have hiO : Function.Bijective iO₀ :=
      ⟨by
        rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Ideal.Quotient.lift_mk, IsLocalRing.residue_eq_zero_iff] at hx
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx, fun z => by
        obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective z
        exact ⟨Ideal.Quotient.mk _ u, Ideal.Quotient.lift_mk _ _ _⟩⟩
    let iO : (O ⧸ IsLocalRing.maximalIdeal O) ≃+* IsLocalRing.ResidueField O := RingEquiv.ofBijective iO₀ hiO
    have hc : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField ↥(v.valuationSubringAtPrime F))).comp iO.toRingHom =
        jW.toRingHom.comp (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) (↥(integralClosure O F) ⧸ v.asIdeal)) := by
      refine RingHom.ext fun x => ?_
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.comp_apply, RingHom.comp_apply]
      have e1 : iO.toRingHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) u) = IsLocalRing.residue O u := by
        show iO₀ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) u) = _
        exact Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal O) (IsLocalRing.residue O) hliftO
      have e2 : (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) (↥(integralClosure O F) ⧸ v.asIdeal)) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) u) =
          Ideal.Quotient.mk v.asIdeal (algebraMap O ↥(integralClosure O F) u) := rfl
      have e3 : jW.toRingHom (Ideal.Quotient.mk v.asIdeal (algebraMap O ↥(integralClosure O F) u)) =
          IsLocalRing.residue _ (algebraMap ↥(integralClosure O F) ↥(v.valuationSubringAtPrime F) (algebraMap O ↥(integralClosure O F) u)) := hψmk _
      rw [e1, e2, e3, hres]
      congr 1
      apply Subtype.ext
      rw [halg, IsScalarTower.algebraMap_apply O ↥(integralClosure O F) F]
      rfl
    rw [Algebra.finrank_eq_of_equiv_equiv iO jW hc]
    exact hf

  obtain ⟨-, -, -, -, h5, -⟩ :=
    IsDiscreteValuationRing.primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
      (O := O) (F := F) E (ι := Unit) (fun _ => v.asIdeal) (hprime := fun _ => hvp) (fun _ => v.ne_bot)
      (hover := fun _ => hover) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => Module.finrank E F) (fun _ => hd) (by simp)
  obtain ⟨_, hW'eq⟩ := h5 W' hW' hOW' hmW'
  rw [hW'eq, hWeq]

end S_IsDiscreteValuationRing_valuationSubring_eq_of_finrank_le_finrank_residueField
end P2MW
export P2MW.S_IsDiscreteValuationRing_valuationSubring_eq_of_finrank_le_finrank_residueField (solution)
