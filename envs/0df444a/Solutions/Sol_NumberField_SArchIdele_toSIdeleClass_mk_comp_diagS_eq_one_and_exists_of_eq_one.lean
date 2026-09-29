-- Prove2me | solution 1 for NumberField.SArchIdele.toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/53cd1cd2-dd4e-5f46-8348-9ae8b94b3eec

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_SArchIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport

import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_SArchIdele_toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one

set_option autoImplicit false
set_option maxHeartbeats 3200000
open IsDedekindDomain NumberField M4aHerbrand
open scoped NumberField.PlaceTransport

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hΦS : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦout : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      NumberField.PlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) =
        (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
            (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K))
    (hΦinf : ∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.ArchIdele.above E K v),
      NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) =
        ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E K v).Completion)ˣ) :
          (NumberField.ArchIdele.above E K v).Completion))
    (hΦdiag : ∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
      Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) :
    (∀ x : NumberField.SUnits.sUnitsRep E K S,
      toSIdeleClass (𝓞 K) K {w | w.under (𝓞 E) ∈ S}
        (QuotientGroup.mk (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom x))))) = 1) ∧
    (∀ y : NumberField.SArchIdele.obj E K S,
      toSIdeleClass (𝓞 K) K {w | w.under (𝓞 E) ∈ S}
        (QuotientGroup.mk (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)))) = 1 →
      ∃ x : NumberField.SUnits.sUnitsRep E K S, (NumberField.SArchIdele.diagS E K S).hom x = y) := by
  classical

  set T : Set (HeightOneSpectrum (𝓞 K)) := {w | w.under (𝓞 E) ∈ S} with hTdef

  have hreadS : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1), (x (Sum.inl (Sum.inl v))).1 y = 0 →
      (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1) := by
    intro x v w y hy h0
    have h := hΦS x v w y hy
    rw [h0] at h
    have h' : NumberField.PlaceTransport.transport y hy
        ((((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w)) = 1 := h
    exact (NumberField.PlaceTransport.transport y hy).injective (h'.trans (map_one _).symm)
  have hreadOut : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1), (x (Sum.inl (Sum.inr v))).1 y = 0 →
      (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1) := by
    intro x v w y hy h0
    have h := hΦout x v w y hy
    rw [h0] at h
    have h' : NumberField.PlaceTransport.transport y hy
        ((((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w)) = 1 := h
    exact (NumberField.PlaceTransport.transport y hy).injective (h'.trans (map_one _).symm)
  have hreadInf : ∀ (x : NumberField.SIdele.obj E K S) (v : InfinitePlace E) (w : InfinitePlace K) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.ArchIdele.above E K v), (x (Sum.inr v)).1 y = 0 →
      (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1) := by
    intro x v w y hy h0
    have h := hΦinf x v w y hy
    rw [h0] at h
    have h' : NumberField.InfinitePlaceTransport.transport y hy
        ((((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w)) = 1 := h
    exact (NumberField.InfinitePlaceTransport.transport y hy).injective (h'.trans (map_one _).symm)

  have htrans : ∀ w : HeightOneSpectrum (𝓞 K), ∃ y : K ≃ₐ[E] K, y • w = NumberField.PlaceAbove.above E K (w.under (𝓞 E)) := by
    intro w
    have hmem : NumberField.PlaceAbove.above E K (w.under (𝓞 E)) ∈ MulAction.orbit (K ≃ₐ[E] K) w := by
      rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K w]
      exact NumberField.SUnits.under_above E K _
    exact MulAction.mem_orbit_iff.1 hmem
  have htransInf : ∀ w : InfinitePlace K, ∃ y : K ≃ₐ[E] K, y • w = NumberField.ArchIdele.above E K (w.comap (algebraMap E K)) :=
    fun w => NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (NumberField.ArchIdele.comap_above E K _).symm

  have hU : ∀ d : NumberField.SIdele.obj E K S, (∀ v : {v // v ∈ S}, d (Sum.inl (Sum.inl v)) = 0) →
      (∀ v : InfinitePlace E, d (Sum.inr v) = 0) →
      (Additive.toMul (Φ d) : (AdeleRing (𝓞 K) K)ˣ) ∈ unitIdelesTrivialOn (𝓞 K) K T := by
    intro d hdS hdinf
    refine ⟨?_, ?_, ?_⟩
    ·
      have hmem : Φ d ∈ Φ.range := ⟨d, rfl⟩
      rw [hΦrange] at hmem
      exact hmem
    ·
      apply Units.ext
      rw [coe_infPart_apply, Units.val_one]
      funext w
      obtain ⟨y, hy⟩ := htransInf w
      exact hreadInf d _ w y hy (by rw [hdinf]; rfl)
    ·
      intro w hw
      apply Units.ext
      rw [coe_finPart_apply, Units.val_one]
      obtain ⟨y, hy⟩ := htrans w
      exact hreadS d ⟨w.under (𝓞 E), hw⟩ w y hy (by rw [hdS]; rfl)

  have hdiagS : ∀ x : NumberField.SUnits.sUnitsRep E K S,
      (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom x))) : (AdeleRing (𝓞 K) K)ˣ)
        = Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x) *
          Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom x) -
            (NumberField.SIdele.diag E K S).hom x)) ∧
      (Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom x) -
            (NumberField.SIdele.diag E K S).hom x)) : (AdeleRing (𝓞 K) K)ˣ) ∈ unitIdelesTrivialOn (𝓞 K) K T := by
    intro x
    constructor
    · rw [map_sub, toMul_sub, hΦdiag, toMul_ofMul, mul_div_cancel]
    · apply hU
      · intro v
        rw [Pi.sub_apply, sub_eq_zero]
        rfl
      · intro v
        rw [Pi.sub_apply, sub_eq_zero]
        rfl
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  ·
    rw [toSIdeleClass_mk_eq_one_iff, sClassKernel]
    obtain ⟨heq, hmem⟩ := hdiagS x
    rw [heq]
    exact Subgroup.mul_mem_sup ⟨NumberField.SUnits.val E K S x, rfl⟩ hmem
  ·
    rw [toSIdeleClass_mk_eq_one_iff, sClassKernel, Subgroup.mem_sup] at hy
    obtain ⟨a, ⟨k, rfl⟩, u, hu, hz⟩ := hy
    set z : (AdeleRing (𝓞 K) K)ˣ := Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)) with hzdef

    have hz1 : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → (z : AdeleRing (𝓞 K) K).2 w = 1 := by
      intro w hw
      obtain ⟨σ, hσ⟩ := htrans w
      exact hreadOut _ ⟨w.under (𝓞 E), hw⟩ w σ hσ rfl

    have hk : k ∈ NumberField.SUnits.sUnits E K S := by
      rw [NumberField.SUnits.mem_sUnits_iff]
      intro σ w hw

      set w' : HeightOneSpectrum (𝓞 K) := σ⁻¹ • w with hw'def
      have hσw : σ • w' = w := by rw [hw'def, smul_inv_smul]
      have hw' : w'.under (𝓞 E) ∉ S := by rwa [hw'def, NumberField.PlaceTransport.under_smul]
      rw [NumberField.PlaceTransport.valuation_apply_of_smul_eq hσw]

      obtain ⟨hu1, hu2⟩ := ((mem_unitIdelesTrivialOn_iff T u).1 hu).1 w' hw'
      have hzu : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k : (AdeleRing (𝓞 K) K)ˣ) :
          AdeleRing (𝓞 K) K).2 w' * (u : AdeleRing (𝓞 K) K).2 w' = 1 := by
        have := congrArg (fun t : (AdeleRing (𝓞 K) K)ˣ => (t : AdeleRing (𝓞 K) K).2 w') hz
        simp [hz1 w' hw'] at this
        exact this
      have huinv : ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' * (u : AdeleRing (𝓞 K) K).2 w' = 1 := by
        rw [← coe_finPart_apply, ← coe_finPart_apply, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have hPk : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k : (AdeleRing (𝓞 K) K)ˣ) :
          AdeleRing (𝓞 K) K).2 w' = ((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' :=
        mul_right_cancel₀ (by intro h0; rw [h0, mul_zero] at huinv; exact zero_ne_one huinv) (hzu.trans huinv.symm)
      have hval1 : Valued.v (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w') = 1 := by
        apply le_antisymm ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hu2)
        have hle : Valued.v ((u : AdeleRing (𝓞 K) K).2 w') ≤ 1 :=
          (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hu1
        have hprod : Valued.v (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w') * Valued.v ((u : AdeleRing (𝓞 K) K).2 w') = 1 := by
          rw [← map_mul, huinv, map_one]
        by_contra hlt
        push Not at hlt
        have := mul_lt_one_of_lt_of_le hlt hle
        rw [hprod] at this
        exact lt_irrefl _ this
      have hcomp : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k : (AdeleRing (𝓞 K) K)ˣ) :
          AdeleRing (𝓞 K) K).2 w' = ((k : K) : w'.adicCompletion K) := rfl
      rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hcomp, hPk, hval1]

    set xS : NumberField.SUnits.sUnitsRep E K S := ⟨Additive.ofMul k, hk⟩ with hxSdef
    have hvalxS : NumberField.SUnits.val E K S xS = k := rfl
    obtain ⟨heq', hu'⟩ := hdiagS xS
    set u' : (AdeleRing (𝓞 K) K)ˣ := Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom xS) -
            (NumberField.SIdele.diag E K S).hom xS)) with hu'def

    have hz'1 : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S →
        ((Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom xS))) :
          (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
      intro w hw
      obtain ⟨σ, hσ⟩ := htrans w
      exact hreadOut _ ⟨w.under (𝓞 E), hw⟩ w σ hσ rfl

    have huu' : u = u' := by
      have hPu : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k * u = z := hz
      have hPu' : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k * u' =
          Additive.toMul (Φ ((NumberField.SArchIdele.toSIdele E K S).hom ((NumberField.SArchIdele.diagS E K S).hom xS))) := by
        rw [heq', hvalxS]
      apply Units.ext
      apply Prod.ext
      ·
        have h1 : (u : AdeleRing (𝓞 K) K).1 = 1 := by
          have := congrArg Units.val hu.2.1; rwa [coe_infPart_apply, Units.val_one] at this
        have h2 : (u' : AdeleRing (𝓞 K) K).1 = 1 := by
          have := congrArg Units.val hu'.2.1; rwa [coe_infPart_apply, Units.val_one] at this
        rw [h1, h2]
      · apply IsDedekindDomain.FiniteAdeleRing.ext
        intro w
        by_cases hw : w.under (𝓞 E) ∈ S
        · have h1 : (u : AdeleRing (𝓞 K) K).2 w = 1 := by
            have := congrArg Units.val (hu.2.2 w hw); rwa [coe_finPart_apply, Units.val_one] at this
          have h2 : (u' : AdeleRing (𝓞 K) K).2 w = 1 := by
            have := congrArg Units.val (hu'.2.2 w hw); rwa [coe_finPart_apply, Units.val_one] at this
          exact h1.trans h2.symm
        ·
          have e1 := congrArg (fun t : (AdeleRing (𝓞 K) K)ˣ => (t : AdeleRing (𝓞 K) K).2 w) hPu
          have e2 := congrArg (fun t : (AdeleRing (𝓞 K) K)ˣ => (t : AdeleRing (𝓞 K) K).2 w) hPu'
          simp only [Units.val_mul] at e1 e2
          rw [hz1 w hw] at e1
          rw [hz'1 w hw] at e2
          have hk0 : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k : (AdeleRing (𝓞 K) K)ˣ) :
              AdeleRing (𝓞 K) K).2 w ≠ 0 := by
            have hc : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k : (AdeleRing (𝓞 K) K)ˣ) :
                AdeleRing (𝓞 K) K).2 w = algebraMap K (w.adicCompletion K) k := by
              rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
            rw [hc]
            exact (map_ne_zero _).2 k.ne_zero
          exact mul_left_cancel₀ hk0 (e1.trans e2.symm)
    refine ⟨xS, ?_⟩
    apply NumberField.SArchIdele.toSIdele_injective E K S
    apply hΦinj
    apply Additive.toMul.injective
    change _ = z
    rw [← hz, huu', heq', hvalxS]

end S_NumberField_SArchIdele_toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one
end P2MW
export P2MW.S_NumberField_SArchIdele_toSIdeleClass_mk_comp_diagS_eq_one_and_exists_of_eq_one (solution)
