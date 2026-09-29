-- Prove2me | solution 1 for NumberField.SArchIdele.injective_comp_toSIdele_and_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cc1d62d9-146d-530f-bf83-6ed13829efd3

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

namespace P2MW.S_NumberField_SArchIdele_injective_comp_toSIdele_and_mem_range_iff

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
          (NumberField.ArchIdele.above E K v).Completion)) :
    Function.Injective (fun y : NumberField.SArchIdele.obj E K S => Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)) ∧
    ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      (∃ y : NumberField.SArchIdele.obj E K S, Φ ((NumberField.SArchIdele.toSIdele E K S).hom y) = Additive.ofMul z) ↔
        ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → finPart w z = 1 := by
  have hinjT : Function.Injective (fun y : NumberField.SArchIdele.obj E K S => Φ ((NumberField.SArchIdele.toSIdele E K S).hom y)) :=
    fun y₁ y₂ h => NumberField.SArchIdele.toSIdele_injective E K S (hΦinj h)

  have hread : ∀ (x : NumberField.SIdele.obj E K S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 K)) (y : K ≃ₐ[E] K)
      (hy : y • w = NumberField.PlaceAbove.above E K v.1),
      (((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 ↔ (x (Sum.inl (Sum.inr v))).1 y = 0) := by
    intro x v w y hy
    have h := hΦout x v w y hy
    constructor
    · intro h1
      rw [h1, map_one] at h
      have hu : (Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
          ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) = 1 := by
        apply Units.ext
        apply Subtype.ext
        rw [Units.val_one, OneMemClass.coe_one]
        exact h.symm
      exact Additive.toMul.injective (hu.trans rfl)
    · intro h0
      rw [h0] at h
      have h' : NumberField.PlaceTransport.transport y hy
          ((((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w)) = 1 := h
      exact (NumberField.PlaceTransport.transport y hy).injective (h'.trans (map_one _).symm)

  have htrans : ∀ w : HeightOneSpectrum (𝓞 K), ∃ y : K ≃ₐ[E] K, y • w = NumberField.PlaceAbove.above E K (w.under (𝓞 E)) := by
    intro w
    have hmem : NumberField.PlaceAbove.above E K (w.under (𝓞 E)) ∈ MulAction.orbit (K ≃ₐ[E] K) w := by
      rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K w]
      exact NumberField.SUnits.under_above E K _
    exact MulAction.mem_orbit_iff.1 hmem
  refine ⟨hinjT, fun z => ⟨?_, ?_⟩⟩
  ·
    rintro ⟨y, hy⟩ w hw
    obtain ⟨σ, hσ⟩ := htrans w
    have h1 := (hread ((NumberField.SArchIdele.toSIdele E K S).hom y) ⟨w.under (𝓞 E), hw⟩ w σ hσ).2 rfl
    rw [hy, toMul_ofMul] at h1
    exact Units.val_eq_one.1 (by rw [M4aHerbrand.coe_finPart_apply]; exact h1)
  ·
    intro hz

    have hzmem : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
      rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
      intro w hw
      have h1 : ((z : AdeleRing (𝓞 K) K).2 w) = 1 := by
        rw [← M4aHerbrand.coe_finPart_apply, hz w hw, Units.val_one]
      have h2 : ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 := by
        rw [← M4aHerbrand.coe_finPart_apply, map_inv, hz w hw, inv_one, Units.val_one]
      refine ⟨?_, ?_⟩
      · change ((z : AdeleRing (𝓞 K) K).2) w ∈ _
        rw [h1]; exact one_mem _
      · rw [← map_inv]
        change ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w ∈ _
        rw [h2]; exact one_mem _
    have hzrange : Additive.ofMul z ∈ Φ.range := by
      rw [hΦrange]
      exact hzmem
    obtain ⟨x, hx⟩ := hzrange

    have hxout : ∀ v : {v // v ∉ S}, x (Sum.inl (Sum.inr v)) = 0 := by
      intro v
      apply Subtype.ext
      funext σ
      set w : HeightOneSpectrum (𝓞 K) := σ⁻¹ • NumberField.PlaceAbove.above E K v.1 with hwdef
      have hσ : σ • w = NumberField.PlaceAbove.above E K v.1 := by rw [hwdef, smul_inv_smul]
      have hwS : w.under (𝓞 E) ∉ S := by
        rw [hwdef, NumberField.PlaceTransport.under_smul, NumberField.SUnits.under_above]
        exact v.2
      have h1 := (hread x v w σ hσ).1 (by rw [hx, toMul_ofMul, ← M4aHerbrand.coe_finPart_apply, hz w hwS, Units.val_one])
      exact h1

    let y : NumberField.SArchIdele.obj E K S := fun i => match i with
      | Sum.inl v => x (Sum.inl (Sum.inl v))
      | Sum.inr v => x (Sum.inr v)
    refine ⟨y, ?_⟩
    rw [← hx]
    congr 1
    funext i
    rcases i with (v | v) | v
    · rfl
    · rw [NumberField.SArchIdele.toSIdele_hom_apply_inl_inr, hxout]
    · rfl

end S_NumberField_SArchIdele_injective_comp_toSIdele_and_mem_range_iff
end P2MW
export P2MW.S_NumberField_SArchIdele_injective_comp_toSIdele_and_mem_range_iff (solution)
