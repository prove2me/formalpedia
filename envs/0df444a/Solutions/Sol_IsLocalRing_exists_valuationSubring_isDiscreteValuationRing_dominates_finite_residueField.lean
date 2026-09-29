-- Prove2me | solution 1 for IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/74886eff-cdc3-595c-84da-9b64e1e57cec

import Mathlib
import Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
import Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField

set_option autoImplicit false

universe u v w

open IsLocalRing

namespace DvrDomFinGC5

theorem finite_of_isFiniteLength {A : Type u} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)]
    {M : Type v} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) : Finite M := by
  induction hM with
  | of_subsingleton => infer_instance
  | @of_simple_quotient M _ _ N hsimp hN ih =>

    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimp
    have hI' : I = maximalIdeal A := (IsLocalRing.eq_maximalIdeal hI)
    haveI : Finite (A ⧸ I) := by rw [hI']; exact ‹Finite (ResidueField A)›
    haveI : Finite (M ⧸ N) := Finite.of_equiv _ e.toEquiv.symm
    haveI : Finite N := ih

    have hs : Function.Surjective (N.mkQ) := Submodule.mkQ_surjective N
    choose s hs' using hs
    refine Finite.of_injective (fun m : M => (⟨m - s (N.mkQ m), ?_⟩, N.mkQ m) : M → N × (M ⧸ N)) ?_
    · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]
    · intro m m' h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h2] at h1
      exact sub_left_inj.mp h1

end DvrDomFinGC5

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1)
    [Finite (ResidueField A)]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ a : A, algebraMap A L a ∈ V) ∧
      (∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A L a ∈ V.nonunits) ∧
      Finite (ResidueField ↥V) := by
  classical

  have hA' : ¬ IsField A := fun hF => by
    have h0 : ringKrullDim A = 0 := by
      letI := hF.toField
      exact ringKrullDim_eq_zero_of_field A
    rw [h0] at hA; exact zero_ne_one hA
  haveI : Ring.KrullDimLE 1 A := (Ring.krullDimLE_iff).mpr hA.le

  obtain ⟨V₀, hV₀, hAV₀, hmV₀⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hA' K
  obtain ⟨V, hV, hV₀V, hmV₀V⟩ :=
    ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional (E := L) V₀ hV₀
  have hAV : ∀ a : A, algebraMap A L a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply A K L]; exact hV₀V _ (hAV₀ a)
  have hdom : ∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A L a ∈ V.nonunits := by
    intro a
    constructor
    · intro ha
      rw [IsScalarTower.algebraMap_apply A K L]
      have h1 : algebraMap A K a ∈ V₀.nonunits := (hmV₀ a).mp ha
      obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h1
      exact hmV₀V ⟨algebraMap A K a, hmem⟩ hmax
    · intro ha
      by_contra hna
      have hu : IsUnit a := by
        rwa [mem_maximalIdeal, mem_nonunits_iff, not_not] at hna
      obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp ha
      apply (mem_maximalIdeal _).mp hmax
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      refine ⟨⟨⟨algebraMap A L a, hmem⟩, ⟨algebraMap A L b, hAV b⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext; show algebraMap A L a * algebraMap A L b = 1; rw [← map_mul, hb, map_one]
      · apply Subtype.ext; show algebraMap A L b * algebraMap A L a = 1; rw [← map_mul, mul_comm, hb, map_one]
  refine ⟨V, hV, hAV, hdom, ?_⟩

  let VB : Subalgebra A L :=
    { carrier := V
      mul_mem' := fun hx hy => V.mul_mem _ _ hx hy
      one_mem' := V.one_mem
      add_mem' := fun hx hy => V.add_mem _ _ hx hy
      zero_mem' := V.zero_mem
      algebraMap_mem' := hAV }
  obtain ⟨-, -, hKA⟩ :=
    Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (K := K) VB

  let e : ↥VB ≃+* ↥V := RingEquiv.subsemiringCongr rfl
  have hJ : (maximalIdeal ↥V).comap e.toRingHom ≠ ⊥ := by
    intro h
    apply IsDiscreteValuationRing.not_a_field ↥V
    have : maximalIdeal ↥V = ((maximalIdeal ↥V).comap e.toRingHom).map e.toRingHom :=
      (Ideal.map_comap_of_surjective _ e.surjective _).symm
    rw [this, h, Ideal.map_bot]
  have hfl := hKA _ hJ
  haveI : Finite (↥VB ⧸ (maximalIdeal ↥V).comap e.toRingHom) := DvrDomFinGC5.finite_of_isFiniteLength hfl
  exact Finite.of_surjective (Ideal.quotientMap (maximalIdeal ↥V) e.toRingHom le_rfl)
    (Ideal.quotientMap_surjective e.surjective)

end S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
end P2MW
export P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField (solution)
