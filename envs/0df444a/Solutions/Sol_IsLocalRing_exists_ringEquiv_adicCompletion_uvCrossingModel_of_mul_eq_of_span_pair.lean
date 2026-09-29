-- Prove2me | solution 1 for IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/74f069cc-f344-5826-a24e-a5d05c5549ae

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsLocalRing_exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span
import Theorems.Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
import Theorems.Thm_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
import Theorems.Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace N3Body

noncomputable def mvMapEquiv {σ A B : Type*} [CommRing A] [CommRing B] (f : A ≃+* B) :
    MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
  { toFun := MvPowerSeries.map (f : A →+* B)
    invFun := MvPowerSeries.map (f.symm : B →+* A)
    left_inv := fun φ => by ext n; simp
    right_inv := fun φ => by ext n; simp
    map_mul' := fun a b => map_mul _ a b
    map_add' := fun a b => map_add _ a b }

theorem mvMapEquiv_apply {σ A B : Type*} [CommRing A] [CommRing B] (f : A ≃+* B) (φ : MvPowerSeries σ A) :
    mvMapEquiv f φ = MvPowerSeries.map (σ := σ) (f : A →+* B) φ := rfl

theorem exists_ringEquiv_uvCrossingModel_map {A B : Type*} [CommRing A] [CommRing B] (f : A ≃+* B)
    (π : A) (ϖ : B) (hπ : f π = ϖ) :
    ∃ e : UVCrossingModel A π ≃+* UVCrossingModel B ϖ,
      (∀ a : A, e (const π a) = const ϖ (f a)) ∧ e (U π) = U ϖ ∧ e (V π) = V ϖ := by
  have hIJ : uvCrossingIdeal B ϖ = (uvCrossingIdeal A π).map ((mvMapEquiv (σ := Fin 2) f : _ ≃+* _) :
      MvPowerSeries (Fin 2) A →+* MvPowerSeries (Fin 2) B) := by
    rw [uvCrossingIdeal, uvCrossingIdeal, Ideal.map_span, Set.image_singleton]
    congr 2
    change _ = MvPowerSeries.map (σ := Fin 2) (f : A →+* B) (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C π)
    rw [map_sub, map_mul, MvPowerSeries.map_X, MvPowerSeries.map_X, MvPowerSeries.map_C]
    simp [hπ]
  refine ⟨Ideal.quotientEquiv _ _ (mvMapEquiv (σ := Fin 2) f) hIJ, fun a => ?_, ?_, ?_⟩
  · change Ideal.quotientEquiv _ _ _ hIJ (Ideal.Quotient.mk _ (MvPowerSeries.C a)) = Ideal.Quotient.mk _ (MvPowerSeries.C (f a))
    rw [Ideal.quotientEquiv_mk]
    congr 1
    change MvPowerSeries.map (σ := Fin 2) (f : A →+* B) (MvPowerSeries.C a) = _
    rw [MvPowerSeries.map_C]; rfl
  · change Ideal.quotientEquiv _ _ _ hIJ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = Ideal.Quotient.mk _ (MvPowerSeries.X 0)
    rw [Ideal.quotientEquiv_mk]; congr 1
    change MvPowerSeries.map (σ := Fin 2) (f : A →+* B) (MvPowerSeries.X 0) = _
    rw [MvPowerSeries.map_X]
  · change Ideal.quotientEquiv _ _ _ hIJ (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = Ideal.Quotient.mk _ (MvPowerSeries.X 1)
    rw [Ideal.quotientEquiv_mk]; congr 1
    change MvPowerSeries.map (σ := Fin 2) (f : A →+* B) (MvPowerSeries.X 1) = _
    rw [MvPowerSeries.map_X]

end N3Body

open N3Body in
theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (ϖ : O) (hϖ : Irreducible ϖ)
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    (x y : R) (hxy : x * y = algebraMap O R ϖ)
    (hm : maximalIdeal R = Ideal.span {x, y})
    (hres : Function.Surjective ((IsLocalRing.residue R).comp (algebraMap O R)))
    (hdim : 2 ≤ ringKrullDim R) :
    ∃ ι : AdicCompletion (maximalIdeal R) R ≃+* UVCrossingModel O ϖ,
      (∀ o : O, ι (algebraMap R _ (algebraMap O R o)) = const ϖ o) ∧
      ι (algebraMap R _ x) = U ϖ ∧
      ι (algebraMap R _ y) = V ϖ := by
  classical

  obtain ⟨instDom, instDVR, instCpl, hπ'⟩ := PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖ

  have hm3 : maximalIdeal R = Ideal.span {algebraMap O R ϖ, x, y} := by
    rw [hm]
    apply le_antisymm
    · exact Ideal.span_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
    · rw [Ideal.span_le]
      rintro z (rfl | rfl | rfl)
      · rw [← hxy]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · exact Ideal.subset_span (by simp)
      · exact Ideal.subset_span (by simp)
  obtain ⟨θW, θ, hθWC, hθWX, hθsurj, hθC, hθ0, hθ1⟩ :=
    IsLocalRing.exists_surjective_mvPowerSeries_adicCompletion_of_maximalIdeal_eq_span ϖ hϖ x y hm3 hres
  have hdim' := IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le R hdim

  have hθCπ : θ (MvPowerSeries.C (Ideal.Quotient.mk _ (PowerSeries.C ϖ))) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap O R ϖ) := by
    rw [← hθWC ϖ, ← hθC]; rfl
  have hrel : θ (MvPowerSeries.X 0) * θ (MvPowerSeries.X 1) =
      θ (MvPowerSeries.C (Ideal.Quotient.mk _ (PowerSeries.C ϖ))) ^ 1 *
        ((1 : (AdicCompletion (maximalIdeal R) R)ˣ) : AdicCompletion (maximalIdeal R) R) := by
    rw [hθ0, hθ1, hθCπ, pow_one, Units.val_one, mul_one, ← map_mul, hxy]
  obtain ⟨ι', hι'C, hι'0, hι'1⟩ :=
    IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
      (Ideal.Quotient.mk _ (PowerSeries.C ϖ)) hπ' 1 le_rfl θ hθsurj 1 hrel hdim'

  obtain ⟨e14, he14⟩ := PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C ϖ hϖ
  let eOW : O ≃+* (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) :=
    ((AdicCompletion.ofAlgEquiv (maximalIdeal O)).toRingEquiv).trans e14
  have heOW : ∀ o : O, eOW o = Ideal.Quotient.mk _ (PowerSeries.C o) := fun o => by
    change e14 (AdicCompletion.ofAlgEquiv (maximalIdeal O) o) = _
    rw [AdicCompletion.ofAlgEquiv_apply]
    exact he14 o
  obtain ⟨e, heC, heU, heV⟩ := exists_ringEquiv_uvCrossingModel_map eOW.symm
    ((Ideal.Quotient.mk _ (PowerSeries.C ϖ)) ^ 1) ϖ (by rw [pow_one, ← heOW ϖ]; exact eOW.symm_apply_apply ϖ)
  refine ⟨ι'.trans e, fun o => ?_, ?_, ?_⟩
  · change e (ι' _) = _
    have : algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap O R o) = θ (MvPowerSeries.C (eOW o)) := by
      rw [heOW, ← hθWC o, ← hθC]; rfl
    rw [this, hι'C, heC, RingEquiv.symm_apply_apply]
  · change e (ι' _) = _
    rw [← hθ0, hι'0, Units.val_one, map_one]
    simpa using heU
  · change e (ι' _) = _
    rw [← hθ1, hι'1, heV]

end S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair
end P2MW
export P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_of_span_pair (solution)
