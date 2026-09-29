-- Prove2me | solution 1 for IsGalois.of_bijective_tensorProduct_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ea6b061e-f94c-51d9-b00d-e8831925c7a6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsGalois_of_bijective_tensorProduct_lift

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {K₁ K E F : Type*} [Field K₁] [Field K] [Field E] [Field F]
    [Algebra K₁ K] [FiniteDimensional K₁ K] [IsGalois K₁ K]
    [Algebra K₁ E] [Algebra E F] [Algebra K F] [Algebra K₁ F]
    [IsScalarTower K₁ E F] [IsScalarTower K₁ K F]
    (h : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
        (fun _ _ => Commute.all _ _) : E ⊗[K₁] K →ₐ[E] F)) :
    FiniteDimensional E F ∧ IsGalois E F ∧
      Nonempty ((F ≃ₐ[E] F) ≃* (K ≃ₐ[K₁] K)) ∧
      Module.finrank E F = Module.finrank K₁ K := by
  classical
  set L : E ⊗[K₁] K →ₐ[E] F := Algebra.TensorProduct.lift (Algebra.ofId E F)
    (IsScalarTower.toAlgHom K₁ K F) (fun _ _ => Commute.all _ _) with hLdef

  let eL : (E ⊗[K₁] K) ≃ₗ[E] F := LinearEquiv.ofBijective L.toLinearMap h
  haveI hfin : FiniteDimensional E F := Module.Finite.of_surjective eL.toLinearMap eL.surjective
  have hrank : Module.finrank E F = Module.finrank K₁ K := by
    rw [← eL.finrank_eq, Module.finrank_baseChange]

  let gE : E →ₐ[K₁] F := IsScalarTower.toAlgHom K₁ E F
  let gK : K →ₐ[K₁] F := IsScalarTower.toAlgHom K₁ K F
  let Ef : IntermediateField K₁ F := IntermediateField.map gE ⊤
  let Kf : IntermediateField K₁ F := IntermediateField.map gK ⊤
  let eK : K ≃ₐ[K₁] Kf := IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ gK)
  let eE : E ≃ₐ[K₁] Ef := IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ gE)
  haveI : IsGalois K₁ Kf := IsGalois.of_algEquiv eK
  haveI : FiniteDimensional K₁ Kf := LinearEquiv.finiteDimensional eK.toLinearEquiv
  have hmemE : ∀ e : E, algebraMap E F e ∈ Ef := fun e =>
    (IntermediateField.mem_map ⊤).mpr ⟨e, IntermediateField.mem_top, rfl⟩
  have hmemK : ∀ k : K, algebraMap K F k ∈ Kf := fun k =>
    (IntermediateField.mem_map ⊤).mpr ⟨k, IntermediateField.mem_top, rfl⟩
  have hsup : Kf ⊔ Ef = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, rfl⟩ := h.2 x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul e k =>
        rw [Algebra.TensorProduct.lift_tmul]
        refine mul_mem ?_ ?_
        · exact (le_sup_right : Ef ≤ Kf ⊔ Ef) (hmemE e)
        · exact (le_sup_left : Kf ≤ Kf ⊔ Ef) (hmemK k)
    | add a b ha hb =>
        rw [map_add]
        exact add_mem (ha trivial) (hb trivial)
  haveI hGal' : IsGalois Ef F := IsGalois.sup_right Kf Ef hsup
  have hcomm : (algebraMap E F).comp (eE.symm : ↥Ef ≃+* E).toRingHom =
      ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap (↥Ef) F) := by
    ext x
    obtain ⟨y, rfl⟩ := eE.surjective x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply, RingEquiv.refl_apply]
    show algebraMap E F y = ((IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ gE)) y : F)
    rw [AlgEquiv.trans_apply, IntermediateField.coe_equivMap_apply, IntermediateField.topEquiv_symm_apply_coe]
    rfl
  have hGal : IsGalois E F :=
    IsGalois.of_equiv_equiv (F := ↥Ef) (E := F) (f := (eE.symm : ↥Ef ≃+* E)) (g := RingEquiv.refl F) hcomm

  haveI : Normal K₁ K := inferInstance
  let ψ : (F ≃ₐ[E] F) →* (K ≃ₐ[K₁] K) := IntermediateField.restrictRestrictAlgEquivMapHom K₁ K E F
  have hψ : ∀ (σ : F ≃ₐ[E] F) (x : K), algebraMap K F (ψ σ x) = σ (algebraMap K F x) := by
    intro σ x
    exact AlgEquiv.restrictNormal_commutes (MulSemiringAction.toAlgAut (F ≃ₐ[E] F) K₁ F σ) K x
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ

    have key : (σ : F →ₐ[E] F).comp L = (AlgHom.id E F).comp L := by
      apply Algebra.TensorProduct.ext
      · exact AlgHom.ext fun e => by
          simp [hLdef, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
      · ext k
        have := hψ σ k
        rw [hσ] at this
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
          Algebra.TensorProduct.includeRight_apply, AlgHom.coe_coe, AlgHom.id_comp]
        rw [hLdef, Algebra.TensorProduct.lift_tmul]
        simpa using this.symm
    apply AlgEquiv.ext
    intro y
    obtain ⟨t, rfl⟩ := h.2 y
    have := congrArg (fun φ => φ t) key
    simpa using this
  have hcard : Nat.card (K ≃ₐ[K₁] K) ≤ Nat.card (F ≃ₐ[E] F) := by
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hrank]
  have hbij : Function.Bijective ψ := hinj.bijective_of_nat_card_le hcard
  exact ⟨hfin, hGal, ⟨MulEquiv.ofBijective ψ hbij⟩, hrank⟩

end S_IsGalois_of_bijective_tensorProduct_lift
end P2MW
export P2MW.S_IsGalois_of_bijective_tensorProduct_lift (solution)
