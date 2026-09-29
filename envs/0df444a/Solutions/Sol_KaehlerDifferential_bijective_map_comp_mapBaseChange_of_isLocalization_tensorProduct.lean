-- Prove2me | solution 1 for KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b585d6aa-4bbc-53cf-99dc-13bd47b45f5b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    (R A A' B C : Type u) [CommRing R] [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    [Algebra R C] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A A' C] [IsScalarTower R A' C]
    (M : Submonoid A) [IsLocalization M A']
    [Algebra (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C]
    (hB : (algebraMap (A ⊗[R] B) C).comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (N : Submonoid (A ⊗[R] B)) [IsLocalization N C] :
    Function.Bijective
      ((KaehlerDifferential.map R A' C C).restrictScalars C ∘ₗ KaehlerDifferential.mapBaseChange R B C) := by
  classical
  set P := A ⊗[R] B with hP
  letI : Algebra B P := Algebra.TensorProduct.rightAlgebra
  have hBP : ∀ b : B, algebraMap B P b = (1 : A) ⊗ₜ[R] b := fun b => rfl
  haveI : IsScalarTower B P C := IsScalarTower.of_algebraMap_eq fun b => by
    rw [hBP]
    exact (congrArg (fun f : B →+* C => f b) hB).symm
  haveI : SMulCommClass A' B C := ⟨fun a b c => by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩
  haveI : SMulCommClass A B C := ⟨fun a b c => by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

  let e1 : C ⊗[B] Ω[B⁄R] ≃ₗ[C] C ⊗[P] (P ⊗[B] Ω[B⁄R]) :=
    (AlgebraTensorModule.cancelBaseChange B P C C Ω[B⁄R]).symm
  let e2 : C ⊗[P] (P ⊗[B] Ω[B⁄R]) ≃ₗ[C] C ⊗[P] Ω[P⁄A] :=
    AlgebraTensorModule.congr (LinearEquiv.refl C C) (KaehlerDifferential.tensorKaehlerEquiv R A B P)
  have hbc : IsBaseChange C (KaehlerDifferential.map A A P C) :=
    (isLocalizedModule_iff_isBaseChange N C _).mp inferInstance
  let e3 : C ⊗[P] Ω[P⁄A] ≃ₗ[C] Ω[C⁄A] := hbc.equiv
  haveI : Algebra.FormallyUnramified A A' := Algebra.FormallyUnramified.of_isLocalization M
  have hinj4 : Function.Injective (KaehlerDifferential.map A A' C C) := by
    have hex := KaehlerDifferential.exact_mapBaseChange_map A A' C
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    have : y = 0 := Subsingleton.elim _ _
    rw [this, map_zero]
  let e4 : Ω[C⁄A] ≃ₗ[C] Ω[C⁄A'] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map A A' C C) ⟨hinj4, KaehlerDifferential.map_surjective A A' C⟩
  let Φ : C ⊗[B] Ω[B⁄R] ≃ₗ[C] Ω[C⁄A'] := e1 ≪≫ₗ e2 ≪≫ₗ e3 ≪≫ₗ e4

  set F := (KaehlerDifferential.map R A' C C).restrictScalars C ∘ₗ KaehlerDifferential.mapBaseChange R B C with hF
  have hFD : ∀ b : B, F ((1 : C) ⊗ₜ[B] KaehlerDifferential.D R B b) = KaehlerDifferential.D A' C (algebraMap B C b) := by
    intro b
    rw [hF, LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul, LinearMap.coe_restrictScalars,
      KaehlerDifferential.map_D, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply]
  have hΦD : ∀ b : B, Φ ((1 : C) ⊗ₜ[B] KaehlerDifferential.D R B b) = KaehlerDifferential.D A' C (algebraMap B C b) := by
    intro b
    simp only [Φ, e1, e2, e3, e4, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul,
      IsBaseChange.equiv_tmul, KaehlerDifferential.map_D, LinearEquiv.ofBijective_apply]
    rw [← IsScalarTower.algebraMap_apply B P C b, Algebra.algebraMap_self, RingHom.id_apply]
  have hFΦ : F = Φ.toLinearMap := by
    apply AlgebraTensorModule.ext
    intro c ω
    have h1 : c ⊗ₜ[B] ω = c • ((1 : C) ⊗ₜ[B] ω) := by rw [smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, map_smul]
    congr 1

    have key : (F.restrictScalars B) ∘ₗ (TensorProduct.mk B C Ω[B⁄R] 1) =
        (Φ.toLinearMap.restrictScalars B) ∘ₗ (TensorProduct.mk B C Ω[B⁄R] 1) := by
      apply Derivation.liftKaehlerDifferential_unique
      refine Derivation.ext fun b => ?_
      change F ((1 : C) ⊗ₜ[B] KaehlerDifferential.D R B b) = Φ ((1 : C) ⊗ₜ[B] KaehlerDifferential.D R B b)
      rw [hFD, hΦD]
    exact congrArg (fun g => g ω) key
  rw [hFΦ]
  exact Φ.bijective

end S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
end P2MW
export P2MW.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct (solution)
