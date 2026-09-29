-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/36e087f2-a3a9-57cb-a411-909abaa3892c

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_IsDiscreteValuationRing_exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free
import Theorems.Thm_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_sub_const_mem_maximalIdeal
import Theorems.Thm_Algebra_Etale_exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing
open scoped TensorProduct

noncomputable section

namespace CoefUpAux

section Generic

theorem isLocalHom_of_finite {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsLocalHom (algebraMap R S) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine ⟨fun r hr => ?_⟩
  by_contra hnu
  have hmem : r ∈ maximalIdeal R := hnu
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal S))
  rw [← hcomap, Ideal.mem_comap] at hmem
  exact hmem hr

theorem etale_of_ringEquiv_base {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (e : R ≃+* S) (he : ∀ r, e r = algebraMap R S r) [Algebra.Etale R T] : Algebra.Etale S T := by
  let e' : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun r => by rw [he]; rfl)
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.of_equiv e'
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.equiv inferInstance e'
  haveI : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_restrictScalars (R := R)
  haveI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

end Generic

section Model

variable (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [IsAdicComplete (maximalIdeal W) W] (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 0 < E)

include hπ hE in
theorem not_isUnit_pow : ¬ IsUnit (π ^ E) := by
  rw [isUnit_pow_iff (Nat.pos_iff_ne_zero.mp hE)]
  exact hπ.not_isUnit

include hπ hE in
theorem isLocalRing_model : IsLocalRing (UVCrossingModel W (π ^ E)) :=
  UVCrossingModel.isLocalRing_of_not_isUnit (not_isUnit_pow W π hπ E hE)

theorem algebraMap_model_apply (w : W) : algebraMap W (UVCrossingModel W (π ^ E)) w = const (π ^ E) w := rfl

include hπ hE in
theorem isLocalHom_model [IsLocalRing (UVCrossingModel W (π ^ E))] :
    IsLocalHom (algebraMap W (UVCrossingModel W (π ^ E))) := by
  refine ⟨fun w hw => ?_⟩
  by_contra hnu
  have hmem : const (π ^ E) w ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair (not_isUnit_pow W π hπ E hE)]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hnu)
  exact hmem hw

include hπ hE in
theorem residue_model_bijective [IsLocalRing (UVCrossingModel W (π ^ E))]
    [IsLocalHom (algebraMap W (UVCrossingModel W (π ^ E)))] :
    Function.Bijective (algebraMap (ResidueField W) (ResidueField (UVCrossingModel W (π ^ E)))) := by
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective x
  obtain ⟨w, hw⟩ := UVCrossingModel.exists_sub_const_mem_maximalIdeal (not_isUnit_pow W π hπ E hE) x
  refine ⟨residue W w, ?_⟩
  rw [ResidueField.algebraMap_residue, algebraMap_model_apply, eq_comm, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff]
  exact hw

end Model

section Cast

variable {W' : Type u} [CommRing W'] {a b : W'} (h : a = b)

def castEq : UVCrossingModel W' a ≃ₐ[W'] UVCrossingModel W' b :=
  Ideal.quotientEquivAlgOfEq W' (by rw [h])

theorem castEq_mk (f : MvPowerSeries (Fin 2) W') : castEq h (UVCrossingModel.mk a f) = UVCrossingModel.mk b f :=
  Ideal.quotientEquivAlgOfEq_mk W' _ f

theorem castEq_U : castEq h (U a) = U b := castEq_mk h _
theorem castEq_V : castEq h (V a) = V b := castEq_mk h _
theorem castEq_const (w : W') : castEq h (const a w) = const b w := castEq_mk h _

end Cast

end CoefUpAux

end

open CoefUpAux ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 0 < E)
    (R₀ : Type u) [CommRing R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    (e₀ : R₀ ≃+* UVCrossingModel W (π ^ E))
    (B₁ : Type u) [CommRing B₁] [IsLocalRing B₁] [Algebra R₀ B₁] [Module.Finite R₀ B₁]
    [FaithfulSMul R₀ B₁] [Algebra.Etale R₀ B₁] :
    ∃ (W' : Type u) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W') (σ' : W →+* W')
      (_ : IsLocalRing.maximalIdeal W' = Ideal.span {σ' π})
      (e : B₁ ≃+* UVCrossingModel W' ((σ' π) ^ E)),
      (∀ (r : R₀) (w : W), e₀ r = const (π ^ E) w →
          e (algebraMap R₀ B₁ r) = const ((σ' π) ^ E) (σ' w)) ∧
      (∀ b : B₁, ∃ w' : W', b - e.symm (const ((σ' π) ^ E) w') ∈ IsLocalRing.maximalIdeal B₁) ∧
      e (algebraMap R₀ B₁ (e₀.symm (U (π ^ E)))) = U ((σ' π) ^ E) ∧
      e (algebraMap R₀ B₁ (e₀.symm (V (π ^ E)))) = V ((σ' π) ^ E) := by
  classical

  haveI hMloc : IsLocalRing (UVCrossingModel W (π ^ E)) := isLocalRing_model W π hπ E hE
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ E)) := UVCrossingModel.isNoetherianRing (π ^ E)
  haveI : IsAdicComplete (maximalIdeal (UVCrossingModel W (π ^ E))) (UVCrossingModel W (π ^ E)) :=
    UVCrossingModel.isAdicComplete_maximalIdeal (π ^ E)
  haveI : IsLocalHom (algebraMap W (UVCrossingModel W (π ^ E))) := isLocalHom_model W π hπ E hE
  have hκWM := residue_model_bijective W π hπ E hE

  letI algRM : Algebra R₀ (UVCrossingModel W (π ^ E)) := e₀.toRingHom.toAlgebra
  letI algMB : Algebra (UVCrossingModel W (π ^ E)) B₁ :=
    ((algebraMap R₀ B₁).comp (e₀.symm : UVCrossingModel W (π ^ E) →+* R₀)).toAlgebra
  have halgMB : ∀ m, algebraMap (UVCrossingModel W (π ^ E)) B₁ m = algebraMap R₀ B₁ (e₀.symm m) :=
    fun m => rfl
  haveI : IsScalarTower R₀ (UVCrossingModel W (π ^ E)) B₁ := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [halgMB]
    show algebraMap R₀ B₁ r = algebraMap R₀ B₁ (e₀.symm (e₀ r))
    rw [RingEquiv.symm_apply_apply])
  haveI : Module.Finite (UVCrossingModel W (π ^ E)) B₁ := Module.Finite.of_restrictScalars_finite R₀ _ B₁
  haveI : Algebra.Etale (UVCrossingModel W (π ^ E)) B₁ := etale_of_ringEquiv_base e₀ (fun r => rfl)
  haveI : IsLocalHom (algebraMap (UVCrossingModel W (π ^ E)) B₁) := isLocalHom_of_finite
  letI algWB : Algebra W B₁ :=
    ((algebraMap (UVCrossingModel W (π ^ E)) B₁).comp (algebraMap W (UVCrossingModel W (π ^ E)))).toAlgebra
  haveI : IsScalarTower W (UVCrossingModel W (π ^ E)) B₁ :=
    IsScalarTower.of_algebraMap_eq (R := W) (S := UVCrossingModel W (π ^ E)) (A := B₁) (fun _ => rfl)
  haveI : IsLocalHom (algebraMap W B₁) := by
    rw [IsScalarTower.algebraMap_eq W (UVCrossingModel W (π ^ E)) B₁]
    exact RingHom.isLocalHom_comp _ _

  haveI : IsScalarTower (ResidueField W) (ResidueField (UVCrossingModel W (π ^ E))) (ResidueField B₁) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      obtain ⟨w, rfl⟩ := residue_surjective x
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
        IsScalarTower.algebraMap_apply W (UVCrossingModel W (π ^ E)) B₁])
  let eκ : ResidueField W ≃ₐ[ResidueField W] ResidueField (UVCrossingModel W (π ^ E)) :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hκWM
  haveI : Module.Finite (ResidueField W) (ResidueField (UVCrossingModel W (π ^ E))) :=
    Module.Finite.equiv eκ.toLinearEquiv
  haveI : Algebra.IsSeparable (ResidueField W) (ResidueField (UVCrossingModel W (π ^ E))) :=
    AlgEquiv.Algebra.isSeparable eκ
  haveI : FiniteDimensional (ResidueField W) (ResidueField B₁) :=
    Module.Finite.trans (ResidueField (UVCrossingModel W (π ^ E))) (ResidueField B₁)
  haveI : Algebra.IsSeparable (ResidueField W) (ResidueField B₁) :=
    Algebra.IsSeparable.trans (ResidueField W) (ResidueField (UVCrossingModel W (π ^ E))) (ResidueField B₁)

  obtain ⟨W', _i1, _i2, _i3, hcompl, _i5, _i6, hfree, _i8, _i9, het, ι, hmap, hres, -, -, -⟩ :=
    IsDiscreteValuationRing.exists_etale_dvr_residueField_equiv_card_algEquiv_eq_of_isAdicComplete W
      (ResidueField B₁)
  haveI := hfree
  haveI := het
  have hσ' : maximalIdeal W' = Ideal.span {algebraMap W W' π} := by
    rw [← hmap, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hπ'0 : algebraMap W W' π ≠ 0 := fun h0 =>
    hπ.ne_zero ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective W W')).mp h0)
  have hπ' : Irreducible (algebraMap W W' π) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hπ'0 hσ'

  haveI hM'loc : IsLocalRing (UVCrossingModel W' ((algebraMap W W' π) ^ E)) := isLocalRing_model W' _ hπ' E hE
  haveI : IsLocalHom (algebraMap W' (UVCrossingModel W' ((algebraMap W W' π) ^ E))) :=
    isLocalHom_model W' _ hπ' E hE
  have hκW'M' := residue_model_bijective W' _ hπ' E hE
  obtain ⟨ebc, -, hbcU, hbcV, hbcC⟩ :=
    UVCrossingModel.exists_algEquiv_tensorProduct_map_of_finite_of_free W W' (π ^ E)
  have hpow : algebraMap W W' (π ^ E) = (algebraMap W W' π) ^ E := map_pow _ _ _
  let ebc' : UVCrossingModel W (π ^ E) ⊗[W] W' ≃+* UVCrossingModel W' ((algebraMap W W' π) ^ E) :=
    ebc.toRingEquiv.trans (castEq hpow).toRingEquiv
  letI algMM' : Algebra (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E)) :=
    ((ebc' : UVCrossingModel W (π ^ E) ⊗[W] W' →+* UVCrossingModel W' ((algebraMap W W' π) ^ E)).comp
      (Algebra.TensorProduct.includeLeft (S := W) (R := W) (A := UVCrossingModel W (π ^ E))
        (B := W')).toRingHom).toAlgebra
  have halgMM' : ∀ m, algebraMap (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E)) m =
      castEq hpow (ebc (m ⊗ₜ[W] 1)) := fun m => rfl
  let eMM' : UVCrossingModel W (π ^ E) ⊗[W] W' ≃ₐ[UVCrossingModel W (π ^ E)]
      UVCrossingModel W' ((algebraMap W W' π) ^ E) :=
    AlgEquiv.ofRingEquiv (f := ebc') (fun m => by
      rw [halgMM', Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rfl)
  haveI : Module.Finite (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E)) :=
    Module.Finite.equiv eMM'.toLinearEquiv
  haveI : Algebra.Etale (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E)) :=
    Algebra.Etale.of_equiv (A := UVCrossingModel W (π ^ E) ⊗[W] W') eMM'
  haveI : IsLocalHom (algebraMap (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E))) :=
    isLocalHom_of_finite
  have hMM'const : ∀ w : W, algebraMap (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E))
      (const (π ^ E) w) = const ((algebraMap W W' π) ^ E) (algebraMap W W' w) := fun w => by
    rw [halgMM', hbcC, castEq_const]
  have hMM'U : algebraMap (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E))
      (U (π ^ E)) = U ((algebraMap W W' π) ^ E) := by
    rw [halgMM', hbcU, castEq_U]
  have hMM'V : algebraMap (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E))
      (V (π ^ E)) = V ((algebraMap W W' π) ^ E) := by
    rw [halgMM', hbcV, castEq_V]

  let eκ' : ResidueField W' ≃+* ResidueField (UVCrossingModel W' ((algebraMap W W' π) ^ E)) :=
    RingEquiv.ofBijective _ hκW'M'
  let e₀'' : ResidueField (UVCrossingModel W' ((algebraMap W W' π) ^ E)) ≃+* ResidueField B₁ := eκ'.symm.trans ι
  have he₀'' : ∀ w' : W', e₀'' (residue _ (const ((algebraMap W W' π) ^ E) w')) = ι (residue W' w') := by
    intro w'
    show ι (eκ'.symm (residue _ (const ((algebraMap W W' π) ^ E) w'))) = _
    congr 1
    apply eκ'.injective
    rw [RingEquiv.apply_symm_apply]
    show _ = algebraMap (ResidueField W') _ (residue W' w')
    rw [ResidueField.algebraMap_residue]
    rfl
  let e₀' : ResidueField (UVCrossingModel W' ((algebraMap W W' π) ^ E)) ≃ₐ[ResidueField (UVCrossingModel W (π ^ E))]
      ResidueField B₁ :=
    AlgEquiv.ofRingEquiv (f := e₀'') (fun x => by
      obtain ⟨x, rfl⟩ := hκWM.2 x
      obtain ⟨w, rfl⟩ := residue_surjective x
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
        algebraMap_model_apply, hMM'const, he₀'', hres, ResidueField.algebraMap_residue,
        IsScalarTower.algebraMap_apply W (UVCrossingModel W (π ^ E)) B₁]
      rfl)

  obtain ⟨e', he'⟩ := Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
    (UVCrossingModel W (π ^ E)) (UVCrossingModel W' ((algebraMap W W' π) ^ E)) B₁ e₀'
  refine ⟨W', inferInstance, inferInstance, inferInstance, hcompl, algebraMap W W', hσ', e'.symm.toRingEquiv,
    ?_, ?_, ?_, ?_⟩
  · intro r w hrw
    apply e'.injective
    show e' (e'.symm (algebraMap R₀ B₁ r)) = _
    rw [AlgEquiv.apply_symm_apply, ← hMM'const, ← hrw]
    have : algebraMap R₀ B₁ r = algebraMap (UVCrossingModel W (π ^ E)) B₁ (e₀ r) := by
      rw [halgMB, RingEquiv.symm_apply_apply]
    rw [this]
    exact (e'.commutes (e₀ r)).symm
  · intro b
    obtain ⟨w', hw'⟩ := UVCrossingModel.exists_sub_const_mem_maximalIdeal
      (not_isUnit_pow W' _ hπ' E hE) (e'.symm b)
    refine ⟨w', ?_⟩
    show b - e' (const _ w') ∈ maximalIdeal B₁
    have h1 : b - e' (const _ w') = e' (e'.symm b - const _ w') := by
      rw [map_sub, AlgEquiv.apply_symm_apply]
    rw [h1]
    intro hu
    exact hw' ((isUnit_map_iff e' _).mp hu)
  · apply e'.injective
    show e' (e'.symm _) = _
    rw [AlgEquiv.apply_symm_apply, ← hMM'U, AlgEquiv.commutes, halgMB]
  · apply e'.injective
    show e' (e'.symm _) = _
    rw [AlgEquiv.apply_symm_apply, ← hMM'V, AlgEquiv.commutes, halgMB]

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_etale_of_isLocalRing_of_isAdicComplete (solution)
