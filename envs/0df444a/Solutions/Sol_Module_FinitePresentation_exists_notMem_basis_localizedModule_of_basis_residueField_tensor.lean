-- Prove2me | solution 1 for Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/382818c5-5ca9-57df-8c77-46274afa6564

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M] [Module.FinitePresentation T M]
    (p : Ideal T) [hp : p.IsPrime] (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M)) (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) := by
  classical
  set R := Localization.AtPrime p with hR
  set Mp := LocalizedModule p.primeCompl M with hMp
  set fM : M →ₗ[T] Mp := LocalizedModule.mkLinearMap p.primeCompl M with hfM

  haveI : Module.Free R Mp := Module.mem_freeLocus.mp hfree
  haveI : Module.FinitePresentation R Mp := inferInstance

  let κ := p.ResidueField
  have hbc : IsBaseChange R fM := IsLocalizedModule.isBaseChange p.primeCompl R fM
  let E : κ ⊗[T] M ≃ₗ[κ] κ ⊗[R] Mp :=
    (AlgebraTensorModule.cancelBaseChange T R κ κ M).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl κ κ) hbc.equiv
  have hE : ∀ x : M, E ((1 : κ) ⊗ₜ[T] x) = (1 : κ) ⊗ₜ[R] fM x := by
    intro x
    simp only [E, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.congr_tmul,
      LinearEquiv.refl_apply, IsBaseChange.equiv_tmul, one_smul]
  let bp : Module.Basis ι κ (κ ⊗[R] Mp) := b.map E
  have hbp : ∀ i, bp i = (TensorProduct.mk R κ Mp 1 ∘ fun i => fM (m i)) i := by
    intro i
    simp only [bp, Module.Basis.map_apply, hb, hE, Function.comp_apply, TensorProduct.mk_apply]
  have hfun : (⇑bp : ι → κ ⊗[R] Mp) = TensorProduct.mk R κ Mp 1 ∘ fun i => fM (m i) := funext hbp
  obtain ⟨B, hB⟩ := Module.exists_basis_of_basis_baseChange (R := R) (M := Mp) (fun i => fM (m i))
    (by rw [← hfun]; exact bp.linearIndependent) (by rw [← hfun]; exact bp.span_eq)
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)

  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Module.FinitePresentation T (ι →₀ T) := Module.finitePresentation_of_projective _ _
  haveI : Module.Finite T (ι →₀ T) := inferInstance
  set L : (ι →₀ T) →ₗ[T] M := Finsupp.linearCombination T m with hL
  set fF : (ι →₀ T) →ₗ[T] (ι →₀ R) := Finsupp.mapRange.linearMap (α := ι) (Algebra.linearMap T R) with hfF
  let ψ : (ι →₀ R) ≃ₗ[R] Mp := (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).equiv B (Equiv.refl ι)
  have hψ : ∀ i, ψ (Finsupp.single i 1) = B i := fun i => by
    have h := Module.Basis.equiv_apply (b := (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R))) (b' := B)
      (i := i) (e := Equiv.refl ι)
    simp only [Finsupp.coe_basisSingleOne, Equiv.refl_apply] at h
    exact h
  have hmap : IsLocalizedModule.map p.primeCompl fF fM L = ψ.toLinearMap.restrictScalars T := by
    apply IsLocalizedModule.ext p.primeCompl fF (IsLocalizedModule.map_units fM)
    rw [IsLocalizedModule.map_comp]
    apply Finsupp.lhom_ext
    intro i c
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, hL,
      Finsupp.linearCombination_single, map_smul, hfF, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      Algebra.linearMap_apply, ← Finsupp.smul_single_one, LinearEquiv.map_smul, hψ, hB, algebraMap_smul]
  have hbij : Function.Bijective (IsLocalizedModule.map p.primeCompl fF fM L) := by
    rw [hmap]; exact ψ.bijective
  obtain ⟨t, ht, hLt⟩ := Module.FinitePresentation.exists_notMem_bijective (M := ι →₀ T) (N := M) L p fF fM hbij

  let et := LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers t) L) hLt
  let bt₀ : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) (ι →₀ T)) :=
    Module.Basis.ofIsLocalizedModule (Localization.Away t) (Submonoid.powers t)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) (ι →₀ T)) Finsupp.basisSingleOne
  refine ⟨t, ht, bt₀.map et, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.ofIsLocalizedModule_apply, Finsupp.coe_basisSingleOne, LinearEquiv.ofBijective_apply,
    LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, hL,
    Finsupp.linearCombination_single, one_smul]

end S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor
end P2MW
export P2MW.S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor (solution)
