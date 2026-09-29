-- Prove2me | solution 1 for IsLocalRing.exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1405fc5d-2373-5329-a9de-06dbba3f41c3

import Mathlib
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite

set_option autoImplicit false

open IsLocalRing

namespace DescentAux

theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (L : Type) [Field L] [Algebra 𝒪 L]
    [Algebra (FractionRing 𝒪) L] [IsScalarTower 𝒪 (FractionRing 𝒪) L]
    (χ : A →ₐ[𝒪] L) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪'))
      (j : 𝒪' →ₐ[𝒪] L) (ψ : A →ₐ[𝒪] 𝒪'),
      Function.Injective j ∧ ∀ a : A, j (ψ a) = χ a := by
  classical
  let K := FractionRing 𝒪
  haveI : Algebra.IsIntegral 𝒪 A := Algebra.IsIntegral.of_finite 𝒪 A

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝒪) (M := A)
  let L' : IntermediateField K L := IntermediateField.adjoin K (χ '' (s : Set A))
  have hintK : ∀ x ∈ χ '' (s : Set A), IsIntegral K x := by
    rintro _ ⟨a, -, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := 𝒪) a).map χ).tower_top
  haveI : Finite ↥(χ '' (s : Set A)) := ((s.finite_toSet).image χ).to_subtype
  haveI : FiniteDimensional K L' := IntermediateField.finiteDimensional_adjoin hintK

  have hχL' : ∀ a : A, χ a ∈ L' := by
    intro a
    have ha : a ∈ Submodule.span 𝒪 (s : Set A) := by rw [hs]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L'
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
        rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪 K L]
        exact mul_mem (L'.algebraMap_mem _) hx

  let ψ₀ : A →ₐ[𝒪] L' :=
    { toFun := fun a => ⟨χ a, hχL' a⟩
      map_one' := Subtype.ext (map_one χ)
      map_mul' := fun a b => Subtype.ext (map_mul χ a b)
      map_zero' := Subtype.ext (map_zero χ)
      map_add' := fun a b => Subtype.ext (map_add χ a b)
      commutes' := fun r => Subtype.ext (by
        simp only [AlgHom.commutes]
        rfl) }

  haveI : Algebra.IsSeparable K L' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨hfin, hdvr, hcomplete⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪 K L'
  let 𝒪' : Type := ↥(integralClosure 𝒪 (L' : Type))
  haveI : Module.Finite 𝒪 𝒪' := hfin
  haveI : IsDiscreteValuationRing 𝒪' := hdvr
  haveI : IsAdicComplete (maximalIdeal 𝒪') 𝒪' := hcomplete

  let ψ : A →ₐ[𝒪] 𝒪' := ψ₀.codRestrict (integralClosure 𝒪 (L' : Type))
    (fun a => (mem_integralClosure_iff 𝒪 (L' : Type)).mpr
      ((Algebra.IsIntegral.isIntegral (R := 𝒪) a).map ψ₀))
  let j : 𝒪' →ₐ[𝒪] L := (L'.val.restrictScalars 𝒪).comp (integralClosure 𝒪 (L' : Type)).val
  have hj : Function.Injective j := fun x y h => Subtype.ext (Subtype.ext h)
  have hjψ : ∀ a, j (ψ a) = χ a := fun _ => rfl

  have hinj : Function.Injective (algebraMap 𝒪 𝒪') := fun a b h => by
    have h1 := congrArg j h
    rw [AlgHom.commutes, AlgHom.commutes] at h1
    exact (IsFractionRing.injective 𝒪 K) ((algebraMap K L).injective (by
      simpa only [IsScalarTower.algebraMap_apply 𝒪 K L] using h1))
  haveI : FaithfulSMul 𝒪 𝒪' := (faithfulSMul_iff_algebraMap_injective 𝒪 𝒪').mpr hinj
  haveI : CharZero 𝒪' := charZero_of_injective_algebraMap hinj
  haveI : IsLocalHom (algebraMap 𝒪 𝒪') := Algebra.IsIntegral.isLocalHom 𝒪 𝒪'
  haveI : Finite (ResidueField 𝒪') := ResidueField.finite_of_finite (R := 𝒪) inferInstance
  exact ⟨𝒪', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, j, ψ, hj, hjψ⟩

end DescentAux

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (L : Type) [Field L] [Algebra 𝒪 L] (hL : Function.Injective (algebraMap 𝒪 L))
    (χ : A →ₐ[𝒪] L) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪'))
      (j : 𝒪' →ₐ[𝒪] L) (ψ : A →ₐ[𝒪] 𝒪'),
      Function.Injective j ∧ ∀ a : A, j (ψ a) = χ a := by
  classical
  haveI : FaithfulSMul 𝒪 L := (faithfulSMul_iff_algebraMap_injective 𝒪 L).mpr hL
  letI : Algebra (FractionRing 𝒪) L := FractionRing.liftAlgebra 𝒪 L
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) L := FractionRing.isScalarTower_liftAlgebra 𝒪 L
  exact DescentAux.main A L χ

end S_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite
end P2MW
export P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite (solution)
