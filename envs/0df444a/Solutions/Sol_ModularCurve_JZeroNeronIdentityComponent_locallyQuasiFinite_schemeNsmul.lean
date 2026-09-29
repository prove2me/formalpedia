-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.locallyQuasiFinite_schemeNsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9e16269e-37aa-5e20-8cc4-6b7ac6eef159

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_flat_of_locallyQuasiFinite_genericFiber
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_of_locallyQuasiFinite_kernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_locallyQuasiFinite_schemeNsmul
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve NeronModelInfra GoodReductionJacobian

theorem solution
    {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p) (n : ℕ) (hn : 0 < n) :
    LocallyQuasiFinite (N.L.schemeNsmul n) := by
  haveI := N.locallyOfFiniteType
  haveI := N.quasiCompact
  haveI := N.separated
  haveI : Flat (N.L.schemeNsmul n) := N.nsmul_flat n hn

  have nsmul_coe : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x : SchemeHomOver t N.g),
      (N.L.nsmul t n x).1 = x.1 ≫ N.L.schemeNsmul n := by
    intro T t x
    have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := N.g)) = x :=
      Subtype.ext (Category.comp_id _)
    have := N.L.nsmul_natural N.g t x.1 x.2 n RelativeGroupLaw.idPoint
    rw [hx] at this
    rw [← this]
    rfl
  have nsmul_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (m : ℕ) (x y : SchemeHomOver t N.g),
      N.L.nsmul t m (N.L.mul t x y) = N.L.mul t (N.L.nsmul t m x) (N.L.nsmul t m y) := by
    intro T t m x y
    induction m with
    | zero => simp only [RelativeGroupLaw.nsmul_zero]; exact (N.L.one_mul t _).symm
    | succ m ih =>
        simp only [RelativeGroupLaw.nsmul_succ, ih]
        letI := N.L.pointGroup t
        show (N.L.nsmul t m x * N.L.nsmul t m y) * (x * y) = (N.L.nsmul t m x * x) * (N.L.nsmul t m y * y)
        have hcomm : ∀ a b : SchemeHomOver t N.g, a * b = b * a := fun a b => N.comm t a b
        rw [_root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (N.L.nsmul t m y), hcomm (N.L.nsmul t m y) x,
          _root_.mul_assoc]
  have hu : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t N.g),
      NeronModelInfra.schemeHomOverComp (N.L.mul t x y) ⟨N.L.schemeNsmul n, N.L.schemeNsmul_over n⟩ =
        N.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨N.L.schemeNsmul n, N.L.schemeNsmul_over n⟩)
          (NeronModelInfra.schemeHomOverComp y ⟨N.L.schemeNsmul n, N.L.schemeNsmul_over n⟩) := by
    intro T t x y
    have key : ∀ z : SchemeHomOver t N.g,
        NeronModelInfra.schemeHomOverComp z ⟨N.L.schemeNsmul n, N.L.schemeNsmul_over n⟩ = N.L.nsmul t n z :=
      fun z => Subtype.ext (nsmul_coe t z).symm
    rw [key, key, key, nsmul_mul]

  have he : (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = 𝟙 _ := (N.L.one (𝟙 _)).2
  haveI : IsClosedImmersion (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
    have : IsClosedImmersion ((N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) := by
      rw [he]; infer_instance
    exact .of_comp _ N.g
  have hkf : pullback.fst (N.L.schemeNsmul n) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g =
      N.L.schemeKerStr n := by
    calc _ = pullback.fst (N.L.schemeNsmul n) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫
          N.L.schemeNsmul n ≫ N.g := by rw [N.L.schemeNsmul_over]
      _ = (pullback.snd (N.L.schemeNsmul n) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫
          (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) ≫ N.g := by rw [← Category.assoc, pullback.condition]
      _ = N.L.schemeKerStr n := by rw [Category.assoc, he, Category.comp_id]
  haveI : LocallyOfFiniteType (N.L.schemeKerStr n) := by rw [← hkf]; infer_instance
  haveI : QuasiCompact (N.L.schemeKerStr n) := by rw [← hkf]; infer_instance
  haveI : Flat (N.L.schemeKerStr n) := inferInstance

  haveI : LocallyQuasiFinite (pullback.snd (N.L.schemeKerStr n)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) :=
    N.L.locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun t x y => N.comm t x y) n (by exact_mod_cast (isUnit_iff_ne_zero.mpr (by exact_mod_cast hn.ne')))

  haveI : LocallyQuasiFinite (N.L.schemeKerStr n) :=
    LocallyQuasiFinite.of_flat_of_locallyQuasiFinite_genericFiber (R := ℤ) (K := ℚ) (N.L.schemeKerStr n)

  exact N.L.locallyQuasiFinite_of_locallyQuasiFinite_kernel N.L ⟨N.L.schemeNsmul n, N.L.schemeNsmul_over n⟩ hu

end S_ModularCurve_JZeroNeronIdentityComponent_locallyQuasiFinite_schemeNsmul
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_locallyQuasiFinite_schemeNsmul (solution)
