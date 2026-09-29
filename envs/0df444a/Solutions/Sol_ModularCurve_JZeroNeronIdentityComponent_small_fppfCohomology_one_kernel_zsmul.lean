-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.small_fppfCohomology_one_kernel_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/54987fb4-a916-559c-b723-daa475f29432

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_AlgebraicGeometry_Scheme_small_fppfCohomology_one_specInt_of_small_sections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_small_fppfCohomology_one_kernel_zsmul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℤ) :
    Small.{0} (fppfCohomology specInt (kernel (n • 𝟙 𝒢)) 1) := by
  haveI : ∀ U : specInt.Fppf, Small.{0} ((kernel (n • 𝟙 𝒢)).1.obj (op U)) := by
    intro U

    have hG : Small.{0} (𝒢.1.obj (op U)) := small_of_injective (e U).injective

    have hmono : Mono ((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 𝒢))) := inferInstance
    have hmono' : Mono (((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 𝒢))).app (op U)) := inferInstance
    have hinj : Function.Injective (((sheafToPresheaf _ _).map (kernel.ι (n • 𝟙 𝒢))).app (op U)) :=
      (AddCommGrpCat.mono_iff_injective _).mp hmono'
    exact @small_of_injective _ _ hG _ hinj
  exact AlgebraicGeometry.Scheme.small_fppfCohomology_one_specInt_of_small_sections _

end S_ModularCurve_JZeroNeronIdentityComponent_small_fppfCohomology_one_kernel_zsmul
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_small_fppfCohomology_one_kernel_zsmul (solution)
