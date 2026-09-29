-- Prove2me | solution 1 for Module.Flat.of_module_fractionRing_of_isReduced_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9047ee9d-3627-5334-ad23-177951317eb6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_of_module_fractionRing_of_isReduced_baseChange
set_option autoImplicit false
universe u v w x
open scoped TensorProduct

theorem solution
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (B₁ : Type w) [CommRing B₁] [Algebra R B₁] [Module.Finite R B₁] [Module.Flat R B₁]
    [IsReduced (TensorProduct R K B₁)]
    (M : Type x) [AddCommGroup M] [Module R M] [Module K M] [Module B₁ M]
    [IsScalarTower R K M] [IsScalarTower R B₁ M] [SMulCommClass K B₁ M] :
    Module.Flat B₁ M := by
  letI : Module (K ⊗[R] B₁) M := TensorProduct.Algebra.module
  letI : Algebra B₁ (K ⊗[R] B₁) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower B₁ (K ⊗[R] B₁) M :=
    IsScalarTower.of_algebraMap_smul fun b m => by
      change ((1 : K) ⊗ₜ[R] b) • m = b • m
      rw [TensorProduct.Algebra.smul_def, one_smul]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B₁ (nonZeroDivisors R)) (K ⊗[R] B₁) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  haveI : Module.Flat B₁ (K ⊗[R] B₁) :=
    IsLocalization.flat _ (Algebra.algebraMapSubmonoid B₁ (nonZeroDivisors R))
  haveI : IsArtinianRing (K ⊗[R] B₁) := IsArtinianRing.of_finite K _
  haveI : IsSemisimpleRing (K ⊗[R] B₁) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  haveI : Module.Projective (K ⊗[R] B₁) M := Module.projective_of_isSemisimpleRing _ _
  exact Module.Flat.trans B₁ (K ⊗[R] B₁) M

end S_Module_Flat_of_module_fractionRing_of_isReduced_baseChange
end P2MW
export P2MW.S_Module_Flat_of_module_fractionRing_of_isReduced_baseChange (solution)
