-- Prove2me | solution 1 for Module.Invertible.of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0ccc1494-df40-54c0-904a-88ed46a0eaf0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Invertible_of_ringEquiv

set_option autoImplicit false

universe u v

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (σ : R ≃+* R')
    (M : Type v) [AddCommGroup M] [Module R' M] [Module.Invertible R' M]
    [Module R M] (hσ : ∀ (r : R) (m : M), r • m = σ r • m) :
    Module.Invertible R M := by
  letI : Algebra R' R := σ.symm.toRingHom.toAlgebra
  haveI : IsScalarTower R' R M := ⟨fun r' r m => by
    rw [Algebra.smul_def, hσ, hσ r m, ← mul_smul]
    congr 1
    simp [RingHom.algebraMap_toAlgebra]⟩
  haveI : IsLocalization (⊥ : Submonoid R') R :=
    IsLocalization.of_le_isUnit_of_bijective
      (by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        simp)
      σ.symm.bijective
  haveI : IsLocalizedModule (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M) :=
    isLocalizedModule_id (S := (⊥ : Submonoid R')) (M := M) (R' := R)
  exact Module.Invertible.of_isLocalization (⊥ : Submonoid R') (LinearMap.id : M →ₗ[R'] M)

end S_Module_Invertible_of_ringEquiv
end P2MW
export P2MW.S_Module_Invertible_of_ringEquiv (solution)
