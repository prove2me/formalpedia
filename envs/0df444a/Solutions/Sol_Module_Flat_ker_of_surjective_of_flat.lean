-- Prove2me | solution 1 for Module.Flat.ker_of_surjective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/36d276e1-f3cc-5336-9c08-105897bc2dfa

import Mathlib
import Theorems.Thm_Module_Flat_lTensor_injective_of_exact_of_surjective_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_ker_of_surjective_of_flat

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] {M P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g) := by
  classical

  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ ι hι

  have hpure : ∀ (A : Type u) [AddCommGroup A] [Module R A],
      Function.Injective ((LinearMap.ker g).subtype.lTensor A) := fun A _ _ =>
    Module.Flat.lTensor_injective_of_exact_of_surjective_of_flat (LinearMap.ker g).subtype g
      (Submodule.subtype_injective _) (LinearMap.exact_subtype_ker_map g) hg A
  have h2 : Function.Injective ((ι.rTensor M) ∘ₗ ((LinearMap.ker g).subtype.lTensor N)) :=
    (Module.Flat.rTensor_preserves_injective_linearMap ι hι).comp (hpure N)
  have hsq : (ι.rTensor M) ∘ₗ ((LinearMap.ker g).subtype.lTensor N) =
      ((LinearMap.ker g).subtype.lTensor N') ∘ₗ (ι.rTensor (LinearMap.ker g)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [hsq] at h2
  exact Function.Injective.of_comp h2

end S_Module_Flat_ker_of_surjective_of_flat
end P2MW
export P2MW.S_Module_Flat_ker_of_surjective_of_flat (solution)
