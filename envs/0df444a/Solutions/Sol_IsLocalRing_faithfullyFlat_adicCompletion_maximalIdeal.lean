-- Prove2me | solution 1 for IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e5dd2559-8649-514c-ad33-3c71b4a48885

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
set_option autoImplicit false

open IsLocalRing

theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  haveI : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI htop => ?_⟩
  have hle : (I • ⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤ (maximalIdeal R) ^ 1 • ⊤ := by
    rw [pow_one]; exact Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal hI)
  rw [htop, top_le_iff, AdicCompletion.pow_smul_top_eq_ker_eval (IsNoetherian.noetherian _)] at hle
  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  have hne : ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R) ≠ ⊤ := by
    rw [pow_one, smul_eq_mul, Ideal.mul_top]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R)) :=
    Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨q, hq⟩ := exists_ne (0 : R ⧸ ((maximalIdeal R) ^ 1 • ⊤ : Submodule R R))
  obtain ⟨x, rfl⟩ := hsurj q
  have hx : x ∈ LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := hle ▸ Submodule.mem_top
  exact hq (LinearMap.mem_ker.mp hx)

end S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
end P2MW
export P2MW.S_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal (solution)
