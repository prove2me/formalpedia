-- Prove2me | solution 1 for IsAdicComplete.of_module_finite_free_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8a8868f6-4c04-588e-95fd-29787b94ddb2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_of_module_finite_free_map

set_option autoImplicit false

universe u v

namespace IsAdicComplete
p2m_export "IsAdicComplete" "map_algebraMap_iff"
namespace FiniteFree
p2m_open "IsAdicComplete"

open AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)

private theorem of_linearEquiv {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (e : M ≃ₗ[A] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← of_bijective_iff]
  have h : (of I N : N → AdicCompletion I N) = congr I e ∘ of I M ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, congr_apply, map_of, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
  rw [h]
  exact (congr I e).bijective.comp ((of_bijective I M).comp e.symm.bijective)

private theorem pi_of_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, IsAdicComplete I (M i)] :
    IsAdicComplete I (∀ i, M i) := by
  rw [← of_bijective_iff]
  have h : (piEquivOfFintype I M : _ → _) ∘ of I (∀ i, M i) = Pi.map fun i => of I (M i) := by
    funext x j
    simp [AdicCompletion.pi, map_of]
  have hb : Function.Bijective ((piEquivOfFintype I M : _ → _) ∘ of I (∀ i, M i)) := by
    rw [h]
    exact Function.Bijective.piMap fun i => of_bijective I (M i)
  exact (Function.Bijective.of_comp_iff' (piEquivOfFintype I M).bijective _).1 hb

end IsAdicComplete.FiniteFree

open IsAdicComplete.FiniteFree in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (I : Ideal 𝓞) [IsAdicComplete I 𝓞]
    (R : Type v) [CommRing R] [Algebra 𝓞 R] [Module.Finite 𝓞 R] [Module.Free 𝓞 R] :
    IsAdicComplete (I.map (algebraMap 𝓞 R)) R := by
  classical
  rw [IsAdicComplete.map_algebraMap_iff]
  haveI : IsAdicComplete I (Module.Free.ChooseBasisIndex 𝓞 R → 𝓞) := pi_of_fintype _ _
  exact of_linearEquiv I (Module.Free.chooseBasis 𝓞 R).equivFun.symm

end S_IsAdicComplete_of_module_finite_free_map
end P2MW
export P2MW.S_IsAdicComplete_of_module_finite_free_map (solution)
