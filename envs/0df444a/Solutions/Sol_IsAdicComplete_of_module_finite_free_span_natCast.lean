-- Prove2me | solution 1 for IsAdicComplete.of_module_finite_free_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/cb0e9b28-6808-579b-9fc8-2d7b3ff47c62

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAdicComplete_of_module_finite_free_span_natCast

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
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R : Type v) [CommRing R] [Algebra 𝓞 R] [Module.Finite 𝓞 R] [Module.Free 𝓞 R] :
    IsAdicComplete (Ideal.span {(p : R)}) R := by
  classical
  have hmap : (Ideal.span {(p : 𝓞)}).map (algebraMap 𝓞 R) = Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap, IsAdicComplete.map_algebraMap_iff]
  haveI : IsAdicComplete (Ideal.span {(p : 𝓞)}) (Module.Free.ChooseBasisIndex 𝓞 R → 𝓞) :=
    pi_of_fintype _ _
  exact of_linearEquiv (Ideal.span {(p : 𝓞)}) (Module.Free.chooseBasis 𝓞 R).equivFun.symm

end S_IsAdicComplete_of_module_finite_free_span_natCast
end P2MW
export P2MW.S_IsAdicComplete_of_module_finite_free_span_natCast (solution)
