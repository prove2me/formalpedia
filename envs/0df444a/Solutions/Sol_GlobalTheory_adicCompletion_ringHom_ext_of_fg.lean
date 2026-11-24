-- Prove2me | solution 1 for GlobalTheory.adicCompletion_ringHom_ext_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:20:19.234576+00:00
-- url     : https://prove2.me/submissions/a30d25be-6303-4b32-97ff-31b8291b7a2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GlobalTheory
theorem _root_.solution (I : Ideal A) (hI : I.FG) (f : A →+* B)
    [IsHausdorff (I.map f) B] {g₁ g₂ : AdicCompletion I A →+* B}
    (h₁ : g₁.comp (algebraMap A _) = f) (h₂ : g₂.comp (algebraMap A _) = f) : g₁ = g₂ := by
  ext x
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I.map f)
  intro n
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.1 n)
  have hx : x - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hI, AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  have key : ∀ g : AdicCompletion I A →+* B, g.comp (algebraMap A _) = f →
      g x - f a ∈ (I.map f) ^ n := by
    intro g hg
    have := Ideal.mem_map_of_mem g hx
    rw [Ideal.map_map, hg, Ideal.map_pow, map_sub] at this
    rwa [← hg, RingHom.comp_apply, hg]
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  simpa using Ideal.sub_mem _ (key g₁ h₁) (key g₂ h₂)
end GlobalTheory
