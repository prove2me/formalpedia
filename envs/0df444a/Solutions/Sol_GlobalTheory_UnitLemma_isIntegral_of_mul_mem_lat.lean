-- Prove2me | solution 1 for GlobalTheory.UnitLemma.isIntegral_of_mul_mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:15.401508+00:00
-- url     : https://prove2.me/submissions/eb9a0e1c-380a-44aa-a15f-65cfc3ed9ec2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticeLeIntegralUnitsSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]
namespace GlobalTheory.UnitLemma
theorem _root_.solution {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End O L := (LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      change t * (((f ^ n) y : L) : A) = _
      rw [ih, pow_succ', mul_assoc]
  have hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y := by
    intro y
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]
  have hkill : ∀ y ∈ L, aeval t p * y = 0 := by
    intro y hy
    have := hev ⟨y, hy⟩
    rw [hpf] at this
    simpa using this.symm
  have hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hkill y hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have h1 : aeval t p = 0 := by
    have := hall 1 (by rw [hL.2]; trivial)
    simpa using this
  exact ⟨p, hp, by rw [← aeval_def]; exact h1⟩
end GlobalTheory.UnitLemma
