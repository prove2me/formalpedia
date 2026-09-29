-- Prove2me | solution 1 for Ideal.exists_ringHom_integralClosure_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e251d03d-9883-5d26-ab22-6a29492cd670

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_ringHom_integralClosure_ker_eq

open Ideal

theorem solution {T : Type*} [CommRing T] [Module.Finite ℤ T] (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime) (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) : ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓 := by
  classical
  haveI := h𝔓

  set D := T ⧸ 𝔓 with hD
  haveI : IsDomain D := Ideal.Quotient.isDomain 𝔓
  have hinjD : Function.Injective (algebraMap ℤ D) := by
    intro a b hab
    have h : ((a - b : ℤ) : T) ∈ 𝔓 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, Int.cast_sub, sub_eq_zero]
      simpa [Algebra.algebraMap_eq_smul_one] using hab
    exact sub_eq_zero.mp (hint _ h)
  haveI : CharZero D := by
    refine ⟨fun a b hab => ?_⟩
    have := hinjD (show algebraMap ℤ D (a : ℤ) = algebraMap ℤ D (b : ℤ) by simpa using hab)
    exact_mod_cast this
  haveI : @Module.IsTorsionFree ℤ D _ _ Algebra.toModule := by
    refine ⟨fun n hn => ?_⟩
    intro a b hab
    have hn0 : algebraMap ℤ D n ≠ 0 := (map_ne_zero_iff _ hinjD).mpr hn.ne_zero
    have h' : algebraMap ℤ D n * a = algebraMap ℤ D n * b := by
      simpa only [Algebra.smul_def] using hab
    exact mul_left_cancel₀ hn0 h'
  haveI : Module.Finite ℤ D :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  haveI : Algebra.IsIntegral ℤ D := inferInstance
  haveI : Algebra.IsAlgebraic ℤ D := ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩

  let φ : D →ₐ[ℤ] ℂ := IsAlgClosed.lift
  have hφker : RingHom.ker φ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] at hn
    simpa using hn
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have : d ∈ RingHom.ker φ.toRingHom := hd
    rw [hφker, Ideal.mem_bot] at this
    exact this

  have hmem : ∀ t : T, (φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)) t ∈ integralClosure ℤ ℂ := by
    intro t
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) (Ideal.Quotient.mk 𝔓 t)).map φ
  refine ⟨(φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)).codRestrict (integralClosure ℤ ℂ) hmem, ?_⟩
  ext t
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply hφinj
    rw [map_zero]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    show φ (Ideal.Quotient.mk 𝔓 t) = 0
    rw [h, map_zero]

end S_Ideal_exists_ringHom_integralClosure_ker_eq
end P2MW
export P2MW.S_Ideal_exists_ringHom_integralClosure_ker_eq (solution)
