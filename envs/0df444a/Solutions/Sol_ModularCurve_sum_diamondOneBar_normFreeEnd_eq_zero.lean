-- Prove2me | solution 1 for ModularCurve.sum_diamondOneBar_normFreeEnd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7a996fda-be8b-59cd-b063-a72b0235177a

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

import Theorems.Thm_ModularCurve_diamondOneBar_mul_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "HeckeDiamondInputsAll x1FunctionField JOne IsDiamondAut diamondAut diamondAutBar diamondOneBar diamondOneBar_apply normFreeRepsAt mem_normFreeRepsAt normFreeEnd normFreeEnd_apply diamondOneBar_mul_of_coprime"
namespace NormKillSol
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero.ModularCurve Finset"

variable (M : ℕ)

theorem isDiamondAut_eq_of_modEq {d e : ℕ} (h : d ≡ e [MOD M]) :
    IsDiamondAut M d = IsDiamondAut M e := by
  funext σ
  have hc : Nat.Coprime d M ↔ Nat.Coprime e M := by
    unfold Nat.Coprime; rw [h.gcd_eq]
  have hz : (d : ZMod M) = (e : ZMod M) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simp only [IsDiamondAut, hz, hc]

theorem diamondAut_eq_of_modEq {d e : ℕ} (h : d ≡ e [MOD M]) : diamondAut M d = diamondAut M e := by
  have key : ∀ (P Q : (x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) → Prop), P = Q →
      (haveI := Classical.dec (∃ σ, P σ); if hP : ∃ σ, P σ then hP.choose else AlgEquiv.refl) =
      (haveI := Classical.dec (∃ σ, Q σ); if hQ : ∃ σ, Q σ then hQ.choose else AlgEquiv.refl) := by
    rintro P Q rfl; rfl
  exact key _ _ (isDiamondAut_eq_of_modEq M h)

theorem diamondOneBar_eq_of_modEq {d e : ℕ} (h : d ≡ e [MOD M]) : diamondOneBar M d = diamondOneBar M e := by
  have : diamondAutBar M d = diamondAutBar M e := by
    unfold diamondAutBar; rw [diamondAut_eq_of_modEq M h]
  apply LinearMap.ext; intro x
  rw [diamondOneBar_apply, diamondOneBar_apply, this]

variable (p : ℕ)

theorem mul_mod_mem (hpM : p ∣ M) (hM : 0 < M) {d d' : ℕ} (hd : d ∈ normFreeRepsAt M p) (hd' : d' ∈ normFreeRepsAt M p) :
    (d * d') % M ∈ normFreeRepsAt M p := by
  rw [mem_normFreeRepsAt] at hd hd' ⊢
  refine ⟨Nat.mod_lt _ hM, ?_, ?_⟩
  · have h1 : Nat.Coprime (d * d') M := Nat.Coprime.mul_left hd.2.1 hd'.2.1
    unfold Nat.Coprime at h1 ⊢
    rw [← h1]; exact (Nat.mod_modEq _ _).gcd_eq
  · have hdvd : M / p ∣ M := Nat.div_dvd_of_dvd hpM
    have h2 : d * d' ≡ 1 [MOD M / p] := by simpa using Nat.ModEq.mul hd.2.2 hd'.2.2
    exact ((Nat.mod_modEq (d * d') M).of_dvd hdvd).trans h2

theorem mul_mod_injOn (hM : 0 < M) {d : ℕ} (hd : d ∈ normFreeRepsAt M p) :
    Set.InjOn (fun d' => (d * d') % M) (normFreeRepsAt M p : Set ℕ) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, mem_normFreeRepsAt] at ha hb
  rw [mem_normFreeRepsAt] at hd
  have h1 : d * a ≡ d * b [MOD M] := hab
  have h2 : a ≡ b [MOD M] := Nat.ModEq.cancel_left_of_coprime (by
    have := hd.2.1; unfold Nat.Coprime at this; rwa [Nat.gcd_comm]) h1
  exact Nat.ModEq.eq_of_lt_of_lt h2 ha.1 hb.1

theorem sum_diamondOneBar_mul (hpM : p ∣ M) (hM : 0 < M) {d : ℕ} (hd : d ∈ normFreeRepsAt M p) (y : JOne M) :
    ∑ d' ∈ normFreeRepsAt M p, diamondOneBar M (d * d') y = ∑ e ∈ normFreeRepsAt M p, diamondOneBar M e y := by
  have hmod : ∀ d' ∈ normFreeRepsAt M p, diamondOneBar M (d * d') y = diamondOneBar M ((d * d') % M) y := fun d' _ => by
    rw [diamondOneBar_eq_of_modEq M (Nat.mod_modEq (d * d') M).symm]
  rw [Finset.sum_congr rfl hmod]
  refine Finset.sum_nbij (fun d' => (d * d') % M) (fun d' hd' => mul_mod_mem M p hpM hM hd hd') (mul_mod_injOn M p hM hd) ?_ (fun _ _ => rfl)
  exact Finset.surjOn_of_injOn_of_card_le _ (fun d' hd' => mul_mod_mem M p hpM hM hd hd') (mul_mod_injOn M p hM hd) le_rfl

end ModularCurve.NormKillSol

open ModularCurve.NormKillSol Finset in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M)
    (hIn : ModularCurve.HeckeDiamondInputsAll M) (x : JOne M) :
    (∑ d ∈ normFreeRepsAt M p, diamondOneBar M d (normFreeEnd M (normFreeRepsAt M p) x) = 0) ∧
    (normFreeEnd M (normFreeRepsAt M p) (∑ d ∈ normFreeRepsAt M p, diamondOneBar M d x) = 0) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set S := normFreeRepsAt M p with hS
  have hcop : ∀ d ∈ S, Nat.Coprime d M := fun d hd => (mem_normFreeRepsAt.mp hd).2.1

  have hmul : ∀ d ∈ S, ∀ d' ∈ S, ∀ y : JOne M,
      diamondOneBar M d (diamondOneBar M d' y) = diamondOneBar M (d * d') y := by
    intro d hd d' hd' y
    rw [ModularCurve.diamondOneBar_mul_of_coprime M hIn.2 d d' (hcop d hd) (hcop d' hd')]
    rfl

  have hdouble : ∀ y : JOne M, ∑ d ∈ S, ∑ d' ∈ S, diamondOneBar M d (diamondOneBar M d' y) =
      S.card • ∑ e ∈ S, diamondOneBar M e y := by
    intro y
    rw [Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun d' hd' => hmul d hd d' hd' y]
    rw [Finset.sum_congr rfl fun d hd => sum_diamondOneBar_mul M p hpM hM hd y, Finset.sum_const]
  have hdouble' : ∀ y : JOne M, ∑ d' ∈ S, ∑ d ∈ S, diamondOneBar M d' (diamondOneBar M d y) =
      S.card • ∑ e ∈ S, diamondOneBar M e y := fun y => hdouble y
  constructor
  ·
    simp only [normFreeEnd_apply, map_sub, map_nsmul, map_sum]
    rw [Finset.sum_sub_distrib, hdouble x, ← Finset.smul_sum, sub_self]
  · simp only [normFreeEnd_apply, map_sub, map_nsmul, map_sum]
    rw [Finset.sum_sub_distrib, Finset.sum_comm, hdouble x, ← Finset.smul_sum, sub_self]

end S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero
end P2MW
export P2MW.S_ModularCurve_sum_diamondOneBar_normFreeEnd_eq_zero (solution)
