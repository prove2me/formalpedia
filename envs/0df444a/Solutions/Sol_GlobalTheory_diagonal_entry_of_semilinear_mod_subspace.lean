-- Prove2me | solution 1 for GlobalTheory.diagonal_entry_of_semilinear_mod_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:08.768536+00:00
-- url     : https://prove2.me/submissions/bc4d5f0e-6695-4c51-8106-eb1af95eaa6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagonalEntryOfSemilinearModSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  intro F _ n θ A W' W f' e' f e w' w k' k m d α hξ hT hf' hf he hTf hTe
  have hx : ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 := by
    intro h
    apply PowerSeries.X_ne_zero (R := F)
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    simpa using h
  set x : LaurentSeries F := ((PowerSeries.X : PowerSeries F) : LaurentSeries F) with hxdef
  set ξ : LaurentSeries F := ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) with hξdef
  obtain ⟨N, j, hj⟩ : ∃ N j : ℕ, (j : ℤ) = (N : ℤ) + k' := ⟨k'.natAbs, (k'.natAbs + k').toNat, by omega⟩
  set a : PowerSeries F := (w' : PowerSeries F) * PowerSeries.X ^ j with hadef
  have ha : ((a : PowerSeries F) : LaurentSeries F) = (w' : LaurentSeries F) * x ^ N * x ^ k' := by
    rw [hadef, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hx, zpow_natCast, mul_assoc]
  have hθa : ((θ a : PowerSeries F) : LaurentSeries F) = ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ξ ^ N * ξ ^ k' := by
    rw [hadef, map_mul, map_pow, PowerSeries.coe_mul, PowerSeries.coe_pow, ← zpow_natCast, hj, zpow_add₀ hξ, zpow_natCast, mul_assoc]
  let y : Fin n → PowerSeries F := fun c => PowerSeries.X ^ N * f' c - a * e' c
  have hy : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) ∈ W' := by
    have : (fun c => ((y c : PowerSeries F) : LaurentSeries F)) = (x ^ N) • ((fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * x ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F))) := by
      funext c
      simp only [y, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, ha, ← hxdef]
      ring
    rw [this]; exact W'.smul_mem _ hf'
  have hvec : A.mulVec (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • A.mulVec (fun c => θ (f' c)) - θ a • A.mulVec (fun c => θ (e' c)) := by
    have : (fun c => θ (y c)) = (θ PowerSeries.X) ^ N • (fun c => θ (f' c)) - θ a • (fun c => θ (e' c)) := by
      ext c; simp [y]
    rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hTy := hT y hy
  set P : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (f' c)) i : PowerSeries F) : LaurentSeries F) with hP
  set Q : Fin n → LaurentSeries F := fun i => ((A.mulVec (fun c => θ (e' c)) i : PowerSeries F) : LaurentSeries F) with hQ
  set E : Fin n → LaurentSeries F := fun i => ((e i : PowerSeries F) : LaurentSeries F) with hE
  set Fv : Fin n → LaurentSeries F := fun i => ((f i : PowerSeries F) : LaurentSeries F) with hFv
  have h4 : ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q ∈ W := by
    have : (fun i => ((A.mulVec (fun c => θ (y c)) i : PowerSeries F) : LaurentSeries F)) = ξ ^ N • P - ((θ a : PowerSeries F) : LaurentSeries F) • Q := by
      funext i
      simp only [hvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow, hP, hQ, hξdef]
    rw [← this]; exact hTy
  set c : LaurentSeries F := ((θ a : PowerSeries F) : LaurentSeries F) * α - x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * x ^ k with hc
  have hcE : c • E ∈ W := by
    have h := W.sub_mem (W.sub_mem (W.add_mem (W.smul_mem (x ^ m * ξ ^ N) hTf) (W.smul_mem (x ^ m * ξ ^ N * ((d : PowerSeries F) : LaurentSeries F)) hf)) (W.smul_mem (((θ a : PowerSeries F) : LaurentSeries F)) hTe)) (W.smul_mem (x ^ m) h4)
    convert h using 1
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hc, hP, hQ, hE, hFv]
    ring
  have hc0 : c = 0 := by
    by_contra hne
    apply he
    have := W.smul_mem c⁻¹ hcE
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hξN : ξ ^ N ≠ 0 := pow_ne_zero _ hξ
  rw [hc, hθa, sub_eq_zero] at hc0
  apply mul_right_cancel₀ hξN
  linear_combination hc0
end GlobalTheory
