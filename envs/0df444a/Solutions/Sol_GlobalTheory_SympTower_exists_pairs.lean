-- Prove2me | solution 1 for GlobalTheory.SympTower.exists_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:08.3618+00:00
-- url     : https://prove2.me/submissions/0be480f3-b037-4753-8b29-25586f42e6fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic
import Theorems.Thm_GlobalTheory_SympTower_rank_le_of_smul_sub_eq_zero
import Theorems.Thm_GlobalTheory_SympTower_exists_eq_one
import Theorems.Thm_GlobalTheory_SympTower_exists_faithful

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower
namespace GlobalTheory.SympTower
theorem _root_.solution {n : ℕ} [NeZero n] {g : ℕ}
    (ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n)
    (halt : ∀ x, ω x x = 0) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) (k : ℕ) (hk : k ≤ g) :
    ∃ v w : Fin k → (Fin (2 * g) → ZMod n), (∀ i j, ω (v i) (v j) = 0) ∧
      (∀ i j, ω (w i) (w j) = 0) ∧ ∀ i j, ω (v i) (w j) = if i = j then 1 else 0 := by
  classical
  have hsk : ∀ x y, ω x y = - ω y x := by
    intro x y
    have := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt] at this
    linear_combination this
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨v, w, hv, hw, hvw⟩ := ih (by omega)
    let φ : (Fin k ⊕ Fin k → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) :=
      Fintype.linearCombination (ZMod n) (Sum.elim v w)
    let ψ : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin k ⊕ Fin k → ZMod n) :=
      LinearMap.pi (Sum.elim (fun i => ω.flip (w i)) (fun i => ω (v i)))
    have hφψ : ∀ x, φ (ψ x) = ∑ i, ω x (w i) • v i + ∑ i, ω (v i) x • w i := by
      intro x
      simp [φ, ψ, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    let K : Submodule (ZMod n) (Fin (2 * g) → ZMod n) :=
      { carrier := {x | ∀ j, ω (v j) x = 0 ∧ ω x (w j) = 0}
        add_mem' := fun ha hb j => by simp [(ha j).1, (ha j).2, (hb j).1, (hb j).2]
        zero_mem' := fun j => by simp
        smul_mem' := fun c x hx j => by simp [(hx j).1, (hx j).2] }
    have hp : ∀ x, x - φ (ψ x) ∈ K := by
      intro x j
      rw [hφψ]
      constructor
      · simp [map_sum, hv, hvw]
      · simp [map_sum, LinearMap.sum_apply, hw, hvw]
    have hKp : ∀ x ∈ K, ∀ y, ω x (y - φ (ψ y)) = ω x y := by
      intro x hx y
      have h1 : ∀ j, ω x (v j) = 0 := fun j => by rw [hsk, (hx j).1, neg_zero]
      rw [hφψ]
      simp [map_sum, h1, fun j => (hx j).2]
    obtain ⟨x, hx⟩ := exists_faithful (n := n) (V := K) (by
      intro c hc
      by_contra hc0
      have := rank_le_of_smul_sub_eq_zero φ ψ c hc0
        (fun x => congrArg Subtype.val (hc ⟨_, hp x⟩))
      simp at this
      omega)
    obtain ⟨y, hy⟩ := exists_eq_one ((ω x.1).comp K.subtype) (by
      intro c hc
      apply hx
      apply Subtype.ext
      apply hnd
      intro y
      have := hc ⟨_, hp y⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, hKp x.1 x.2] at this
      simpa using this)
    have hxv : ∀ j, ω x.1 (v j) = 0 := fun j => by rw [hsk, (x.2 j).1, neg_zero]
    have hwy : ∀ j, ω (w j) y.1 = 0 := fun j => by rw [hsk, (y.2 j).2, neg_zero]
    refine ⟨Fin.cons x.1 v, Fin.cons y.1 w, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [halt, hxv, hv, (x.2 _).1]
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [halt, hwy, hw, (y.2 _).2]
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hy
      · simp [(x.2 _).2, (Fin.succ_ne_zero j).symm]
      · simp [(y.2 _).1]
      · simp [hvw]
end GlobalTheory.SympTower
