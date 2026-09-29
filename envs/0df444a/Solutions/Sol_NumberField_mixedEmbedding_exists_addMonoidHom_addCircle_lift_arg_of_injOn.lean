-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_addMonoidHom_addCircle_lift_arg_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d6d16080-056b-5bb3-89c2-6c9e15b6df3c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] {c : ℕ}
    (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
    (harg : ∀ y y' : mixedSpace K, IsUnit y → IsUnit y' →
      ∃ k : Fin (nrComplexPlaces K) → ℤ, arg (y * y') = arg y + arg y' + fun j => (k j : ℝ))
    (F : Subgroup Kˣ)
    (L : Kˣ → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ))
    (hL_mul : ∀ φ ∈ F, ∀ ψ ∈ F, L (φ * ψ) = L φ + L ψ)
    (hL_inj : ∀ φ ∈ F, L φ = 0 → φ = 1)
    (Λ : AddSubgroup ((Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ)))
    (hΛ : ∀ γ, γ ∈ Λ ↔ ∃ φ ∈ F, L φ = γ)
    (b : Fin c → ℝ) :
    ∃ (χ : Λ →+ (Fin (Fintype.card (InfinitePlace K) + c) → AddCircle (1 : ℝ)))
      (lift : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ) →
        (Fin (Fintype.card (InfinitePlace K) + c) → ℝ)),
      lift 0 = 0 ∧
      (∀ (γ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ)) (hγ : γ ∈ Λ)
          (j : Fin (Fintype.card (InfinitePlace K) + c)), ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∀ φ ∈ F,
        (∀ w : {w : InfinitePlace K // w.IsComplex},
          ((lift (L φ) (Fin.castAdd c (Fintype.equivFin (InfinitePlace K) w.1)) : ℝ) : AddCircle (1 : ℝ)) =
            ((arg (mixedEmbedding K (φ : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} w) : ℝ) :
              AddCircle (1 : ℝ))) ∧
        (∀ j : Fin c,
          ((lift (L φ) (Fin.natAdd (Fintype.card (InfinitePlace K)) j) : ℝ) : AddCircle (1 : ℝ)) =
            ((b j * ((L φ).2 j : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by
  classical

  have hL1 : L 1 = 0 := by
    have := hL_mul 1 F.one_mem 1 F.one_mem
    rw [one_mul] at this

    have h2 : L 1 + L 1 = L 1 + 0 := by rw [add_zero]; exact this.symm
    exact add_left_cancel h2
  have hLinj : ∀ φ ∈ F, ∀ ψ ∈ F, L φ = L ψ → φ = ψ := by
    intro φ hφ ψ hψ h
    have hinv : L ψ⁻¹ = - L ψ := by
      have := hL_mul ψ hψ ψ⁻¹ (F.inv_mem hψ)
      rw [mul_inv_cancel, hL1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    have h0 : L (φ * ψ⁻¹) = 0 := by rw [hL_mul φ hφ ψ⁻¹ (F.inv_mem hψ), hinv, h, add_neg_cancel]
    have := hL_inj (φ * ψ⁻¹) (F.mul_mem hφ (F.inv_mem hψ)) h0
    exact mul_inv_eq_one.mp this

  obtain ⟨k₁, hk₁⟩ := harg 1 1 isUnit_one isUnit_one
  have harg1 : ∀ i, arg 1 i = -(k₁ i : ℝ) := by
    intro i
    have := congrFun hk₁ i
    simp only [mul_one, Pi.add_apply] at this
    linarith
  have hιu : ∀ φ : Kˣ, IsUnit (mixedEmbedding K (φ : K)) := fun φ => (Units.isUnit φ).map (mixedEmbedding K)

  let argC : Kˣ → InfinitePlace K → ℝ := fun φ w =>
    if h : w.IsComplex then arg (mixedEmbedding K (φ : K)) (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨w, h⟩) else 0
  let v : Kˣ → (Fin (Fintype.card (InfinitePlace K) + c) → ℝ) := fun φ =>
    Fin.addCases (fun i => argC φ ((Fintype.equivFin (InfinitePlace K)).symm i)) (fun j => b j * ((L φ).2 j : ℝ))
  have v_left : ∀ φ (i : Fin (Fintype.card (InfinitePlace K))), v φ (Fin.castAdd c i) = argC φ ((Fintype.equivFin (InfinitePlace K)).symm i) := by
    intro φ i; simp [v]
  have v_right : ∀ φ (j : Fin c), v φ (Fin.natAdd (Fintype.card (InfinitePlace K)) j) = b j * ((L φ).2 j : ℝ) := by
    intro φ j; simp [v]

  have hv1 : ∀ j, ∃ m : ℤ, v 1 j = (m : ℝ) := by
    intro j
    induction j using Fin.addCases with
    | left i =>
      rw [v_left]
      simp only [argC]
      split_ifs with h
      · exact ⟨-k₁ _, by rw [Units.val_one, map_one, harg1]; push_cast; ring⟩
      · exact ⟨0, by simp⟩
    | right j =>
      rw [v_right, hL1]
      exact ⟨0, by simp⟩
  have hvmul : ∀ φ ∈ F, ∀ ψ ∈ F, ∀ j, ∃ m : ℤ, v (φ * ψ) j = v φ j + v ψ j + (m : ℝ) := by
    intro φ hφ ψ hψ j
    obtain ⟨k, hk⟩ := harg _ _ (hιu φ) (hιu ψ)
    induction j using Fin.addCases with
    | left i =>
      rw [v_left, v_left, v_left]
      simp only [argC]
      split_ifs with h
      · refine ⟨k (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨_, h⟩), ?_⟩
        have := congrFun hk (Fintype.equivFin {w : InfinitePlace K // w.IsComplex} ⟨_, h⟩)
        simp only [Pi.add_apply] at this
        rw [Units.val_mul, map_mul, this]
      · exact ⟨0, by simp⟩
    | right j =>
      rw [v_right, v_right, v_right, hL_mul φ hφ ψ hψ]
      exact ⟨0, by push_cast; simp only [Prod.snd_add, Pi.add_apply, Int.cast_add]; ring⟩

  let lift : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin c → ℤ) → (Fin (Fintype.card (InfinitePlace K) + c) → ℝ) := fun γ =>
    if h : ∃ φ ∈ F, L φ = γ then v (Classical.choose h) - v 1 else 0
  have lift_of : ∀ φ ∈ F, lift (L φ) = v φ - v 1 := by
    intro φ hφ
    have h : ∃ ψ ∈ F, L ψ = L φ := ⟨φ, hφ, rfl⟩
    simp only [lift, dif_pos h]
    have hc := Classical.choose_spec h
    rw [hLinj _ hc.1 φ hφ hc.2]
  have lift0 : lift 0 = 0 := by
    rw [← hL1, lift_of 1 F.one_mem, sub_self]
  have hcoe_int : ∀ (x : ℝ) (m : ℤ), (((x + (m : ℝ)) : ℝ) : AddCircle (1 : ℝ)) = ((x : ℝ) : AddCircle (1 : ℝ)) := by
    intro x m
    have hm0 : (((m : ℝ)) : AddCircle (1 : ℝ)) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp⟩
    rw [AddCircle.coe_add, hm0, add_zero]
  refine ⟨{ toFun := fun γ j => ((lift γ.1 j : ℝ) : AddCircle (1 : ℝ)),
            map_zero' := ?_, map_add' := ?_ }, lift, lift0, ?_, ?_⟩
  · funext j
    show ((lift (0 : Λ).1 j : ℝ) : AddCircle (1 : ℝ)) = 0
    have : (0 : Λ).1 = 0 := rfl
    rw [this, lift0, Pi.zero_apply]
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨0, by simp⟩
  · intro γ γ'
    funext j
    show ((lift (γ + γ').1 j : ℝ) : AddCircle (1 : ℝ)) =
      ((lift γ.1 j : ℝ) : AddCircle (1 : ℝ)) + ((lift γ'.1 j : ℝ) : AddCircle (1 : ℝ))
    obtain ⟨φ, hφ, hφγ⟩ := (hΛ _).mp γ.2
    obtain ⟨ψ, hψ, hψγ⟩ := (hΛ _).mp γ'.2
    have hsum : (γ + γ').1 = L (φ * ψ) := by
      rw [hL_mul φ hφ ψ hψ, hφγ, hψγ]; rfl
    rw [hsum, lift_of _ (F.mul_mem hφ hψ)]
    rw [show γ.1 = L φ from hφγ.symm, show γ'.1 = L ψ from hψγ.symm, lift_of φ hφ, lift_of ψ hψ]
    obtain ⟨m, hm⟩ := hvmul φ hφ ψ hψ j
    obtain ⟨m1, hm1⟩ := hv1 j
    simp only [Pi.sub_apply, hm, hm1]
    rw [show (v φ j + v ψ j + (m : ℝ) - (m1 : ℝ) : ℝ) = ((v φ j - (m1 : ℝ)) + (v ψ j - (m1 : ℝ))) + ((m + m1 : ℤ) : ℝ) by
      push_cast; ring, hcoe_int, AddCircle.coe_add]
  · intro γ hγ j; rfl
  · intro φ hφ
    constructor
    · intro w
      show ((lift (L φ) (Fin.castAdd c (Fintype.equivFin (InfinitePlace K) w.1)) : ℝ) : AddCircle (1 : ℝ)) = _
      rw [lift_of φ hφ, Pi.sub_apply, v_left, v_left]
      simp only [argC, Equiv.symm_apply_apply, dif_pos w.2]
      rw [Units.val_one, map_one, harg1, sub_neg_eq_add, hcoe_int]
    · intro j
      show ((lift (L φ) (Fin.natAdd (Fintype.card (InfinitePlace K)) j) : ℝ) : AddCircle (1 : ℝ)) = _
      rw [lift_of φ hφ, Pi.sub_apply, v_right, v_right, hL1]
      simp

end S_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_addMonoidHom_addCircle_lift_arg_of_injOn (solution)
