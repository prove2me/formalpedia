-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7e0d6815-578b-5d5a-aba7-fbfb473dd33d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (P₀ P₁ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (hP₀ : ContDiff ℝ (⊤ : ℕ∞) P₀)
    (hP₀_per : ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
      (k : Fin (nrComplexPlaces K) → ℤ), P₀ (x, θ + fun j => (k j : ℝ)) = P₀ (x, θ))
    (hP_mul : ∀ (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P₀ (x + x', θ + θ') = P₀ (x, θ) * P₁ (x', θ'))
    (hP₀_bdd : ∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
      ∃ R : ℝ, ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
        P₀ (x, θ) ∈ C → ∀ i, |x i| ≤ R)
    (Wa : mixedSpace K → ℂ) (hWa : ContDiff ℝ (⊤ : ℕ∞) Wa)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y)
    (hWa0 : ∀ y, Wa y ≠ 0 → y ∈ C₀)
    {c d : ℕ} (cs : Fin (nrComplexPlaces K) → Fin d) (ts : Fin c → Fin d)
    (t : Fin c → ℂ) (ht : ∀ j, t j ≠ 0)
    (ℓ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ)
    (x₀ : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ₀ : Fin (nrComplexPlaces K) → ℝ) (n₀ : Fin c → ℤ) :
    ∃ G : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ Rb : ℝ, 0 ≤ Rb ∧
        ∀ p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ), (∃ i, Rb < |p.1 i|) → G p = 0) ∧
      (∀ (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ)) (J : Fin d),
        G (p.1, p.2 + Pi.single J 1) = G p) ∧
      ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (k : Fin c → ℤ)
        (Θ : Fin d → ℝ),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (t j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖t j‖ ^ (-(k j)) →
        G (x₀ + x, Θ) = (∏ j, t j ^ (-(n₀ j + k j))) * Wa (P₀ (x₀, θ₀) * P₁ (x, θ)) := by
  obtain ⟨R, hR⟩ := hP₀_bdd C₀ hC₀ hC₀u
  let A : ℂ := ∏ j, t j ^ (-(n₀ j))
  let θof : (Fin d → ℝ) → (Fin (nrComplexPlaces K) → ℝ) := fun Θ j => θ₀ j + Θ (cs j)
  let G : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ := fun p =>
    A * Complex.exp ((ℓ (p.1 - x₀) : ℝ) : ℂ) *
      Complex.exp (∑ j, (p.2 (ts j) : ℂ) * (2 * Real.pi * Complex.I)) * Wa (P₀ (p.1, θof p.2))
  have hθof_smooth : ContDiff ℝ (⊤ : ℕ∞)
      fun p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) => θof p.2 := by
    refine contDiff_pi.2 fun j => ?_
    exact contDiff_const.add ((contDiff_apply ℝ ℝ (cs j)).comp contDiff_snd)
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) G := by
    refine ((contDiff_const.mul ?_).mul ?_).mul ?_
    · refine Complex.contDiff_exp.comp ?_
      refine (Complex.ofRealCLM.contDiff).comp ?_
      exact (ℓ.toContinuousLinearMap.contDiff).comp (contDiff_fst.sub contDiff_const)
    · refine Complex.contDiff_exp.comp ?_
      refine ContDiff.sum fun j _ => ?_
      refine ContDiff.mul ?_ contDiff_const
      exact (Complex.ofRealCLM.contDiff).comp ((contDiff_apply ℝ ℝ (ts j)).comp contDiff_snd)
    · exact hWa.comp (hP₀.comp (contDiff_fst.prodMk hθof_smooth))
  refine ⟨G, hG_smooth, ⟨max R 0, le_max_right _ _, ?_⟩, ?_, ?_⟩
  ·
    rintro p ⟨i, hi⟩
    suffices hW : Wa (P₀ (p.1, θof p.2)) = 0 by
      simp only [G, hW, mul_zero]
    by_contra hW
    have hmem := hWa0 _ hW
    have := hR p.1 (θof p.2) hmem i
    exact absurd (lt_of_le_of_lt (le_max_left R 0) hi) (not_lt.2 this)
  ·
    intro p J
    have h1 : θof (p.2 + Pi.single J 1) = θof p.2 + fun j => ((if cs j = J then (1 : ℤ) else 0 : ℤ) : ℝ) := by
      funext j
      simp only [θof, Pi.add_apply, Pi.single_apply]
      split_ifs <;> push_cast <;> ring
    have h2 : Complex.exp (∑ j, ((p.2 + Pi.single J (1 : ℝ) : Fin d → ℝ) (ts j) : ℂ) * (2 * Real.pi * Complex.I)) =
        Complex.exp (∑ j, (p.2 (ts j) : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [Complex.exp_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Pi.add_apply, Pi.single_apply, Complex.ofReal_add, add_mul, Complex.exp_add]
      split_ifs
      · simp [Complex.exp_two_pi_mul_I]
      · simp
    show A * _ * _ * _ = A * _ * _ * _
    rw [h2, h1, hP₀_per]
  ·
    intro x θ k Θ hcs hts hℓ

    have ha : Complex.exp ((ℓ (x₀ + x - x₀) : ℝ) : ℂ) = ∏ j, ((‖t j‖ : ℝ) : ℂ) ^ (-(k j)) := by
      rw [add_sub_cancel_left, ← Complex.ofReal_exp, hℓ]
      push_cast
      rfl

    have hb : Complex.exp (∑ j, (Θ (ts j) : ℂ) * (2 * Real.pi * Complex.I)) =
        ∏ j, Complex.exp ((t j).arg * Complex.I) ^ (-(k j)) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      obtain ⟨m, hm⟩ : ∃ m : ℤ, Θ (ts j) = -(k j : ℝ) * (t j).arg / (2 * Real.pi) + m := by
        have h := hts j
        rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
        obtain ⟨m, hm⟩ := h
        refine ⟨-m, ?_⟩
        simp only [zsmul_eq_mul, mul_one] at hm
        push_cast
        linarith
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have harg : ((-(k j : ℝ) * (t j).arg / (2 * Real.pi) + (m : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I) =
          ((-(k j) : ℤ) : ℂ) * (((t j).arg : ℂ) * Complex.I) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
      rw [hm, harg, Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul_two_pi_mul_I, mul_one]

    have hc : P₀ (x₀ + x, θof Θ) = P₀ (x₀, θ₀) * P₁ (x, θ) := by
      have : ∃ m : Fin (nrComplexPlaces K) → ℤ, θof Θ = θ₀ + θ + fun j => (m j : ℝ) := by
        have hm : ∀ j, ∃ m : ℤ, Θ (cs j) = θ j + m := by
          intro j
          have h := hcs j
          rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
          obtain ⟨m, hm⟩ := h
          refine ⟨m, ?_⟩
          simp only [zsmul_eq_mul, mul_one] at hm
          linarith
        choose m hm using hm
        refine ⟨m, funext fun j => ?_⟩
        simp only [θof, Pi.add_apply, hm j]
        ring
      obtain ⟨m, hm⟩ := this
      rw [hm, hP₀_per, hP_mul]

    show A * Complex.exp ((ℓ (x₀ + x - x₀) : ℝ) : ℂ) *
        Complex.exp (∑ j, (Θ (ts j) : ℂ) * (2 * Real.pi * Complex.I)) * Wa (P₀ (x₀ + x, θof Θ)) = _
    rw [ha, hb, hc, mul_assoc A, ← Finset.prod_mul_distrib]
    have hd : ∀ j, ((‖t j‖ : ℝ) : ℂ) ^ (-(k j)) * Complex.exp ((t j).arg * Complex.I) ^ (-(k j)) =
        t j ^ (-(k j)) := by
      intro j
      rw [← mul_zpow, Complex.norm_mul_exp_arg_mul_I]
    simp_rw [hd]
    rw [show A * ∏ j, t j ^ (-(k j)) = ∏ j, t j ^ (-(n₀ j + k j)) from ?_]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [neg_add, zpow_add₀ (ht j)]

end S_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord (solution)
