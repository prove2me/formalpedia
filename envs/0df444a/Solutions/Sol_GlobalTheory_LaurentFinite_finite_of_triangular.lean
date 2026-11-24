-- Prove2me | solution 1 for GlobalTheory.LaurentFinite.finite_of_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:42.179796+00:00
-- url     : https://prove2.me/submissions/7d46bcb8-a296-401d-b53b-1107c076b97f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
import Theorems.Thm_GlobalTheory_LaurentFinite_abs_cut_le
import Theorems.Thm_GlobalTheory_LaurentFinite_sum_sq_lt
import Theorems.Thm_GlobalTheory_LaurentFinite_exists_gap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFinite
open AddMonoidAlgebra
namespace GlobalTheory.LaurentFinite
theorem _root_.solution (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ)))
    (hB : ∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧
      ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) :
    Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  classical
  set S : Finset (AddMonoidAlgebra ℂ (Fin m → ℤ)) :=
    (Fintype.piFinset fun _ : Fin m => Finset.Icc (-(m : ℤ)) m).image fun ν => single ν 1 with hS
  set N : Submodule B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := Submodule.span B (S : Set _) with hN
  have hsm : ∀ (ν : Fin m → ℤ) (c : ℂ), single ν 1 ∈ N → single ν c ∈ N := by
    intro ν c h
    have := N.smul_of_tower_mem c h
    rwa [smul_single', mul_one] at this
  have key : ∀ (n : ℕ) (ν : Fin m → ℤ), ∑ i, ν i ^ 2 < n → single ν (1 : ℂ) ∈ N := by
    intro n
    induction n with
    | zero =>
      intro ν h
      have : 0 ≤ ∑ i, ν i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      simp at h
      omega
    | succ n ih =>
      intro ν h
      by_cases hb : ∀ i, |ν i| ≤ m
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ν, ?_, rfl⟩)
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_Icc.mpr (abs_le.mp (hb i))
      · push Not at hb
        obtain ⟨i0, hi0⟩ := hb
        obtain ⟨j, hj, hj0, hν⟩ := exists_gap ν i0 hi0
        set ε : Fin m → ℤ := fun i => cut j (ν i) with hε
        obtain ⟨s, hsB, hs0, hs⟩ := hB ε fun i => abs_cut_le _ _
        have step : ∀ κ : Fin m → ℤ, (∀ i, |κ i| ≤ 1) → ∑ i, |κ i| ≤ ∑ i, |ε i| → κ ≠ ε →
            single (κ + (ν - ε)) (1 : ℂ) ∈ N := by
          intro κ h1 h2 h3
          apply ih
          have := sum_sq_lt j ν κ hj hν h1 h2 h3
          have e : ∑ i, (κ + (ν - ε)) i ^ 2 = ∑ i, (ν i - cut j (ν i) + κ i) ^ 2 :=
            Finset.sum_congr rfl fun i _ => by simp [hε, add_comm]
          push_cast at h
          omega
        have h0 : single (ν - ε) (1 : ℂ) ∈ N := by
          have := step 0 (by simp) (by simpa using Finset.sum_nonneg fun i _ => abs_nonneg (ε i)) (by
            intro h0
            have h1 : ε i0 = 0 := by rw [← h0]; rfl
            simp only [hε, cut, hj0, if_true, Int.sign_eq_zero_iff_zero] at h1
            rw [h1] at hj0
            simp at hj0
            omega)
          rwa [zero_add] at this
        have h1 : s * single (ν - ε) (1 : ℂ) ∈ N := N.smul_mem ⟨s, hsB⟩ h0
        have h2 : s * single (ν - ε) (1 : ℂ)
            = ∑ κ ∈ s.coeff.support, single (κ + (ν - ε)) (s.coeff κ) := by
          conv_lhs => rw [← sum_coeff_single s, Finsupp.sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun κ _ => by rw [single_mul_single, mul_one]
        rw [h2, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.mpr hs0)] at h1
        have h3 : ∑ κ ∈ s.coeff.support.erase ε, single (κ + (ν - ε)) (s.coeff κ) ∈ N := by
          refine N.sum_mem fun κ hκ => hsm _ _ ?_
          rw [Finset.mem_erase, Finsupp.mem_support_iff] at hκ
          exact step κ (hs κ hκ.2).1 (hs κ hκ.2).2 hκ.1
        have h4 := N.smul_of_tower_mem (s.coeff ε)⁻¹ ((N.add_mem_iff_left h3).mp h1)
        rwa [smul_single', inv_mul_cancel₀ hs0, add_sub_cancel] at h4
  refine Module.Finite.of_fg_top ⟨S, ?_⟩
  rw [eq_top_iff]
  intro x _
  change x ∈ N
  induction x using induction_linear with
  | zero => exact N.zero_mem
  | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)
  | single ν c =>
    refine hsm _ _ (key ((∑ i, ν i ^ 2).toNat + 1) ν ?_)
    push_cast
    omega
end GlobalTheory.LaurentFinite
