-- Prove2me | solution 1 for GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:07.755897+00:00
-- url     : https://prove2.me/submissions/82cf928a-18e4-4190-bcec-2e0e713dbff1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EntriesBoundedOfConjSpanningBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
namespace GlobalTheory.ClassFin
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  intro ι _ _ σ _ g hg C
  have hmem : ∀ k l : ι, ∃ a : σ → ℂ, ∑ s, a s • g s = Matrix.single k l (1 : ℂ) := by
    intro k l
    have : Matrix.single k l (1 : ℂ) ∈ Submodule.span ℂ (Set.range g) := by
      rw [hg]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose a ha using hmem
  set C₁ : ℝ := ∑ k, ∑ l, ∑ s, ‖a k l s‖ * |C| with hC₁
  refine ⟨max 1 ((Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι), ?_⟩
  intro P hP hb i k
  have hent : ∀ l j, ‖P i k * P⁻¹ l j‖ ≤ C₁ := by
    intro l j
    have h1 : P i k * P⁻¹ l j = ∑ s, a k l s * (P * g s * P⁻¹) i j := by
      have h2 : (P * Matrix.single k l (1 : ℂ) * P⁻¹) i j = P i k * P⁻¹ l j := by
        simp [Matrix.mul_apply, Matrix.single, ite_and]
      rw [← h2, ← ha k l, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    have h3 : ‖P i k * P⁻¹ l j‖ ≤ ∑ s, ‖a k l s‖ * |C| := by
      rw [h1]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hb s i j).trans (le_abs_self C)) (norm_nonneg _)
    refine h3.trans ?_
    calc ∑ s, ‖a k l s‖ * |C| ≤ ∑ l, ∑ s, ‖a k l s‖ * |C| :=
          Finset.single_le_sum (f := fun l => ∑ s, ‖a k l s‖ * |C|)
            (fun l _ => by positivity) (Finset.mem_univ l)
      _ ≤ C₁ :=
          Finset.single_le_sum (f := fun k => ∑ l, ∑ s, ‖a k l s‖ * |C|)
            (fun k _ => by positivity) (Finset.mem_univ k)
  have hdetinv : (P⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hP]; simp
  have hdet := Matrix.det_le (A := P i k • P⁻¹) (abv := NormedField.toAbsoluteValue ℂ) (x := C₁)
    (fun l j => hent l j)
  rw [Matrix.det_smul, hdetinv, mul_one] at hdet
  have hdet' : ‖P i k‖ ^ Fintype.card ι ≤
      (Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι := by
    rw [← norm_pow]; exact hdet
  have hN : Fintype.card ι ≠ 0 := (Fintype.card_pos_iff.2 ⟨i⟩).ne'
  rcases le_total ‖P i k‖ 1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact ((le_self_pow₀ h hN).trans hdet').trans (le_max_right _ _)
end GlobalTheory.ClassFin
