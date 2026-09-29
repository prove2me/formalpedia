-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_quadratic_termination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T00:17:39.096402+00:00
-- url     : https://prove2.me/submissions/1fb97548-4414-4889-9640-8a130133a926

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_grad_orthogonality

open Matrix

open LimitedBFGS.SQN

/-- Dotting a finite linear combination against a fixed vector distributes over the
coefficients. The `dotProduct` on a function type unfolds to a finite sum, so this is
the bilinearity fact the orthogonality argument needs. -/
theorem dot_lincomb {ι : Type} [Fintype ι] {m : ℕ} (c : ι → ℝ) (v : ι → (Fin m → ℝ))
    (z : Fin m → ℝ) : (∑ i, c i • v i) ⬝ᵥ z = ∑ i, c i * (v i ⬝ᵥ z) := by
  have hsmul : ∀ (a : ℝ) (u w : Fin m → ℝ), (a • u) ⬝ᵥ w = a * (u ⬝ᵥ w) := by
    intro a u w
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  have hsplit : ∀ (u q w : Fin m → ℝ), (u + q) ⬝ᵥ w = u ⬝ᵥ w + q ⬝ᵥ w := by
    intro u q w
    simp [dotProduct, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  classical
  have key : ∀ s : Finset ι,
      (∑ i ∈ s, c i • v i) ⬝ᵥ z = ∑ i ∈ s, c i * (v i ⬝ᵥ z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [hsplit, hsmul, ih]
  simpa [dotProduct] using key Finset.univ

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∃ k ≤ n, grad A b (pcgIter A b H₀ x₀ k).x = 0 := by
  classical
  set G : Fin (n + 1) → (Fin n → ℝ) :=
    fun i => grad A b (pcgIter A b H₀ x₀ (i : ℕ)).x with hGdef
  by_cases hex : ∃ k : ℕ, k ≤ n ∧ grad A b (pcgIter A b H₀ x₀ k).x = 0
  · exact hex
  have hne : ∀ i : Fin (n + 1), G i ≠ 0 := by
    intro i hGi
    exact hex ⟨(i : ℕ), (Nat.lt_succ_iff.mp i.isLt), hGi⟩
  have horth : ∀ i j : Fin (n + 1), i ≠ j → G i ⬝ᵥ (H₀ *ᵥ G j) = 0 := by
    intro i j hij
    have hne' : (i : ℕ) ≠ (j : ℕ) := by
      intro hc
      exact hij (Fin.ext hc)
    exact hGdef ▸ pcg_grad_orthogonality A hA b H₀ hH₀ x₀ (i : ℕ) (j : ℕ) hne'
  have hli : LinearIndependent ℝ G := by
    rw [linearIndependent_iff_injective_fintypeLinearCombination, Function.Injective]
    intro c f hcf
    simp only [Fintype.linearCombination_apply] at hcf
    have hdecomp : (∑ i, (c i - f i) • G i) = 0 := by
      have hsplit' : ∀ (a d : Fin (n + 1) → ℝ) (v : Fin (n + 1) → (Fin n → ℝ)),
          (∑ i, (a i - d i) • v i) = (∑ i, a i • v i) - ∑ i, d i • v i := by
        intro a d v
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_smul]
      calc (∑ i, (c i - f i) • G i)
          = (∑ i, c i • G i) - ∑ i, f i • G i := hsplit' c f G
        _ = 0 := sub_eq_zero.mpr hcf
    funext i
    have hdots := congrArg (fun w : (Fin n → ℝ) => w ⬝ᵥ (H₀ *ᵥ G i)) hdecomp
    rw [dot_lincomb] at hdots
    have hdots0 : (∑ j, (c j - f j) * (G j ⬝ᵥ (H₀ *ᵥ G i))) = 0 := by
      simpa [dotProduct] using hdots
    have hfz := Finset.eq_zero_of_sum_eq_zero
      (f := fun j => (c j - f j) * (G j ⬝ᵥ (H₀ *ᵥ G i))) hdots0
      (fun j _ hj => by rw [horth j i hj]; simp)
    have hone := hfz i (Finset.mem_univ i)
    have hpos : 0 < G i ⬝ᵥ (H₀ *ᵥ G i) := hH₀.dotProduct_mulVec_pos (hne i)
    exact sub_eq_zero.mp (mul_eq_zero.mp hone |>.resolve_right (fun h => (ne_of_gt hpos) h))
  have hcard : Fintype.card (Fin (n + 1)) ≤ (Set.range G).finrank ℝ :=
    linearIndependent_iff_card_le_finrank_span.mp hli
  have hfin : (Set.range G).finrank ℝ ≤ Module.finrank ℝ (Fin n → ℝ) := by
    have hsub : (Set.range G : Set (Fin n → ℝ)) ⊆ (Set.univ : Set (Fin n → ℝ)) :=
      Set.subset_univ _
    have htop : (Set.univ : Set (Fin n → ℝ)).finrank ℝ = Module.finrank ℝ (Fin n → ℝ) := by
      rw [Set.finrank, Submodule.span_univ, finrank_top]
    exact (Set.finrank_mono hsub).trans_eq htop
  have hbad : Fintype.card (Fin (n + 1)) ≤ Module.finrank ℝ (Fin n → ℝ) := hcard.trans hfin
  simp only [Fintype.card_fin, Module.finrank_fin_fun] at hbad
  omega

