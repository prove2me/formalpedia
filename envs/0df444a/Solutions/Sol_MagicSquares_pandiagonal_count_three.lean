-- Prove2me | solution 1 for MagicSquares.pandiagonal_count_three
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T15:38:18.851996+00:00
-- url     : https://prove2.me/submissions/6c54ca36-ab9e-4305-9a75-79537cadc2c8

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresPandiagonal

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

private lemma pandiagonal_three_entries (t : ℕ) (M : Square 3 ℕ)
    (hM : IsPandiagonal M t) :
    M 1 0 = M 0 1 ∧ M 1 1 = M 0 2 ∧ M 1 2 = M 0 0 ∧
      M 2 0 = M 0 2 ∧ M 2 1 = M 0 0 ∧ M 2 2 = M 0 1 := by
  obtain ⟨hsemi, hbd⟩ := hM
  have hR0 : M 0 0 + M 0 1 + M 0 2 = t := by
    simpa [rowSum, Fin.sum_univ_three] using hsemi.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = t := by
    simpa [rowSum, Fin.sum_univ_three] using hsemi.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = t := by
    simpa [rowSum, Fin.sum_univ_three] using hsemi.1 (2 : Fin 3)
  have hC0 : M 0 0 + M 1 0 + M 2 0 = t := by
    simpa [colSum, Fin.sum_univ_three] using hsemi.2 (0 : Fin 3)
  have hC1 : M 0 1 + M 1 1 + M 2 1 = t := by
    simpa [colSum, Fin.sum_univ_three] using hsemi.2 (1 : Fin 3)
  have hC2 : M 0 2 + M 1 2 + M 2 2 = t := by
    simpa [colSum, Fin.sum_univ_three] using hsemi.2 (2 : Fin 3)
  have hB0 : M 0 0 + M 1 1 + M 2 2 = t := by
    have h := hbd (0 : Fin 3)
    simpa [brokenDiagSum, Fin.sum_univ_three] using h
  have hB1 : M 0 1 + M 1 2 + M 2 0 = t := by
    have h := hbd (1 : Fin 3)
    simpa [brokenDiagSum, Fin.sum_univ_three] using h
  have hB2 : M 0 2 + M 1 0 + M 2 1 = t := by
    have h := hbd (2 : Fin 3)
    simpa [brokenDiagSum, Fin.sum_univ_three] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Solution for `MagicSquares.pandiagonal_count_three`: BCCG's `P_3(t) = (t+2).choose 2`. Every pandiagonal `3 x 3` square of line sum `t` is `M i j = g (i + j)` for a single `g : Fin 3 -> N`, and the line sum is `g 0 + g 1 + g 2`; so the count is the number of triples of naturals summing to `t`, equivalently the number of pairs `(a, b)` with `a + b <= t`. -/
theorem solution (t : ℕ) :
    pandiagonalCount 3 t = (t + 2).choose 2 := by
  classical
  rw [pandiagonalCount, pandiagonalSquares]
  have hbij : (Finset.univ.filter (fun M : Square 3 (Fin (t + 1)) =>
        IsPandiagonal (fun i j => (M i j : ℕ)) t)).card =
      ((Finset.range (t + 1)).sigma fun a => Finset.range (t - a + 1)).card := by
    refine Finset.card_bij (fun M _ => ⟨(M 0 1 : ℕ), (M 0 2 : ℕ)⟩) ?_ ?_ ?_
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
      simp only [Finset.mem_sigma, Finset.mem_range]
      have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = t := by
        simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
      exact ⟨(M 0 1).isLt, by omega⟩
    · intro M₁ hM₁ M₂ hM₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM₁ hM₂
      have he1 : (M₁ 0 1 : ℕ) = (M₂ 0 1 : ℕ) := congrArg Sigma.fst heq
      have he2 : (M₁ 0 2 : ℕ) = (M₂ 0 2 : ℕ) := congrArg Sigma.snd heq
      have hR0₁ : (M₁ 0 0 : ℕ) + (M₁ 0 1 : ℕ) + (M₁ 0 2 : ℕ) = t := by
        simpa [rowSum, Fin.sum_univ_three] using hM₁.1.1 (0 : Fin 3)
      have hR0₂ : (M₂ 0 0 : ℕ) + (M₂ 0 1 : ℕ) + (M₂ 0 2 : ℕ) = t := by
        simpa [rowSum, Fin.sum_univ_three] using hM₂.1.1 (0 : Fin 3)
      have t0 : (M₁ 0 0 : ℕ) = (M₂ 0 0 : ℕ) := by omega
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        pandiagonal_three_entries t (fun i j => (M₁ i j : ℕ)) hM₁
      obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆⟩ :=
        pandiagonal_three_entries t (fun i j => (M₂ i j : ℕ)) hM₂
      have hall : ∀ i j : Fin 3, (M₁ i j : ℕ) = (M₂ i j : ℕ) := by
        intro i j
        fin_cases i <;> fin_cases j
        · exact t0
        · exact he1
        · exact he2
        · exact (h₁.trans (he1.trans g₁.symm))
        · exact (h₂.trans (he2.trans g₂.symm))
        · exact (h₃.trans (t0.trans g₃.symm))
        · exact (h₄.trans (he2.trans g₄.symm))
        · exact (h₅.trans (t0.trans g₅.symm))
        · exact (h₆.trans (he1.trans g₆.symm))
      funext i j
      exact Fin.ext (hall i j)
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      have hsum : p.1 + p.2 ≤ t := by omega
      let g : Fin 3 → ℕ := fun k =>
        if (k : ℕ) = 0 then t - p.1 - p.2 else if (k : ℕ) = 1 then p.1 else p.2
      let M : Square 3 (Fin (t + 1)) := fun i j => ⟨g (i + j), by
        fin_cases i <;> fin_cases j <;> (simp only [g]; split_ifs <;> omega)⟩
      have hMf : ∀ i j : Fin 3, (M i j : ℕ) = g (i + j) := fun i j => rfl
      refine ⟨M, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨fun i => ?_, fun j => ?_⟩, fun k => ?_⟩
        · fin_cases i <;>
            (simp [rowSum, Fin.sum_univ_three, hMf, g]; omega)
        · fin_cases j <;>
            (simp [colSum, Fin.sum_univ_three, hMf, g]; omega)
        · fin_cases k <;>
            (simp [brokenDiagSum, Fin.sum_univ_three, hMf, g]; omega)
      · obtain ⟨a, b⟩ := p
        have h1 : (M 0 1 : ℕ) = a := by
          show g (1 : Fin 3) = a
          simp [g]
        have h2 : (M 0 2 : ℕ) = b := by
          show g (2 : Fin 3) = b
          simp [g]
        simp only [h1, h2]
  rw [hbij, Finset.card_sigma]
  have hstep : ∀ a : ℕ, (Finset.range (t - a + 1)).card = t - a + 1 := fun a =>
    Finset.card_range _
  simp only [hstep]
  rw [show (∑ a ∈ Finset.range (t + 1), (t - a + 1))
      = ∑ a ∈ Finset.range (t + 1), (a + 1) from by
    simpa using (Finset.sum_range_reflect (fun a : ℕ => a + 1) (t + 1))]
  rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range,
    smul_eq_mul, mul_one, ← Nat.choose_two_right]
  rw [Nat.choose_succ_succ' (t + 1) 1, Nat.choose_one_right, Nat.add_comm]

/-! ## Order three: the two-direction contrast -/
