-- Prove2me | solution 1 for LinExchangeSP.ZPlus.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:01:50.229959+00:00
-- url     : https://prove2.me/submissions/26866e1f-c76c-422e-964c-3cfb64a648b8

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting

set_option autoImplicit false
open LinExchangeSP.ZPlus

theorem solution {t : ℕ} (ht : 0 < t) (M : Matrix (Fin t) (Fin t) ℚ) (hM : IsZPlus M)
    (γ : Fin t → ℚ) (hγ : ∀ i, 0 < γ i) (p : Fin t → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hMp : ∀ i, rowVal M p i ≤ (γ i : ℝ)) :
    ∀ i, -((lam γ i : ℚ) : ℝ) ≤ rowVal M p i ∧
      -((Bconst γ ht - 1) * (γ i : ℝ)) ≤ -((lam γ i : ℚ) : ℝ) := by
  intro i
  have hcolsum : ∀ j, (0 : ℝ) ≤ ∑ l, (M l j : ℝ) := by
    intro j
    have h := hM.2 j
    have h' : (0 : ℝ) ≤ ((∑ l, M l j : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hsum : 0 ≤ ∑ l, rowVal M p l := by
    unfold rowVal
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro j _
    rw [← Finset.sum_mul]
    exact mul_nonneg (hcolsum j) (hp j)
  have hlam : ((lam γ i : ℚ) : ℝ) = (∑ j, (γ j : ℝ)) - (γ i : ℝ) := by
    unfold lam
    push_cast
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  constructor
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
    have h2 : ∑ l ∈ Finset.univ.erase i, rowVal M p l ≤ ∑ l ∈ Finset.univ.erase i, (γ l : ℝ) :=
      Finset.sum_le_sum (fun l _ => hMp l)
    rw [hlam, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    linarith
  · have hne : (Finset.univ : Finset (Fin t)).Nonempty := ⟨⟨0, ht⟩, Finset.mem_univ _⟩
    have hm : 0 < Finset.univ.inf' hne (fun i => (γ i : ℝ)) := by
      rw [Finset.lt_inf'_iff]
      intro j _
      exact_mod_cast hγ j
    have hmi : Finset.univ.inf' hne (fun i => (γ i : ℝ)) ≤ (γ i : ℝ) :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have hS : 0 ≤ ∑ j, (γ j : ℝ) :=
      Finset.sum_nonneg (fun j _ => by exact_mod_cast (hγ j).le)
    unfold Bconst
    set m := Finset.univ.inf' hne (fun i => (γ i : ℝ)) with hmdef
    set S := ∑ j, (γ j : ℝ) with hSdef
    have key : S ≤ S / m * (γ i : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]
      exact mul_le_mul_of_nonneg_left hmi hS
    rw [hlam]
    nlinarith [key]
