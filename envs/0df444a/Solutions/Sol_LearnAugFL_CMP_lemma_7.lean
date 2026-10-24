-- Prove2me | solution 1 for LearnAugFL.CMP.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:31:13.034802+00:00
-- url     : https://prove2.me/submissions/0801375d-a732-4641-837a-93e41603c74e

import Mathlib
import Definitions.Def_LearnAugFL_CMP_Setting
import Theorems.Thm_LearnAugFL_CMP_lemma_8
import Theorems.Thm_LearnAugFL_CMP_theorem_9

open LearnAugFL.CMP

def Theorem9Statement : Prop :=
  ∀ (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (n k : ℕ) (hnk : Admissible c n k)
    (P : Fin n → Pt),
    (∀ o : Pt, IsOpt P o →
        ucost P (cmp P o k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 + c) * ucost P o) ∧
    (∀ ô o : Pt, IsOpt P o →
        ucost P (cmp P ô k) ≤ Real.sqrt (2 * c ^ 2 + 2) / (1 - c) * ucost P o)

namespace LearnAugFL.CMP.WorstCaseProof

lemma ucost_nonneg {n : ℕ} (P : Fin n → Pt) (z : Pt) : 0 ≤ ucost P z := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg)) (Nat.cast_nonneg n)

lemma sharp_le_consistency (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∃ n k, Admissible c n k) (a : ℝ)
    (ha : ∀ (m k : ℕ) (Q : Fin m → Pt), COA_C c m k Q →
      ucost Q (cmp Q !₂[0,1] k) ≤ a * ucost Q !₂[0,1]) :
    Real.sqrt (2*c^2+2)/(1+c) ≤ a := by
  obtain ⟨n,k,Q,hQ,he⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 hc).1
  have ht : 0 < Real.sqrt (2*c^2+2)/(1+c) := by positivity
  have hn : ucost Q !₂[0,1] ≠ 0 := by
    intro h
    simp only [ratio,h,div_zero] at he
    linarith
  have hp : 0 < ucost Q !₂[0,1] := lt_of_le_of_ne (ucost_nonneg _ _) (Ne.symm hn)
  have hh := ha n k Q hQ
  have hh' := (div_le_iff₀ hp).mpr hh
  change ratio Q !₂[0,1] !₂[0,1] k ≤ a at hh'
  rwa [he] at hh'

lemma sharp_le_robustness (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∃ n k, Admissible c n k) (a : ℝ)
    (ha : ∀ (m k : ℕ) (Q : Fin m → Pt), COA_R c m k Q →
      ucost Q (cmp Q 0 k) ≤ a * ucost Q !₂[0,1]) :
    Real.sqrt (2*c^2+2)/(1-c) ≤ a := by
  obtain ⟨n,k,Q,hQ,he⟩ := (LearnAugFL.CMP.lemma_8 c hc0 hc1 hc).2
  have ht : 0 < Real.sqrt (2*c^2+2)/(1-c) :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) (by linarith)
  have hn : ucost Q !₂[0,1] ≠ 0 := by
    intro h
    simp only [ratio,h,div_zero] at he
    linarith
  have hp : 0 < ucost Q !₂[0,1] := lt_of_le_of_ne (ucost_nonneg _ _) (Ne.symm hn)
  have hh := ha n k Q hQ
  have hh' := (div_le_iff₀ hp).mpr hh
  change ratio Q 0 !₂[0,1] k ≤ a at hh'
  rwa [he] at hh'

end LearnAugFL.CMP.WorstCaseProof

open LearnAugFL.CMP.WorstCaseProof

theorem conditional_solution (h9 : Theorem9Statement) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt), COA_C c m k' Q →
        ucost Q (cmp Q !₂[0, 1] k') ≤ α * ucost Q !₂[0, 1]) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt), COA_R c m k' Q →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q !₂[0, 1]) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o) := by
  constructor
  · intro α hα n k hnk P o ho
    have hsharp := sharp_le_consistency c hc0 hc1 ⟨n, k, hnk⟩ α hα
    exact ((h9 c hc0 hc1 n k hnk P).1 o ho).trans
      (mul_le_mul_of_nonneg_right hsharp (ucost_nonneg P o))
  · intro β hβ n k hnk P ô o ho
    have hsharp := sharp_le_robustness c hc0 hc1 ⟨n, k, hnk⟩ β hβ
    exact ((h9 c hc0 hc1 n k hnk P).2 ô o ho).trans
      (mul_le_mul_of_nonneg_right hsharp (ucost_nonneg P o))


theorem solution (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∀ α : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt), COA_C c m k' Q →
        ucost Q (cmp Q !₂[0, 1] k') ≤ α * ucost Q !₂[0, 1]) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (o : Pt), IsOpt P o →
        ucost P (cmp P o k) ≤ α * ucost P o) ∧
    (∀ β : ℝ,
      (∀ (m k' : ℕ) (Q : Fin m → Pt), COA_R c m k' Q →
        ucost Q (cmp Q 0 k') ≤ β * ucost Q !₂[0, 1]) →
      ∀ (n k : ℕ), Admissible c n k → ∀ (P : Fin n → Pt) (ô o : Pt), IsOpt P o →
        ucost P (cmp P ô k) ≤ β * ucost P o) := by
  exact conditional_solution LearnAugFL.CMP.theorem_9 c hc0 hc1
