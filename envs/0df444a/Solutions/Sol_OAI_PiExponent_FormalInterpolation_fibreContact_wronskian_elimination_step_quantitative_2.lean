-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_quantitative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T03:43:21.99298+00:00
-- url     : https://prove2.me/submissions/aafd224e-e298-4fea-b74d-05d59b3f842d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_wronskian_elimination_step_prefix_budget

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {n : Nat} (W V : Fin (n + 1) → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin (n + 1) → E)
    (hlast : ∀ a : Complex, x (Fin.last n) ≠ algebraMap Complex E a)
    (B : Real)
    (hprefix : ∀ T : Nat, 0 < T →
      ∀ U : MvPolynomial (Fin n) Complex, U ≠ 0 →
        fibreContactSupportBound (fun i => W i.castSucc) T U →
        ∃ word : List (Fin n),
          fibreContactWordCost (fun i => V i.castSucc) word ≤ B * (T : Real) ∧
          MvPolynomial.aeval (fun i => x i.castSucc) (fibreContactWord word U) ≠ 0)
    (N : Nat) (hN : 0 < N)
    (F : MvPolynomial (Fin (n + 1)) Complex) (hF : F ≠ 0)
    (hbound : fibreContactSupportBound W N F) :
    ∃ word : List (Fin (n + 1)),
      fibreContactWordCost V word ≤
        (B + (∑ i : Fin n, (V i.castSucc : Real)) /
          (W (Fin.last n) : Real)) * (N : Real) ∧
      MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by
  have hOneBound :
      fibreContactSupportBound (fun i => W i.castSucc) 1
        (1 : MvPolynomial (Fin n) Complex) := by
    intro a ha
    simp only [MvPolynomial.support_one, Finset.mem_singleton] at ha
    subst a
    simp [fibreContactSupportBound]
  obtain ⟨w, hw, _⟩ :=
    hprefix 1 (by norm_num) 1 (by norm_num) hOneBound
  have hcost_nonneg :
      0 ≤ fibreContactWordCost (fun i => V i.castSucc) w := by
    unfold fibreContactWordCost
    apply List.sum_nonneg
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact le_of_lt (hV i.castSucc)
  have hB : 0 ≤ B := by
    have : fibreContactWordCost (fun i => V i.castSucc) w ≤ B := by
      simpa using hw
    linarith
  obtain ⟨word, hword, heval⟩ :=
    OAI.PiExponent.FormalInterpolation.fibreContact_wronskian_elimination_step_prefix_budget
      W V hW hV E x hlast B hprefix N hN F hF hbound
  have hsum_nonneg :
      0 ≤ ∑ i : Fin n, (V i.castSucc : Real) := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (hV i.castSucc)
  have hallow_nonneg :
      0 ≤ (∑ i : Fin n, (V i.castSucc : Real)) /
        (W (Fin.last n) : Real) :=
    div_nonneg hsum_nonneg (le_of_lt (hW (Fin.last n)))
  refine ⟨word, ?_, heval⟩
  nlinarith [hword, hB, hN, hallow_nonneg]