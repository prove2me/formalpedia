-- Prove2me | solution 1 for MultiItemRev.MultiBuyer.marginal_mechanism_ds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:05:04.2457+00:00
-- url     : https://prove2.me/submissions/871220e8-4f6c-4a3e-869d-d5e13a211eb9

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.MultiBuyer in
theorem solution {n : ℕ} (M : MechanismN n (Fin 2))
    (hF : IsFeasibleN M) (hIC : IsICDS M) (hIR : IsIRDS M) (z : Fin n → ℝ≥0) :
    IsFeasibleN (marginalMech M z) ∧ IsICDS (marginalMech M z) ∧ IsIRDS (marginalMech M z) := by
  refine ⟨⟨fun x j _ => hF.1 (fun l => ![x l (), z l]) j 0,
    fun x _ => hF.2 (fun l => ![x l (), z l]) 0⟩, ?_, ?_⟩
  · intro x j x'
    have hupd : (fun l => ![(Function.update x j x') l (), z l]) =
        Function.update (fun l => ![x l (), z l]) j ![x' (), z j] := by
      funext l
      by_cases h : l = j
      · subst h; simp
      · simp [Function.update_apply, h]
    have h := hIC (fun l => ![x l (), z l]) j ![x' (), z j]
    rw [← hupd] at h
    simp [payoffN, marginalMech, Fin.sum_univ_two] at h ⊢
    linarith
  · intro x j
    have h := hIR (fun l => ![x l (), z l]) j
    simp [payoffN, marginalMech, Fin.sum_univ_two] at h ⊢
    linarith
