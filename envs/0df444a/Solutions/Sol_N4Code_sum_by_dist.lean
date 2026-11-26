-- Prove2me | solution 1 for N4Code.sum_by_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:06:09.950901+00:00
-- url     : https://prove2.me/submissions/1aeaa99e-e24d-42a6-9d04-3711ee97b6e1

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dCode_le


set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (P : Word n → Prop) [DecidablePred P]
    (f : ℕ → ℝ) :
    (∑ y ∈ (Finset.univ.filter P), f (dCode C y)) =
      ∑ d ∈ Finset.Icc 0 n,
        ((Finset.univ.filter fun y : Word n => P y ∧ dCode C y = d).card : ℝ) * f d := by
  let E : ℕ → Finset (Word n) := fun d =>
    Finset.univ.filter fun y : Word n => P y ∧ dCode C y = d
  calc
    (∑ y ∈ (Finset.univ.filter P), f (dCode C y))
        = ∑ x ∈ Finset.sigma (Finset.Icc 0 n) E, f x.1 := by
          refine Finset.sum_bij (fun y hy => ⟨dCode C y, y⟩) ?_ ?_ ?_ ?_
          · intro y hy
            have hle := dCode_le C y
            rw [Finset.mem_sigma]
            exact ⟨by simp [hle], by simpa [E] using hy⟩
          · intro a _ b _ hab
            exact congrArg (fun z : Sigma (fun _ : ℕ => Word n) => z.2) hab
          · intro x hx
            rcases x with ⟨d, y⟩
            have hyE : y ∈ E d := (Finset.mem_sigma.mp hx).2
            have hP : P y := (Finset.mem_filter.mp hyE).2.1
            refine ⟨y, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨by simp, hP⟩
            · have hdist : dCode C y = d := (Finset.mem_filter.mp hyE).2.2
              simp [hdist]
          · intro y hy
            rfl
    _ = ∑ d ∈ Finset.Icc 0 n, (E d).card * f d := by
          rw [Finset.sum_sigma]
          apply Finset.sum_congr rfl
          intro d hd
          simp [E]
end N4Code
