-- Prove2me | solution 1 for N4Code.equivalent_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:26.014113+00:00
-- url     : https://prove2.me/submissions/db35f751-f8cf-453d-b7b0-4fe826f2cc54

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_rowPermute_comp
import Theorems.Thm_N4Code_flipCol_involutive
import Theorems.Thm_N4Code_rowPermute_flipCol

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {C C' : Code n} (h : Equivalent C C') : Equivalent C' C := by
  rcases h with ⟨ρ, p, f, h⟩
  refine ⟨ρ.symm, p.symm, fun t => f (p.symm t), ?_⟩
  intro t
  have hs : p (p.symm t) = t := p.apply_symm_apply t
  have ht : C' t = rowPermute ρ (if f (p.symm t) then flipCol (C (p.symm t)) else C (p.symm t)) := by
    simpa [hs] using h (p.symm t)
  by_cases hf : f (p.symm t) = true
  · -- flipped case
    have hρ : rowPermute ρ.symm (C' t) = flipCol (C (p.symm t)) := by
      rw [ht]
      simp [hf]
      rw [rowPermute_comp, rowPermute_flipCol]
      have hρρ : ρ.symm.trans ρ = Equiv.refl (Fin 4) := by
        ext j
        simp
      rw [hρρ]
      rfl
    have hCs : C (p.symm t) = flipCol (rowPermute ρ.symm (C' t)) := by
      rw [hρ]
      exact (flipCol_involutive (C (p.symm t))).symm
    have hmain : C (p.symm t) = rowPermute ρ.symm (flipCol (C' t)) := by
      rw [rowPermute_flipCol, hCs]
    simpa [hf] using hmain
  · -- unflipped case
    have hρ : rowPermute ρ.symm (C' t) = C (p.symm t) := by
      rw [ht]
      simp [hf]
      rw [rowPermute_comp]
      have hρρ : ρ.symm.trans ρ = Equiv.refl (Fin 4) := by
        ext j
        simp
      rw [hρρ]
      rfl
    simpa [hf] using hρ.symm
end N4Code
