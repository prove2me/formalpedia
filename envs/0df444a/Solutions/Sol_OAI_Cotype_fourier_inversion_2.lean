-- Prove2me | solution 2 for OAI.Cotype.fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:26:08.454991+00:00
-- url     : https://prove2.me/submissions/0e7dcf4c-6210-4d61-aed0-8a4393086d99

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Cube.lean:L59-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.fourier_inversion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube

-- ---- from OAI.Analysis.Cotype.Cube ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem character_symm (p ε : ι → Bool) : character p ε = character ε p := by
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> cases ε i <;> rfl

theorem fourier_inversion (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    (∑ p, fourier f p * character p ε) = f ε := by
  classical
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι → Bool))
  have ho (η : ι → Bool) :
      (∑ p, character p η * character p ε) =
        if η = ε then (Fintype.card (ι → Bool) : ℝ) else 0 := by
    simp_rw [character_symm _ η, character_symm _ ε]
    exact character_orthogonality η ε
  calc
    (∑ p, fourier f p * character p ε) =
        (Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ η, f η * ∑ p, character p η * character p ε := by
      simp only [fourier, average, smul_eq_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro η _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = f ε := by simp [ho, mul_comm (f ε)]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.fourier_inversion := @_root_.OAI.Cotype.fourier_inversion
