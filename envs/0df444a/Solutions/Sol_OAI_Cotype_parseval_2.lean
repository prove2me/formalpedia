-- Prove2me | solution 2 for OAI.Cotype.parseval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:29:38.776251+00:00
-- url     : https://prove2.me/submissions/3e985073-fdd1-42e7-ae21-8a0d5faf3449

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Cube.lean:L83-L101
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.parseval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Theorems.Thm_OAI_Cotype_fourier_inversion

-- ---- from OAI.Analysis.Cotype.Cube ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem parseval (f : (ι → Bool) → ℝ) :
    (∑ p, fourier f p ^ 2) = average (fun ε => f ε ^ 2) := by
  classical
  calc
    (∑ p, fourier f p ^ 2) =
        ∑ p, fourier f p * ((Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ ε, f ε * character p ε) := by
      simp only [fourier, average, smul_eq_mul, pow_two]
    _ = (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ ε, f ε * ∑ p, fourier f p * character p ε := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ε _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = average (fun ε => f ε ^ 2) := by
      simp only [fourier_inversion, average, smul_eq_mul, pow_two]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.parseval := @_root_.OAI.Cotype.parseval
