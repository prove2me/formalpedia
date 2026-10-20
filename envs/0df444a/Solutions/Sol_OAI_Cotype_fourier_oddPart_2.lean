-- Prove2me | solution 2 for OAI.Cotype.fourier_oddPart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:31:19.195317+00:00
-- url     : https://prove2.me/submissions/553f3892-097b-4451-b04f-c592fbfeb15b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Fourier.lean:L72-L90
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.fourier_oddPart. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem average_negate {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : (ι → Bool) → E) : average (fun ε => f (negateCube ε)) = average f := by
  unfold average
  congr 1
  exact Fintype.sum_equiv negateEquiv _ _ (fun _ => rfl)

omit [DecidableEq ι] in
theorem character_negate (p ε : ι → Bool) :
    character p (negateCube ε) = paritySign p * character p ε := by
  unfold character paritySign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp [negateCube]

theorem fourier_negate (f : (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun ε => f (negateCube ε)) p = paritySign p * fourier f p := by
  rw [fourier, ← average_negate]
  simp only [negateCube_negateCube, character_negate]
  simp only [average, fourier, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  ring

theorem fourier_oddPart (f : (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (oddPart f) p = (1 - paritySign p) / 2 * fourier f p := by
  have h := fourier_negate f p
  simp only [fourier, average, smul_eq_mul] at h ⊢
  have he : (∑ ε, oddPart f ε * character p ε) =
      ((∑ ε, f ε * character p ε) -
        ∑ ε, f (negateCube ε) * character p ε) / 2 := by
    calc
      _ = ∑ ε, (f ε * character p ε -
          f (negateCube ε) * character p ε) / 2 := by
        apply Finset.sum_congr rfl
        intro ε _
        dsimp [oddPart]
        ring
      _ = _ := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [he]
  nlinarith [h]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.fourier_oddPart := @_root_.OAI.Cotype.fourier_oddPart
