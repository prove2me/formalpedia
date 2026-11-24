-- Prove2me | solution 1 for GlobalTheory.DetFactor.factors_through_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:06.699864+00:00
-- url     : https://prove2.me/submissions/2640dfb2-4606-4b3f-878d-62a8abbf72fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Theorems.Thm_GlobalTheory_DetFactor_diagGL_val
import Theorems.Thm_GlobalTheory_DetFactor_toGL_val
import Theorems.Thm_GlobalTheory_DetFactor_map_transvection_eq_one
import Theorems.Thm_GlobalTheory_DetFactor_map_diagGL_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DetFactor.toGL_val

set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory.DetFactor
theorem _root_.solution (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) :
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  cases n with
  | zero =>
    refine ⟨1, fun g => ?_⟩
    have : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    simp [this]
  | succ m =>
    refine ⟨(c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0), fun g => ?_⟩
    set χ := (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0)
    let P : Matrix (Fin (m + 1)) (Fin (m + 1)) k → Prop := fun M =>
      ∀ u : GL (Fin (m + 1)) k, (u : Matrix _ _ k) = M → c u = χ (Matrix.GeneralLinearGroup.det u)
    have hg : Matrix.det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    refine diagonal_transvection_induction_of_det_ne_zero P (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) hg ?_ ?_ ?_ g rfl
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := by
        intro i; rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      have hu' : u = diagGL (m + 1) (fun i => Units.mk0 (D i) (hD' i)) := by
        apply Units.ext; rw [hu, diagGL_val]; rfl
      have hdet : Matrix.GeneralLinearGroup.det u = ∏ i, Units.mk0 (D i) (hD' i) := by
        apply Units.ext; simp [hu, det_diagonal]
      rw [hdet, hu', map_diagGL_eq]
    · intro t u hu
      have hu' : u = toGL (transvection t.i t.j t.c) (det_transvection_ne t.hij t.c) := Units.ext hu
      have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
        apply Units.ext; simp [hu, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
      rw [hdet, map_one, hu']
      exact map_transvection_eq_one h2 c t.hij t.c
    · intro A B hA hB PA PB u hu
      have hu' : u = toGL A hA * toGL B hB := Units.ext (by simp [hu])
      rw [hu', map_mul, map_mul, PA _ rfl, PB _ rfl, ← map_mul]
end GlobalTheory.DetFactor
