-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.IdxFour.mat_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:27.428816+00:00
-- url     : https://prove2.me/submissions/f7108e89-7dab-426b-9878-36b6a2154c4f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism.UG
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.IdxFour
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.IdxFour
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {g : GU σ 4} (hg : g ∈ rootU σ ![0, 0, 1, 1]) :
    mat g = rootMat σ (mat g 0 1) := by
  have h1 : ∀ i j : Fin 4, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 4) (Fin 4) L) i j := hg.1
  have h2 : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ (![0, 0, 1, 1] : Fin 4 → ℕ) j → mat g i j = 0 := hg.2
  have h3 : cT σ (mat g) * antiJ L 4 * mat g = antiJ L 4 := g.2
  have h4 := congrFun (congrFun h3 1) 3
  rw [Matrix.mul_apply] at h4
  simp only [P.fSatake_cTJ, Fin.sum_univ_four] at h4
  have e00 := h1 0 0 (by decide)
  have e11 := h1 1 1 (by decide)
  have e22 := h1 2 2 (by decide)
  have e33 := h1 3 3 (by decide)
  have e10 := h1 1 0 (by decide)
  have e32 := h1 3 2 (by decide)
  have e02 := h2 0 2 (by decide)
  have e03 := h2 0 3 (by decide)
  have e12 := h2 1 2 (by decide)
  have e13 := h2 1 3 (by decide)
  have e20 := h2 2 0 (by decide)
  have e21 := h2 2 1 (by decide)
  have e30 := h2 3 0 (by decide)
  have e31 := h2 3 1 (by decide)
  have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [r0, r1, r2, r3, e03, e13, e11, e33] at h4
  have e23 : mat g 2 3 = -σ (mat g 0 1) := by
    simp [antiJ] at h4
    exact eq_neg_of_add_eq_zero_left h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, *]
end GlobalTheory.SatakeWeyl.IdxFour
