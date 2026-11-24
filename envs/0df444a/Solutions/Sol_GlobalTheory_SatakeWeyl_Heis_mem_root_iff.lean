-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.mem_root_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:31:26.12911+00:00
-- url     : https://prove2.me/submissions/2176fc49-c89a-481b-871d-775d9664d76f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
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
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.Heis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (g : GU σ 3) :
    g ∈ rootU σ ![0, 0, 0] ↔ ∃ x y, y + σ y + x * σ x = 0 ∧ mat g = Heisenberg₂ σ x y := by
  constructor
  · rintro ⟨hg, -⟩
    have hg : ∀ i j : Fin 3, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 3) (Fin 3) L) i j := hg
    have h1 : cT σ (mat g) * antiJ L 3 * mat g = antiJ L 3 := g.2
    have e00 : mat g 0 0 = 1 := by simpa using hg 0 0 (by decide)
    have e10 : mat g 1 0 = 0 := by simpa using hg 1 0 (by decide)
    have e11 : mat g 1 1 = 1 := by simpa using hg 1 1 (by decide)
    have e20 : mat g 2 0 = 0 := by simpa using hg 2 0 (by decide)
    have e21 : mat g 2 1 = 0 := by simpa using hg 2 1 (by decide)
    have e22 : mat g 2 2 = 1 := by simpa using hg 2 2 (by decide)
    have r0 : (0 : Fin 3).rev = 2 := rfl
    have r1 : (1 : Fin 3).rev = 1 := rfl
    have r2 : (2 : Fin 3).rev = 0 := rfl
    have a := congrFun (congrFun h1 1) 2
    have b := congrFun (congrFun h1 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_three] at a b
    simp only [P.fSatake_cTJ, r0, r1, r2, e11, e21, e22, map_one, map_zero] at a b
    have a' : mat g 1 2 = -σ (mat g 0 1) := by
      have : antiJ L 3 1 2 = 0 := by simp [antiJ]
      linear_combination a + this
    have : antiJ L 3 2 2 = 0 := by simp [antiJ]
    rw [a', map_neg, hσ] at b
    refine ⟨mat g 0 1, mat g 0 2, by linear_combination b + this, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, e00, e10, e11, e20, e21, e22, a']
  · rintro ⟨x, y, -, e⟩
    refine ⟨fun i j h => ?_, fun i j h => ?_⟩
    · rw [e]
      fin_cases i <;> fin_cases j <;> simp [Heisenberg₂] at h ⊢
    · fin_cases i <;> fin_cases j <;> simp at h
end GlobalTheory.SatakeWeyl.Heis
