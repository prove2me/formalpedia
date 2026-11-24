-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.Heis.conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:37.485413+00:00
-- url     : https://prove2.me/submissions/6b003989-0b97-40a8-a4ca-f4b9c9d440f9

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv
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
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.SatakeWeyl.Heis
theorem _root_.solution {ϖ : L} (h0 : ϖ ≠ 0) (hϖ : σ ϖ = ϖ) {s : GU σ 3}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, 0, -1] : Fin 3 → ℤ) i)) (g : GU σ 3) (x y : L)
    (e : mat g = Heisenberg₂ σ x y) : mat (s * g * s⁻¹) = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) := by
  have : mat s * mat g = Heisenberg₂ σ (ϖ * x) (ϖ * (ϖ * y)) * mat s := by
    rw [e, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [Heisenberg₂, hϖ] <;> field_simp
  rw [mat_mul, mat_mul, this, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]
end GlobalTheory.SatakeWeyl.Heis
