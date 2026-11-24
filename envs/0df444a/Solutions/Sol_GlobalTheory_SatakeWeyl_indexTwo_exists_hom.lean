-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.indexTwo_exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:49:06.978983+00:00
-- url     : https://prove2.me/submissions/666b6978-53ea-42a6-8589-264455acb732

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankTwoRootIndexOfTraceZeroCard
import Theorems.Thm_GlobalTheory_SatakeWeyl_indexTwo_unitary
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution (σ : L →+* L) (T : AddSubgroup L) (hT : ∀ y, y ∈ T ↔ σ y + y = 0) :
    ∃ ψ : Multiplicative T →* GU σ 2,
      ∀ y, mat (ψ y) = !![1, (y.toAdd : L); 0, 1] := by
  have h : ∀ y : Multiplicative T,
      ∃ g : GU σ 2, mat g = !![1, (y.toAdd : L); 0, 1] := fun y =>
    exists_mat _ (indexTwo_unitary _ ((hT _).1 y.toAdd.2))
  choose f hf using h
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, hf⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, AddSubgroup.coe_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
end GlobalTheory.SatakeWeyl
