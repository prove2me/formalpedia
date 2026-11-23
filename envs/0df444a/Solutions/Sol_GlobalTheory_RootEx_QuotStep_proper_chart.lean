-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.proper_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:43.629216+00:00
-- url     : https://prove2.me/submissions/b280922b-c436-4fe9-920b-b372a3605ab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_pos
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_embX
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution {q : ℕ} {b : n ⊕ Fin c → ℕ} {S : (n ⊕ Fin c) × (n ⊕ Fin c) → Prop}
    (hS : ∀ rs, S rs → b rs.1 < b rs.2) (hq : ∀ e, (chart hS e : GL (n ⊕ Fin c) k) ∈ N k n c q)
    (C : Set (GL (n ⊕ Fin c) k)) (hC : IsCompact C) :
    ∃ D, IsCompact D ∧ ∀ t : GL n k × ({rs // S rs} → k), embX c t.1 * chart hS t.2 ∈ C → t ∈ D := by
  haveI := t2Space k
  have c1 : Continuous fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁ :=
    continuous_matrix fun r s => Units.continuous_val.matrix_elem _ _
  have hX := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    ((hC.image c1).prod ((hC.image (c1.comp continuous_inv)).image MulOpposite.continuous_op))
  have c2 : Continuous fun (y : GL n k × GL (n ⊕ Fin c) k) (i : {rs // S rs}) =>
      ((embX c y.1)⁻¹ * y.2).val i.1.1 i.1.2 :=
    continuous_pi fun i => (Units.continuous_val.comp
      ((continuous_embX.comp continuous_fst).inv.mul continuous_snd)).matrix_elem _ _
  refine ⟨_, hX.prod ((hX.prod hC).image c2), fun t ht => ?_⟩
  have h1 : t.1 ∈ Units.embedProduct (Matrix n n k) ⁻¹' ((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) '' C) ×ˢ
      (MulOpposite.op '' (((fun g : GL (n ⊕ Fin c) k => g.val.toBlocks₁₁) ∘ fun a => a⁻¹) '' C)) := by
    refine ⟨⟨_, ht, Radical.toBlocks₁₁_embX_mul _ (hq _)⟩, _, ⟨_, ht, rfl⟩, congrArg MulOpposite.op ?_⟩
    rw [← Radical.toBlocks₁₁_embX_mul t.1⁻¹ (Radical.conj_mem t.1 (inv_mem (hq t.2))), map_inv,
      mul_assoc, inv_mul_cancel_left, ← _root_.mul_inv_rev]
    rfl
  refine ⟨h1, (t.1, _), ⟨h1, ht⟩, funext fun i => ?_⟩
  simp only [inv_mul_cancel_left]
  exact chart_pos hS _ i
end GlobalTheory.RootEx.QuotStep
