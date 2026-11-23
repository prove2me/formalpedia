-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.integral_volN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:06.241804+00:00
-- url     : https://prove2.me/submissions/d437187e-38b0-4dda-a5a0-43dd9c2f9d63

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
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_chart
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chartN_mem
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chartN_entries
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotStep
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution (q : ℕ) (φ : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c q, φ u ∂(volN ν n c q) = ∫ e, φ (chartN q e) ∂(Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  let eqv : N k n c q ≃ᵐ ({rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k) :=
    { toFun := fun g rs => (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2
      invFun := fun e => ⟨chartN q e, chartN_mem q e⟩
      left_inv := fun g => Subtype.ext (chartN_entries g.2)
      right_inv := fun e => funext fun i => chart_pos (b := lev q) (fun _ h => h) e i
      measurable_toFun := (continuous_pi fun i =>
        (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _).measurable
      measurable_invFun := ((continuous_chart _).subtype_mk _).measurable }
  have : volN ν n c q = (Measure.pi fun _ => ν).map eqv.symm := by
    rw [MeasurableEquiv.map_symm]
    unfold volN
    congr!
  rw [this, integral_map_equiv]
  rfl
end GlobalTheory.RootEx.QuotStep
