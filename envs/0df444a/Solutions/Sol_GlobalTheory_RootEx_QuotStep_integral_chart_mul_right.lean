-- Prove2me | solution 1 for GlobalTheory.RootEx.QuotStep.integral_chart_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:10.62791+00:00
-- url     : https://prove2.me/submissions/1881ed8f-d304-4df6-8b4a-df1c7ca7622f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_integral_comp_mp
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_ext_pos
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_val
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_chart_entries
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_ext
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_chart
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_SgLoc_TriShift_measurePreserving_triangular
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
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
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
variable {b : ι → ℕ} {S : ι × ι → Prop}
variable (hS : ∀ rs, S rs → b rs.1 < b rs.2)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.QuotStep
theorem _root_.solution [Fintype {rs // S rs}] (m : GL ι k)
    (hm : ∀ r s, ¬ S (r, s) → m.val r s = (1 : Matrix ι ι k) r s)
    (hm' : ∀ e r s, ¬ S (r, s) → (chart hS e * m).val r s = (1 : Matrix ι ι k) r s)
    (φ : GL ι k → ℂ) (hφ : Continuous φ) :
    ∫ e, φ (chart hS e * m) ∂(Measure.pi fun _ => ν) = ∫ e, φ (chart hS e) ∂(Measure.pi fun _ => ν) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hT := GlobalTheory.SgLoc.TriShift.measurePreserving_triangular ν (fun i : {rs // S rs} => b i.1.2)
    (fun i e => (m.val - 1) i.1.1 i.1.2 + ∑ t, ext S e i.1.1 t * (m.val - 1) t i.1.2)
    (fun i => (continuous_const.add (continuous_finset_sum _ fun t _ =>
      (continuous_ext S _ _).mul continuous_const)).measurable)
    (fun i x y hxy => by
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h2 : S (t, i.1.2)
      · by_cases h1 : S (i.1.1, t)
        · rw [ext_pos _ h1, ext_pos _ h1, hxy _ (hS _ h2)]
        · rw [ext_neg _ h1, ext_neg _ h1]
      · rw [Matrix.sub_apply, hm _ _ h2, sub_self, mul_zero, mul_zero])
  rw [← integral_comp_mp hT (f := fun e => φ (chart hS e)) (hφ.comp (continuous_chart hS)).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  dsimp only
  rw [← chart_entries hS _ (hm' e)]
  congr 2
  funext i
  have hne : i.1.1 ≠ i.1.2 := fun h => absurd (hS _ i.2) (by rw [h]; exact lt_irrefl _)
  have : (chart hS e * m).val = 1 + (ext S e + ((m.val - 1) + ext S e * (m.val - 1))) := by
    rw [Units.val_mul, chart_val]; noncomm_ring
  rw [this, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.add_apply, ext_pos e i.2]
  rfl
end GlobalTheory.RootEx.QuotStep
