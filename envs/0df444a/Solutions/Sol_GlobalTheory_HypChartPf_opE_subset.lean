-- Prove2me | solution 1 for GlobalTheory.HypChartPf.opE_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:32:36.339037+00:00
-- url     : https://prove2.me/submissions/ae51b65c-fa9e-4718-9ecf-93bbd91fd758

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
import Theorems.Thm_GlobalTheory_HypChartPf_exp_form
import Theorems.Thm_GlobalTheory_HypChartPf_form_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
private lemma wI_injective' (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [wI] at this
  omega
end GlobalTheory.HypChartPf
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypChartPf
open PI.RhsWLim PI.RhsWLim.W
namespace GlobalTheory.HypChartPf
theorem _root_.solution (k r : ℕ) (T' : ℝ) (hT' : 0 < T') (ρ : ℝ) : opE k r T' ρ ⊆ hypS k T' := by
  rintro p ⟨q, -, rfl⟩
  have hq : star (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') ⬝ᵥ
      (Matrix.diagonal (sgn k r) *ᵥ (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) =
      star (opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ opBase k r T') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_form]
  rw [form_eq, form_eq] at hq
  have hb : ∀ i : Fin k, opBase k r T' (wI k r i.castSucc) = 0 := by
    intro i
    have hne : wI k r i.castSucc ≠ wI k r (Fin.last k) := fun h => (Fin.castSucc_lt_last i).ne (wI_injective' k r h)
    simp [opBase, wLast, bvec, hne]
  have hl : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
    simp [opBase, wLast, bvec]
  simp only [opCo, hb, hl, map_zero, Finset.sum_const_zero, Complex.normSq_ofReal,
    Real.mul_self_sqrt hT'.le] at hq
  simp only [hypS, Set.mem_ofPred_eq, opCo]
  linarith [Complex.ofReal_injective hq]
end GlobalTheory.HypChartPf
