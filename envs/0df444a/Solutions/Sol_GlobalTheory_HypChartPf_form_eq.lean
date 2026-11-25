-- Prove2me | solution 1 for GlobalTheory.HypChartPf.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:58.982827+00:00
-- url     : https://prove2.me/submissions/ef236348-d3b1-47ef-b18e-a58d7963326b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushQ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidChartMeasureFormula
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
theorem _root_.solution (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ((∑ i, Complex.normSq ((opCo k r v).1 i) - Complex.normSq (opCo k r v).2 : ℝ) : ℂ) := by
  have hs : star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ∑ j : Fin (k + 1), star (v (wI k r j)) * (sgn k r (wI k r j) * v (wI k r j)) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    symm
    refine Fintype.sum_of_injective _ (wI_injective' k r) _ (fun i => star (v i) * (sgn k r i * v i)) ?_ (fun _ => rfl)
    intro i hi
    have : sgn k r i = 0 := by
      unfold sgn
      rw [if_neg, if_neg]
      · intro h; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
      · rintro ⟨h1, h2⟩; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
    simp [this]
  have h1 : ∀ j : Fin k, sgn k r (wI k r j.castSucc) = 1 := by
    intro j; unfold sgn; rw [if_pos]; simp [wI]
  have h2 : sgn k r (wI k r (Fin.last k)) = -1 := by
    unfold sgn; rw [if_neg, if_pos] <;> simp [wI]
  rw [hs, Fin.sum_univ_castSucc, h2]
  simp only [h1, opCo]
  push_cast
  simp [Complex.normSq_eq_conj_mul_self, sub_eq_add_neg]
end GlobalTheory.HypChartPf
