-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_pair_eq_contr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:47.847866+00:00
-- url     : https://prove2.me/submissions/a6390f5f-f4b3-471b-85d3-0dc320981617

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_integrable_col
import Theorems.Thm_GlobalTheory_FunObj_integrable_row
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
  {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.FunObj
theorem _root_.solution (hψ : Continuous ψ) {Ψ₁ : Matrix n (n' ⊕ Unit) k → ℂ} {Ψ₂ : Matrix (n'' ⊕ Unit) n k → ℂ}
    (h₁ : Ψ₁ ∈ SB _) (h₂ : Ψ₂ ∈ SB _) (x₁ : Matrix n n' k) (x₂ : Matrix n'' n k) :
    ∫ p : (n → k) × (n → k), Ψ₁ (fromCols x₁ (Matrix.of fun r _ => p.1 r)) * Ψ₂ (fromRows x₂ (Matrix.of fun _ => p.2)) *
      (ψ (-∑ r, p.2 r * p.1 r) : ℂ) ∂((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) =
      contr ψ ν Ψ₁ Ψ₂ (x₁, x₂) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : Continuous fun p : (n → k) × (n → k) => (ψ (-∑ r, p.2 r * p.1 r) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (by fun_prop))
  have hI := ((integrable_col ν h₁ x₁).mul_prod (integrable_row ν h₂ x₂)).mul_bdd (c := 1) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (Circle.norm_coe _).le)
  rw [integral_prod_symm _ hI, contr]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [GlobalTheory.StepData.hat, ← integral_const_mul, neg_mul, one_mul, dotProduct]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring
end GlobalTheory.FunObj
