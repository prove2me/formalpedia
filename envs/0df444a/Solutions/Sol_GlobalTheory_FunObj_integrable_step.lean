-- Prove2me | solution 1 for GlobalTheory.FunObj.integrable_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:39.588166+00:00
-- url     : https://prove2.me/submissions/b63dc187-a223-48cd-8c95-8ce91cabeba6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_isClosedEmbedding_stepPt
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
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
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [MeasurableSpace k] [BorelSpace k]
open Classical
omit [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.FunObj
theorem _root_.solution {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure]
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _) (x₀ : Matrix n n' k) :
    Integrable (fun e : StepVar n c n' → k => Φ (stepPt x₀ e) * (ψ (-ch (stepPt x₀ e)) : ℂ)) (Measure.pi fun _ => ν) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h := isClosedEmbedding_stepPt (c := c) x₀
  refine Continuous.integrable_of_hasCompactSupport ((hΦ.1.continuous.comp h.continuous).mul
    (continuous_subtype_val.comp (hψ.comp (continuous_finset_sum _ fun i _ => h.continuous.matrix_elem _ _).neg))) ?_
  exact (hΦ.2.comp_isClosedEmbedding h).mul_right
end GlobalTheory.FunObj
