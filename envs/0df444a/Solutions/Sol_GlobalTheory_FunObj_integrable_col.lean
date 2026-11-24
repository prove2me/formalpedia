-- Prove2me | solution 1 for GlobalTheory.FunObj.integrable_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:09.14465+00:00
-- url     : https://prove2.me/submissions/7a0b0619-4619-4b8f-aa53-1153a536ef65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
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
omit [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.FunObj
theorem _root_.solution {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB _) (x : Matrix n n' k) :
    Integrable (fun y : n → k => Ψ (fromCols x (Matrix.of fun r _ => y r))) (Measure.pi fun _ => ν) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h : Topology.IsClosedEmbedding fun y : n → k => fromCols x (Matrix.of fun r (_ : Unit) => y r) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun z r => z r (.inr ())) (fun y => rfl)
      (continuous_pi fun r => continuous_id.matrix_elem _ _) (continuous_matrix fun r s => ?_)
    rcases s with s | s
    · exact continuous_const
    · exact continuous_apply r
  exact (hΨ.1.continuous.comp h.continuous).integrable_of_hasCompactSupport (hΨ.2.comp_isClosedEmbedding h)
end GlobalTheory.FunObj
