-- Prove2me | solution 1 for GlobalTheory.FunObj.integrable_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:09.869259+00:00
-- url     : https://prove2.me/submissions/dba4fc55-6c98-4576-bec1-90b9ff0962f0

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
omit [DecidableEq n] [DecidableEq n'']
namespace GlobalTheory.FunObj
theorem _root_.solution {Ψ : Matrix (n'' ⊕ Unit) n k → ℂ} (hΨ : Ψ ∈ SB _) (x : Matrix n'' n k) :
    Integrable (fun u : n → k => Ψ (fromRows x (Matrix.of fun _ => u))) (Measure.pi fun _ => ν) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have h : Topology.IsClosedEmbedding fun u : n → k => fromRows x (Matrix.of fun (_ : Unit) => u) := by
    refine Function.LeftInverse.isClosedEmbedding (f := fun z => z (.inr ())) (fun y => rfl)
      (continuous_pi fun r => continuous_id.matrix_elem _ _) (continuous_matrix fun r s => ?_)
    rcases r with r | r
    · exact continuous_const
    · exact continuous_apply s
  exact (hΨ.1.continuous.comp h.continuous).integrable_of_hasCompactSupport (hΨ.2.comp_isClosedEmbedding h)
end GlobalTheory.FunObj
