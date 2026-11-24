-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_last_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:39.494046+00:00
-- url     : https://prove2.me/submissions/b6bceee4-3247-43d7-a198-1f2d5a700be4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_flatStep_eq_flCol
import Theorems.Thm_GlobalTheory_FunObj_measurePreserving_comp_equiv
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
open Classical
namespace GlobalTheory.FunObj
theorem _root_.solution {c : ℕ} (hc : Even c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k)
    (z : n → k) :
    ∫ w : KeptVar n c n' → k, flatStep ψ ν Φ x w * (ψ (-∑ r, z r * w (colIx hc r)) : ℂ) ∂(Measure.pi fun _ => ν) =
      GlobalTheory.StepData.hat ψ ν (-1) (fun u => flCol ψ ν (c / 2 + 1) Φ (fromCols x (Matrix.of fun r _ => u r))) z := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [GlobalTheory.StepData.hat, ← (measurePreserving_comp_equiv ν (colEquiv (n := n) (n' := n') hc)).integral_comp']
  simp only [flatStep_eq_flCol ψ ν hc, neg_mul, one_mul, dotProduct]
  rfl
end GlobalTheory.FunObj
