-- Prove2me | solution 1 for GlobalTheory.FunObj.flatStep_eq_flCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:48.376397+00:00
-- url     : https://prove2.me/submissions/e9e75fdc-312f-4ade-be5c-a5dbba79d9f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_keptPt_eq_colAt

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
variable {k : Type} [Field k] {n n' : Type} {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar k Circle) (ν : Measure k)
namespace GlobalTheory.FunObj
theorem _root_.solution (hc : Even c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : KeptVar n c n' → k) :
    flatStep ψ ν Φ x₀ w = flCol ψ ν (c / 2 + 1) Φ (fromCols x₀ (Matrix.of fun r _ => w (colIx hc r))) := by
  simp only [flatStep, flCol, keptPt_eq_colAt hc, toCols₁_fromCols, fromCols_apply_inr, of_apply]
end GlobalTheory.FunObj
