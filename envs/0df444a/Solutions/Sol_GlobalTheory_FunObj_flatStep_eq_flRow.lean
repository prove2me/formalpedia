-- Prove2me | solution 1 for GlobalTheory.FunObj.flatStep_eq_flRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:52.548856+00:00
-- url     : https://prove2.me/submissions/6e0fe043-4e1d-4192-9f33-f505809fd755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_keptPt_eq_rowAt

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
theorem _root_.solution (hc : Odd c) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (w : KeptVar n c n' → k) :
    flatStep ψ ν Φ x₀ w = flRow ψ ν (c / 2 + 1) Φ (fromRows x₀ (Matrix.of fun _ s => w (rowIx hc s))) := by
  simp only [flatStep, flRow, keptPt_eq_rowAt hc, toRows₁_fromRows]
  rfl
end GlobalTheory.FunObj
