-- Prove2me | solution 1 for GlobalTheory.LocFlat.flRow_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:06.577159+00:00
-- url     : https://prove2.me/submissions/a75ecabf-88cc-487a-bff5-dae1c1c930aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
open Classical
namespace GlobalTheory.LocFlat
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flRow ψ ν p Φ = fun x => ∫ e, Φ (ptRow p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ)
      ∂(Measure.pi fun _ => ν) := rfl
end GlobalTheory.LocFlat
