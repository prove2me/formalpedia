-- Prove2me | solution 1 for GlobalTheory.LocFlat.isClosedEmbedding_freeMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:25.097662+00:00
-- url     : https://prove2.me/submissions/4e6fe93f-d537-48bc-a02a-89e18516b6f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_LocFlat_freeMat_apply_free
import Theorems.Thm_GlobalTheory_LocFlat_continuous_freeMat
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


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
namespace GlobalTheory.LocFlat
theorem _root_.solution (p : ℕ) :
    Topology.IsClosedEmbedding (freeMat (k := k) (n := n) (n' := n') (c := c) p) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine Function.LeftInverse.isClosedEmbedding
    (f := fun z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
      fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} => z rs.1.1 rs.1.2)
    (fun e => funext fun rs => freeMat_apply_free p e rs) ?_ (continuous_freeMat p)
  exact continuous_pi fun rs => continuous_id.matrix_elem _ _
end GlobalTheory.LocFlat
