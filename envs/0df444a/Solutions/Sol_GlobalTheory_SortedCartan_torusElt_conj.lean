-- Prove2me | solution 1 for GlobalTheory.SortedCartan.torusElt_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:06.655603+00:00
-- url     : https://prove2.me/submissions/8d9f3601-7680-42ab-9908-01bc3178f468

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
import Theorems.Thm_GlobalTheory_SortedCartan_conj_torusElt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
open GlobalTheory GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SortedCartan
theorem _root_.solution {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    torusElt k (Fin N) ϖ m = (permUnit σ)⁻¹ * torusElt k (Fin N) ϖ (m ∘ σ) * permUnit σ := by
  rw [← conj_torusElt ϖ m σ]
  group
end GlobalTheory.SortedCartan
