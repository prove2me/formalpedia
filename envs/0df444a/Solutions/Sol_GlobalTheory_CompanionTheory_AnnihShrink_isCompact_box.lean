-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnnihShrink.isCompact_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:19.970791+00:00
-- url     : https://prove2.me/submissions/e747816e-4ae9-4f38-8fac-a3bf2f18db45

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihShrink
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.AnnihShrink
theorem _root_.solution (n : ℕ) (b : k) : IsCompact (box n b : Set (Fin n → k)) := by
  have : (box n b : Set (Fin n → k)) =
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k b}) := by
    ext a
    exact ⟨fun h j _ => h j, fun h j => h j (Set.mem_univ j)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
end GlobalTheory.CompanionTheory.AnnihShrink
