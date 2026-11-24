-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.Cx.ex_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:25:54.505229+00:00
-- url     : https://prove2.me/submissions/3e975a17-b9ff-484f-9824-896969ef33eb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.NerveCoh
namespace Cx
theorem _root_.solution {A : Cx R} {k : ℕ} : A.Ex (k + 1) ↔ ∀ x, A.d (k + 1) x = 0 → ∃ y, A.d k y = x :=
  ⟨fun h x hx ↦ (h x).1 hx, fun h x ↦ ⟨h x, fun ⟨y, e⟩ ↦ e ▸ A.d_d k y⟩⟩
end Cx
end GlobalTheory.CompanionTheory.NerveCoh
