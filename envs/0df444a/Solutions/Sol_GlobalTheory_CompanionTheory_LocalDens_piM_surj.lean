-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.piM_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:50.331238+00:00
-- url     : https://prove2.me/submissions/6b1f2bbc-6e44-4579-9f8b-792e3b430229

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution (ϖ : R) (k a b : ℕ) : Function.Surjective (piM ϖ k a b) := by
  intro y
  obtain ⟨x, rfl⟩ := red_surj ϖ k y
  exact ⟨red ϖ (k + 1) x, piM_red ϖ k x⟩
end GlobalTheory.CompanionTheory.LocalDens
