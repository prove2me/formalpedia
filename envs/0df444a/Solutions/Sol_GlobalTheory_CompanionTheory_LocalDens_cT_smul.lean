-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.cT_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:36.614917+00:00
-- url     : https://prove2.me/submissions/f5f4fd77-37ac-4c3a-91e0-03bee3949dc3

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
theorem _root_.solution (σ : R →+* R) {a b : ℕ} (r : R) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (r • x) = σ r • cT σ x := by
  ext i j; simp [cT]
end GlobalTheory.CompanionTheory.LocalDens
