-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.cT_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:06.54054+00:00
-- url     : https://prove2.me/submissions/ed4b1b7c-3c85-4f9a-a148-37fbf5748e09

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
theorem _root_.solution (σ : R →+* R) {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  ext i j; simp [cT, Matrix.one_apply, eq_comm]
end GlobalTheory.CompanionTheory.LocalDens
