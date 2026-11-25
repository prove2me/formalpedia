-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.sol_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:15.358513+00:00
-- url     : https://prove2.me/submissions/420120c4-f705-4540-b138-535bcdb2f66c

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
theorem _root_.solution (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    {T₁ T₂ : Matrix (Fin n) (Fin n) R} (k : ℕ) (h : red ϖ k T₁ = red ϖ k T₂) :
    sol σ ϖ S T₁ k = sol σ ϖ S T₂ k := by
  simp only [sol, h]
end GlobalTheory.CompanionTheory.LocalDens
