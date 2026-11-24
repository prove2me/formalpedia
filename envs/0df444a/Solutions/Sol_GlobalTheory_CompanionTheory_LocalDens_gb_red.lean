-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.gb_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:11.07664+00:00
-- url     : https://prove2.me/submissions/e491c317-33b9-4fb3-8ee1-2eba439828fb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gr_congr

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
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (k : ℕ)
    (x : Matrix (Fin m) (Fin n) R) : gb σ ϖ S k (red ϖ k x) = red ϖ k (gr σ S x) :=
  gr_congr hσ k S (Function.surjInv_eq _ _)
end GlobalTheory.CompanionTheory.LocalDens
