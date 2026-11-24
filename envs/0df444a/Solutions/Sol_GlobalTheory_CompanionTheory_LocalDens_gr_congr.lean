-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.gr_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:38.794037+00:00
-- url     : https://prove2.me/submissions/56171c52-263f-41e1-ae9f-8a703c72a807

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_cT_congr

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
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) (k : ℕ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    {x y : Matrix (Fin m) (Fin n) R} (h : red ϖ k x = red ϖ k y) :
    red ϖ k (gr σ S x) = red ϖ k (gr σ S y) := by
  rw [gr, gr, red_mul, red_mul, red_mul, red_mul, red_cT_congr hσ k h, h]
end GlobalTheory.CompanionTheory.LocalDens
