-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.red_cT_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:04.497073+00:00
-- url     : https://prove2.me/submissions/f446400e-c674-46d9-a31b-ec8a5f128850

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_red_eq_iff

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
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hσ : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    {x y : Matrix (Fin a) (Fin b) R} (h : red ϖ k x = red ϖ k y) :
    red ϖ k (cT σ x) = red ϖ k (cT σ y) := by
  rw [red_eq_iff] at h ⊢
  intro i j
  have := map_dvd σ (h j i)
  simpa [cT, hσ, map_sub] using this
end GlobalTheory.CompanionTheory.LocalDens
