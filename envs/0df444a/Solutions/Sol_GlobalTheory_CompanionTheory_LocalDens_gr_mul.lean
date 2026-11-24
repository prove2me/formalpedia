-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.gr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:43.238169+00:00
-- url     : https://prove2.me/submissions/1646bbb6-175a-48ea-9e49-b1bac23d2824

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_cT_mul

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
theorem _root_.solution (σ : R →+* R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R)
    (g : Matrix (Fin n) (Fin n) R) : gr σ S (x * g) = cT σ g * gr σ S x * g := by
  simp only [gr, cT_mul, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.LocalDens
