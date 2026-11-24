-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.gr_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:41.98779+00:00
-- url     : https://prove2.me/submissions/8be95eac-aa20-4fa3-a561-c494bf32cbcc

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
theorem _root_.solution {σ : R →+* R} (hinv : ∀ a, σ (σ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) R}
    (hS : cT σ S = S) (x : Matrix (Fin m) (Fin n) R) : cT σ (gr σ S x) = gr σ S x := by
  have : cT σ (cT σ x) = x := by ext i j; simp [cT, hinv]
  rw [gr, cT_mul, cT_mul, this, hS, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.LocalDens
