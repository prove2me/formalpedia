-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.compoundMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:21.918811+00:00
-- url     : https://prove2.me/submissions/b5568315-7874-418a-bd17-5774de0a1d24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_compoundMatrix_inv
import Theorems.Thm_GlobalTheory_posDef_compoundMatrix
import Theorems.Thm_GlobalTheory_IsLogBounded_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
open GlobalTheory.IsLogBounded
namespace GlobalTheory.IsLogBounded
theorem _root_.solution {n : Type*} [Fintype n] [LinearOrder n] {G : X → Matrix n n ℂ}
    (hG : IsLogBounded S w U G) (k : ℕ) :
    IsLogBounded S w U fun x => compoundMatrix k (G x) :=
  isLogBounded_iff_entries.2 ⟨fun _ hx hB => posDef_compoundMatrix k (hG.posDef hx hB),
    fun _ _ => (hG.hasLogGrowthEntries.submatrix _ _).det,
    HasLogGrowthEntries.congr (A := fun x => GlobalTheory.compoundMatrix k (G x)⁻¹)
      (fun _ _ => (hG.hasLogGrowthEntries_inv.submatrix _ _).det)
      fun _ hx hB => compoundMatrix_inv k (hG.posDef hx hB).isUnit⟩
end GlobalTheory.IsLogBounded
