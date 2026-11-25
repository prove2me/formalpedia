-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:45.089816+00:00
-- url     : https://prove2.me/submissions/254bbed3-547a-49c2-8fb4-1b9adcb3e804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_inv_real_smul_of_posDef


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
theorem _root_.solution {g : X → ℝ} (hg : IsLogBoundedScalar S w U g) (hG : IsLogBounded S w U G) :
    IsLogBounded S w U fun x => g x • G x :=
  isLogBounded_iff_entries.2 ⟨fun _ hx hB => (hG.posDef hx hB).smul (hg.pos hx hB),
    fun i j => hg.hasLogGrowth.smul (hG.hasLogGrowthEntries i j),
    HasLogGrowthEntries.congr (A := fun x => (g x)⁻¹ • (G x)⁻¹)
      (fun i j => hg.hasLogGrowth_inv.smul (hG.hasLogGrowthEntries_inv i j))
      fun _ hx hB => inv_real_smul_of_posDef (hG.posDef hx hB) (hg.pos hx hB).ne'⟩
end GlobalTheory.IsLogBounded
