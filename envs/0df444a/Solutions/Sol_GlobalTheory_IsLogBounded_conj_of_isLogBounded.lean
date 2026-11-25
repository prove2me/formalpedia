-- Prove2me | solution 1 for GlobalTheory.IsLogBounded.conj_of_isLogBounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:40.925284+00:00
-- url     : https://prove2.me/submissions/7b829429-62cd-4241-964f-f35efb294b06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_isLogBounded_iff_exists_scalar
import Theorems.Thm_GlobalTheory_IsLogBounded_of_le_of_le
import Theorems.Thm_GlobalTheory_IsLogBounded_smul
import Theorems.Thm_GlobalTheory_conjTranspose_mul_mul_le_of_le


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
variable [Fintype m]
namespace GlobalTheory.IsLogBounded
theorem _root_.solution (hG : IsLogBounded S w U G) {A : X → Matrix n m ℂ}
    (hA : IsLogBounded S w U fun x => (A x)ᴴ * A x) :
    IsLogBounded S w U fun x => (A x)ᴴ * G x * A x := by
  obtain ⟨g, hg, h⟩ := isLogBounded_iff_exists_scalar.1 hG
  refine (hA.smul hg.inv).of_le_of_le (hA.smul hg) fun x hx hB => ⟨?_, ?_⟩
  · simpa using conjTranspose_mul_mul_le_of_le (h x hx hB).1 (A x)
  · simpa using conjTranspose_mul_mul_le_of_le (h x hx hB).2 (A x)
end GlobalTheory.IsLogBounded
