-- Prove2me | solution 1 for GlobalTheory.PMon.homUnit_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:59:35.838799+00:00
-- url     : https://prove2.me/submissions/18866742-95c7-43c4-9ed6-36402f194bcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KroneckerTransposeMulVec
import Theorems.Thm_GlobalTheory_PMon_kronecker_transpose_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.PMon
variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.PMon
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) (A : GL a R) (B : GL b R) (X : Matrix a b S) :
    (((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R).map f).mulVec (vecM X) =
      vecM ((A : Matrix a a R).map f * X * ((B⁻¹ : GL b R) : Matrix b b R).map f) := by
  rw [homUnit_val, ← kronecker_transpose_mulVec]
  congr 1
  ext p q
  simp [Matrix.kroneckerMap_apply]
end GlobalTheory.PMon
