-- Prove2me | solution 1 for GlobalTheory.JR.SuppBdd.Bm_actU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:32.678639+00:00
-- url     : https://prove2.me/submissions/99d0ba5e-8579-4d65-864a-8867643bbb1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
import Theorems.Thm_GlobalTheory_JR_SuppBdd_pow_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SuppBdd
namespace GlobalTheory.JR.SuppBdd
theorem _root_.solution {n : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g : Matrix.unitaryGroup (Fin n) E) (Y : Hn n F E) :
    Bm (actU g Y).toGl = g.1 * Bm Y.toGl := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  ext i j
  have h1 : ((g.1 * Y.1.1 * star g.1) ^ (j : ℕ)) *ᵥ (g.1 *ᵥ Y.2.1) = g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1) := by
    rw [pow_conj, mulVec_mulVec, mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc, hg, Matrix.mul_one]
  have h2 : Bm (actU g Y).toGl i j = (g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1)) i := by
    rw [← h1]; rfl
  rw [h2, Matrix.mul_apply]
  simp only [mulVec, dotProduct, Bm, Hn.toGl, of_apply]
end GlobalTheory.JR.SuppBdd
