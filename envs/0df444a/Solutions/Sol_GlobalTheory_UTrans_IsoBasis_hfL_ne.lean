-- Prove2me | solution 1 for GlobalTheory.UTrans.IsoBasis.hfL_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:08.611069+00:00
-- url     : https://prove2.me/submissions/6ca3fef8-cb3c-4e24-8ef8-3070ed428672

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
import Theorems.Thm_GlobalTheory_UTrans_IsoBasis_hfL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.IsoBasis
variable {E : Type} [Field E] {n : ℕ}
namespace GlobalTheory.UTrans.IsoBasis
theorem _root_.solution {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) {y : Fin n → E}
    (hy : y ≠ 0) : ∃ x, hfL σ G y x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hy
  have h0 : G.mulVec (fun b => σ (y b)) = 0 := by
    funext a
    have := h (Pi.single a 1)
    simpa [hfL_apply, hf, Pi.single_apply, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_irrel] using this
  have h1 := Matrix.eq_zero_of_mulVec_eq_zero hG.det_ne h0
  funext b
  have := congrFun h1 b
  simpa using this
end GlobalTheory.UTrans.IsoBasis
