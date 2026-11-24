-- Prove2me | solution 1 for GlobalTheory.UTrans.IsoBasis.hfL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:34.459902+00:00
-- url     : https://prove2.me/submissions/f5f78c0f-cc44-4de1-bd40-d822eef92108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors

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
theorem _root_.solution (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    hfL σ G y x = hf σ G x y := rfl
end GlobalTheory.UTrans.IsoBasis
