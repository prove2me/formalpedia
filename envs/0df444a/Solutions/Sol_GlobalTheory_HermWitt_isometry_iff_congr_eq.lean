-- Prove2me | solution 1 for GlobalTheory.HermWitt.isometry_iff_congr_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:43.532704+00:00
-- url     : https://prove2.me/submissions/d6babcfd-17cf-4f08-844e-0045e064ed98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_dotProduct_congr_mulVec
import Theorems.Thm_P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution (c : E →+* E) (G P : Matrix n n E) :
    (∀ x y, (P *ᵥ x) ⬝ᵥ G *ᵥ (c ∘ (P *ᵥ y)) = x ⬝ᵥ G *ᵥ (c ∘ y)) ↔ Pᵀ * G * P.map c = G := by
  constructor
  · intro h
    apply (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c).injective
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [toLinearMapₛₗ₂'_eq_dotProduct, toLinearMapₛₗ₂'_eq_dotProduct, dotProduct_congr_mulVec, h]
  · intro h x y
    rw [← dotProduct_congr_mulVec, h]
end GlobalTheory.HermWitt
