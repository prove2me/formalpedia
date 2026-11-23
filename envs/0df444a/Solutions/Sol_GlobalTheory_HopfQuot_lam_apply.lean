-- Prove2me | solution 1 for GlobalTheory.HopfQuot.lam_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:59.33495+00:00
-- url     : https://prove2.me/submissions/fb9f6c3d-45ca-44e1-b781-a5dd1ef89e52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (e : ι → Λ) (c : ι → Λ →ₗ[R] R) (f : Λ →ₗ[R] R) (x : Λ) :
    lam e c f x = tr e c (hit f ∘ₗ LinearMap.mulLeft R x) := by
  simp [lam, tr]
end GlobalTheory.HopfQuot
