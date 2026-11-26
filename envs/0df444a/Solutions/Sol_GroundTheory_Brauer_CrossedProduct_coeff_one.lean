-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:23.428186+00:00
-- url     : https://prove2.me/submissions/ccec0b84-0b0d-40de-a8ea-74062e2d1781

import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
open GroundTheory.Brauer.CrossedProduct
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable {hf : IsMulCocycle₂ f}
theorem _root_.solution :
    (1 : CrossedProduct hf).coeff = Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_16_1"

end 
