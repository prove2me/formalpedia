-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.nonempty_algEquiv_of_isBrauerEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:12.693826+00:00
-- url     : https://prove2.me/submissions/6b9066cb-ad77-4d63-af3c-bfd9c387ba90

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_of_isBrauerEquivalent
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq


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
universe u v
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
    (hf : IsMulCocycle₂ f) (hg : IsMulCocycle₂ g)
    (h : IsBrauerEquivalent (csaOf K (CrossedProduct hf)) (csaOf K (CrossedProduct hg))) :
    Nonempty (CrossedProduct hf ≃ₐ[K] CrossedProduct hg) :=
  GroundTheory.Brauer.nonempty_algEquiv_of_isBrauerEquivalent h
    (show Module.finrank K (CrossedProduct hf) = Module.finrank K (CrossedProduct hg) by
      rw [finrank_eq_sq, finrank_eq_sq])
end GroundTheory.Brauer.CrossedProduct
