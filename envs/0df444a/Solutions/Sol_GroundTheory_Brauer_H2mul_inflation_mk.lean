-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.inflation_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:57.215333+00:00
-- url     : https://prove2.me/submissions/d4a40d70-a5c6-473b-93b1-ebb24e511003

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_Inflation

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
universe u
open GroundTheory.Brauer.H2mul
variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]
variable {K L L'}
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    inflation K L L' (mk _ _ c) =
      mk _ _ ⟨CrossedProduct.inflate L' (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ),
        CrossedProduct.isMulCocycle₂_inflate L' c.2⟩ :=
  rfl
end GroundTheory.Brauer.H2mul
