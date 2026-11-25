-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.toBrauer_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:12.540727+00:00
-- url     : https://prove2.me/submissions/4baa13c6-de00-47ad-a863-4e76a9a21774

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj

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
open GroundTheory.Brauer.H2mul
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {K L}
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L (mk _ _ c) = ⟦csaOf K (CrossedProduct (isMulCocycle₂_of_mem c))⟧ := rfl
end GroundTheory.Brauer.H2mul
