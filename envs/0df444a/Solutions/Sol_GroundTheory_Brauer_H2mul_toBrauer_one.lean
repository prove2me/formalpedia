-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.toBrauer_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:47.944919+00:00
-- url     : https://prove2.me/submissions/4ab0dfa4-b481-41fd-a5ca-23befeab9cb4

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_eq_one_iff

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
theorem _root_.solution : toBrauer K L (1 : H2mul (L ≃ₐ[K] L) Lˣ) = 1 :=
  (toBrauer_eq_one_iff _).2 rfl
end GroundTheory.Brauer.H2mul
