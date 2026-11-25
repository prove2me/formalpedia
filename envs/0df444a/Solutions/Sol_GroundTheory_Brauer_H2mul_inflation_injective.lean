-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.inflation_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:40.237677+00:00
-- url     : https://prove2.me/submissions/10af804c-f3bb-424e-a137-1259f36c0500

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
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_inflation
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_injective


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
variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution : Function.Injective (inflation K L L') := by
  intro x y h
  apply toBrauer_injective (K := K) (L := L)
  have h' := congrArg (toBrauer K L') h
  rwa [toBrauer_inflation, toBrauer_inflation] at h'
end GroundTheory.Brauer.H2mul
