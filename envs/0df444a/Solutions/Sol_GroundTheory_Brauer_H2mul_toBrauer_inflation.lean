-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.toBrauer_inflation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:20:52.951654+00:00
-- url     : https://prove2.me/submissions/b8fe8f35-3f5b-421b-b0fe-45c6b808abb4

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
import Theorems.Thm_GroundTheory_Brauer_CrossedProduct_isBrauerEquivalent_inflate
import Theorems.Thm_GroundTheory_Brauer_H2mul_inflation_mk
import Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.H2mul.toBrauer_mk



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
theorem _root_.solution (x : H2mul (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L' (inflation K L L' x) = toBrauer K L x := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [inflation_mk, toBrauer_mk, toBrauer_mk]
  exact Quotient.sound (CrossedProduct.isBrauerEquivalent_inflate L' c.2)
end GroundTheory.Brauer.H2mul
