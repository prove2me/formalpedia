-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.pow_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:22.055587+00:00
-- url     : https://prove2.me/submissions/b43d01f3-b9eb-4547-a3a6-bdb3f4f33eb3

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductIso
import Theorems.Thm_P2M_GroundTheory_Brauer_isMulCoboundary__pow_card_427b229fa3ef

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
open TensorProduct Module groupCohomology
universe u
open GroundTheory.Brauer.H2mul
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (x : H2mul G M) : x ^ Fintype.card G = 1 := by
  induction x using H2mul.induction_on with
  | h c =>
  rw [← map_pow, mk_eq_one_iff, SubmonoidClass.coe_pow]
  exact isMulCoboundary₂_pow_card (isMulCocycle₂_of_mem c)
end GroundTheory.Brauer.H2mul
