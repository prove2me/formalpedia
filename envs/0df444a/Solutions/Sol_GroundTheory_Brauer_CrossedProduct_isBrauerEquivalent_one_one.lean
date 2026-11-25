-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.isBrauerEquivalent_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:34:10.247959+00:00
-- url     : https://prove2.me/submissions/0bd76997-70ed-4cfc-8e60-36cda8d2e4db

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Theorems.Thm_GroundTheory_Brauer_isBrauerEquivalent_of_algEquiv_matrix


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
theorem _root_.solution :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_one (K := K) (L := L))))
      (oneCSA K) := by
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact isBrauerEquivalent_of_algEquiv_matrix (C := K) (matrixEquiv isMulCocycle₂_one)
    (matrixFinOneAlgEquiv K).symm
end GroundTheory.Brauer.CrossedProduct
