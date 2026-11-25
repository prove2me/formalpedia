-- Prove2me | solution 1 for GroundTheory.Brauer.CrossedProduct.isBrauerEquivalent_inflate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:55:51.447095+00:00
-- url     : https://prove2.me/submissions/96bd354a-d539-4601-8ba8-62088307d4ef

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
universe u
open GroundTheory.Brauer.CrossedProduct
variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']
variable (L')
namespace GroundTheory.Brauer.CrossedProduct
theorem _root_.solution {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_inflate L' hf)))
      (csaOf K (CrossedProduct hf)) := by
  have : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite K L L'
  have : Nonempty (Fin (Module.finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact isBrauerEquivalent_of_algEquiv_matrix (C := CrossedProduct hf)
    (inflateAlgEquiv (Module.finBasis L L') hf) (matrixFinOneAlgEquiv (CrossedProduct hf)).symm
end GroundTheory.Brauer.CrossedProduct
