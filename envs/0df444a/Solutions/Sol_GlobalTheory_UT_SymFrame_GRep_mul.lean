-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.GRep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:57.17914+00:00
-- url     : https://prove2.me/submissions/d137a5f7-0473-42a7-a604-03d1c0a6d767

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UT.SymFrame
namespace GRep
theorem _root_.solution {P P' v v'} (h : GRep L Y P v) (h' : GRep L Y P' v') :
    GRep L Y (fun U _ h => P U h * P' U h) (fun T r z J => v T r z J * v' T r z J) := by
  obtain ⟨K, _, φ, ε, s, hs, hP, hv⟩ := h
  obtain ⟨K', _, φ', ε', s', hs', hP', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ s s', mulGen_isGen _ _ _ _ _ _ _ hs hs',
    fun U _ h => ?_, fun T r z J hJ => ?_⟩
  · exact prod_sum₂ _ (hP U h) (hP' U h)
  · rw [val_mul hJ, hv T r z J hJ, hv' T r z J hJ]
end GRep
end GlobalTheory.UT.SymFrame
