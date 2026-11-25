-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.Rep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:55.168422+00:00
-- url     : https://prove2.me/submissions/4b67e7ad-103b-43f0-b36c-6f3256a312eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {X Y Y' : Scheme.{0}} {L : LB X}
namespace GlobalTheory.GeneratorLaw
namespace Rep
theorem _root_.solution {σ σ' : Form Y X} {F F' : Vals L Y} (h : Rep L σ F) (h' : Rep L σ' F') :
    Rep L (fun V _ k => σ V k * σ' V k) (fun Z r z J => F Z r z J * F' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hs', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun V _ k => ?_, fun Z r z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs V k) (hs' V k)
  · rw [val_mul hJ, hv _ _ _ _ hJ, hv' _ _ _ _ hJ]
end Rep
end GlobalTheory.GeneratorLaw
