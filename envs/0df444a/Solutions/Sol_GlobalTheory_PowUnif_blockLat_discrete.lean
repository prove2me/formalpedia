-- Prove2me | solution 1 for GlobalTheory.PowUnif.blockLat_discrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:55.246806+00:00
-- url     : https://prove2.me/submissions/92e248a9-b88e-49f3-81cb-1a3eca9ee995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_IsHolFamily_comp
import Theorems.Thm_GlobalTheory_PowUnif_sum_blockIn_blockPr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PowUnif
variable {j g n : ℕ} (e : Fin j × Fin g ≃ Fin n)
namespace GlobalTheory.PowUnif
theorem _root_.solution (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] : DiscreteTopology (blockLat e Λ) := by
  refine DiscreteTopology.of_continuous_injective (β := Fin j → Λ)
    (f := fun z i => ⟨blockPr e i z.1, z.2 i⟩)
    (continuous_pi fun i => ((blockPr e i).continuous.comp continuous_subtype_val).subtype_mk _) fun z z' h => ?_
  refine Subtype.ext ?_
  rw [← sum_blockIn_blockPr e z.1, ← sum_blockIn_blockPr e z'.1]
  exact Finset.sum_congr rfl fun i _ => congrArg _ (congrArg Subtype.val (congrFun h i))
end GlobalTheory.PowUnif
