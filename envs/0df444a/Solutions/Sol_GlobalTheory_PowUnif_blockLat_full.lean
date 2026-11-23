-- Prove2me | solution 1 for GlobalTheory.PowUnif.blockLat_full
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:56.458409+00:00
-- url     : https://prove2.me/submissions/fcb7b726-64a3-42a2-a10d-e255132ef966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Theorems.Thm_GlobalTheory_PowUnif_blockPr_blockIn
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
theorem _root_.solution (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    Submodule.span ℝ (blockLat e Λ : Set (Fin n → ℂ)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  rw [← sum_blockIn_blockPr e z]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hz : blockPr e i z ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
  generalize blockPr e i z = a at hz
  induction hz using Submodule.span_induction with
  | mem a ha =>
    refine Submodule.subset_span fun i' => ?_
    rw [blockPr_blockIn]
    split_ifs
    exacts [ha, Λ.zero_mem]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [ContinuousLinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ r ha
end GlobalTheory.PowUnif
