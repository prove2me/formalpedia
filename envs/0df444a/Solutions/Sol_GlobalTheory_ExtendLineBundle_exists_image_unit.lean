-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_image_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:28.195803+00:00
-- url     : https://prove2.me/submissions/deb3b8b9-bf23-436e-8efe-1e336d3b2da4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {V : Y.Opens} {t : X.functionFieldˣ}
    (ht : ∀ y ∈ V, t ∈ localUnits (j y)) :
    ∃ a : Γ(Y, V)ˣ, genericPoint X ∈ j ''ᵁ V → imageVal j V a = t := by
  obtain ⟨a, ha⟩ := exists_unit (U := j ''ᵁ V) (t := t) (by
    rintro _ ⟨y, hy, rfl⟩
    exact ht y hy)
  refine ⟨(imageUnit j V).symm a, fun h => ?_⟩
  rw [← ha h]
  exact congrArg (unitVal _) ((imageUnit j V).apply_symm_apply a)
end GlobalTheory.ExtendLineBundle
