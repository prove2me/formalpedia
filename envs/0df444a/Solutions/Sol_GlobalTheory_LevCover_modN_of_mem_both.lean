-- Prove2me | solution 1 for GlobalTheory.LevCover.modN_of_mem_both
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:58.942028+00:00
-- url     : https://prove2.me/submissions/f4431b8a-7e66-41e3-aea3-8a1cc34f2874

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Theorems.Thm_GlobalTheory_LevCover_exists_idem
import Theorems.Thm_GlobalTheory_LevCover_modN_smul_Mb
import Theorems.Thm_GlobalTheory_LevCover_modN_smul_Mc
import Theorems.Thm_GlobalTheory_LevelTwist_twist_ev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LevelTwist.twist_ev



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.LevCover
theorem _root_.solution (l : Level H) {a : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (ha' : a ∈ Mc l • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M a := by
  obtain ⟨e, he, he'⟩ := exists_idem l
  obtain ⟨b₁, hb₁⟩ := modN_smul_Mb l he ha
  obtain ⟨b₂, hb₂⟩ := modN_smul_Mc l he' ha'
  refine ⟨b₁ + b₂, ?_⟩
  rw [smul_add, ← hb₁, ← hb₂, ← add_smul]
  simp
end GlobalTheory.LevCover
