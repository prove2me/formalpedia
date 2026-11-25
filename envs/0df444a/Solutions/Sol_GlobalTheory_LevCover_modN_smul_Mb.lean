-- Prove2me | solution 1 for GlobalTheory.LevCover.modN_smul_Mb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:25.001305+00:00
-- url     : https://prove2.me/submissions/5ab63c95-e15f-407a-9581-7b3635584a42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsObjTwistBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsoDifferBySimilitude
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCoprimeZpow
import Theorems.Thm_GlobalTheory_LevCover_modN_of_mem_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.LevCover
theorem _root_.solution (l : Level H) {c : 𝓞 E} (hc : c ∈ Mc l) {a : D.La}
    (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • a) := by
  apply modN_of_mem_span
  have h1 : c • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • l.Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hc ha
  rwa [← Submodule.mul_smul, mul_comm, l.prod] at h1
end GlobalTheory.LevCover
