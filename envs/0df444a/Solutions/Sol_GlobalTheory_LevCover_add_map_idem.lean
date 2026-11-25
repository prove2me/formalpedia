-- Prove2me | solution 1 for GlobalTheory.LevCover.add_map_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:22:37.885803+00:00
-- url     : https://prove2.me/submissions/d81a41a7-7bc0-4569-86fc-65de56601d58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsInducedLocus

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
variable {l : Level H}
namespace GlobalTheory.LevCover
theorem _root_.solution {Q : Type} [Group Q] {l₂ : Level H} {e : 𝓞 E} (he' : 1 - e ∈ l₂.Mb) {f : D.La → Q}
    (hf : ∀ a c, f (a + c) = f a * f c) (hk : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), f a = 1) (a : D.La) :
    f (e • a) = f a := by
  have : a = e • a + (1 - e) • a := by rw [← add_smul, add_sub_cancel, one_smul]
  conv_rhs => rw [this, hf, hk _ (Submodule.smul_mem_smul he' Submodule.mem_top), _root_.mul_one]
end GlobalTheory.LevCover
