-- Prove2me | solution 1 for GlobalTheory.SerreField.homRing_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:53.67478+00:00
-- url     : https://prove2.me/submissions/ef8ec13a-cc60-4124-acc5-e4e590a277bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable {A}
namespace GlobalTheory.SerreField
theorem _root_.solution {f g : homRing A}
    (h : f.1 (Additive.ofMul (𝟙 A)) = g.1 (Additive.ofMul (𝟙 A))) : f = g := by
  obtain ⟨f, u, hu, hf⟩ := f
  obtain ⟨g, v, hv, hg⟩ := g
  have e : u = v := by
    simpa only [hf, hg, Category.id_comp, EmbeddingLike.apply_eq_iff_eq] using h
  subst e
  exact Subtype.ext (AddMonoidHom.ext fun x => (hf x.toMul).trans (hg x.toMul).symm)
end GlobalTheory.SerreField
