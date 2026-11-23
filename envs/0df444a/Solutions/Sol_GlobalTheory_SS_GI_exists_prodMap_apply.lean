-- Prove2me | solution 1 for GlobalTheory.SS.GI.exists_prodMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:11.89784+00:00
-- url     : https://prove2.me/submissions/12dffa75-fda1-4ace-96a8-f35c187452d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
namespace GlobalTheory.SS.GI
theorem _root_.solution {M : Model R A} {N : Model R A'} {W W' : Scheme.{0}}
    (u : W ⟶ M.Y.left) (u' : W' ⟶ N.Y.left) [IsOpenImmersion u] [IsOpenImmersion u'] (z : (M.prod N).Y.left)
    (w : W) (w' : W') (e : u w = (fst M.Y N.Y).left z) (e' : u' w' = (snd M.Y N.Y).left z) :
    ∃ t, prodMap M N _ _ u u' rfl rfl t = z := by
  have := Scheme.Pullback.range_map (u ≫ M.Y.hom) (u' ≫ N.Y.hom) M.Y.hom N.Y.hom u u' (𝟙 _) (by simp) (by simp)
  exact (Set.ext_iff.1 this z).2 ⟨⟨w, e⟩, ⟨w', e'⟩⟩
end GlobalTheory.SS.GI
