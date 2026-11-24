-- Prove2me | solution 1 for GlobalTheory.SS.GI.exists_mem_sp_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:00.606101+00:00
-- url     : https://prove2.me/submissions/268ce41d-029a-41d4-adac-87f0ed5c7c11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
import Theorems.Thm_GlobalTheory_SS_GI_Via_mem_sp

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
variable [IsLocalRing R]
namespace GlobalTheory.SS.GI
theorem _root_.solution {M : Model R A} {N : Model R A'} {x : M.Y.left} {y : N.Y.left}
    (hx : x ∈ M.sp) (hy : y ∈ N.sp) :
    ∃ z ∈ (M.prod N).sp, (fst M.Y N.Y).left z = x ∧ (snd M.Y N.Y).left z = y := by
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := M.Y.hom) (g := N.Y.hom) x y
    (hx.trans hy.symm)
  refine ⟨z, ?_, h1, h2⟩
  exact ((via_fst M N (𝟙 _)).mem_sp z).1 (by
    rw [Category.id_comp]
    exact h1.symm ▸ hx)
end GlobalTheory.SS.GI
