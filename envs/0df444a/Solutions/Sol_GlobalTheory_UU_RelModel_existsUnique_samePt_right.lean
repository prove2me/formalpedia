-- Prove2me | solution 1 for GlobalTheory.UU.RelModel.existsUnique_samePt_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:05.349378+00:00
-- url     : https://prove2.me/submissions/ff50f475-9c30-4766-8337-2127f5aa1ebc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.RelModel
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UU.RelModel
theorem _root_.solution (U : PreU I D A G) (x : TFK (R := R) F ⟶ A.A) : ∃! y, U.SamePt x y := by
  refine ⟨Over.homMk (x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ?_, rfl, fun y h => Over.OverMorphism.ext h.symm⟩
  have a : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
  have b : x.left ≫ A.A.hom = jFK (R := R) F := Over.w x
  simp only [Category.assoc]
  rw [pullback.condition, ← Category.assoc U.gen.inv.left, a, ← Category.assoc, b]; rfl
end GlobalTheory.UU.RelModel
