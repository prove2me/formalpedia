-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.mono_of_isFinFlatSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:34:38.554029+00:00
-- url     : https://prove2.me/submissions/7a570029-0df3-4ff2-a464-3e1d181bb8cf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_affine_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.GR GlobalTheory.CompanionTheory.Ar.GR.SubGrp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
variable {R : Type} [CommRing R]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}
namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp
theorem _root_.solution (H : IsFinFlatSub A B h) : Mono h := by
  constructor
  intro T a b hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
  haveI : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have := affine_mono H (j ≫ a) (j ≫ b) (by rw [Category.assoc, Category.assoc, hab])
  exact congrArg (·.left) this
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
