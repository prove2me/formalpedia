-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.affine_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:44.247254+00:00
-- url     : https://prove2.me/submissions/5476fbe9-f578-421e-8075-f286f1999cff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_exists_sp_iso

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
theorem _root_.solution (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] :
    ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨χ, hχ⟩ := H.one S
  exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
