-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.affine_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:40.572341+00:00
-- url     : https://prove2.me/submissions/4cb8c200-2566-4985-8559-71f425180fa4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_exists_eq_spMap
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
theorem _root_.solution (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, (c ≫ h) * (a ≫ h) = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨χ, hχ⟩ := H.inv S φ
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [← hφ] at hχ
  have := congrArg (inv j ≫ ·) hχ
  simp only [MonObj.comp_mul, MonObj.comp_one, Category.assoc, IsIso.inv_hom_id_assoc] at this
  simpa [Category.assoc] using this
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
