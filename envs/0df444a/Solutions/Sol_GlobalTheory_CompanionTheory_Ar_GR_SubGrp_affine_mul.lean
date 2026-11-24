-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.GR.SubGrp.affine_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:43.250867+00:00
-- url     : https://prove2.me/submissions/05355dc5-2209-48e7-8034-e2fa4c0296c5

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
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  obtain ⟨χ, hχ⟩ := H.mul S φ φ'
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [Category.assoc, hχ, ← hφ, ← hφ', MonObj.comp_mul, Category.assoc, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
