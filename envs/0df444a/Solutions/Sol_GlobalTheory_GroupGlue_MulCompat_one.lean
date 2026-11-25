-- Prove2me | solution 1 for GlobalTheory.GroupGlue.MulCompat.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:06.380247+00:00
-- url     : https://prove2.me/submissions/71db35f6-148e-492e-95a1-e3b179a76e78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_exists_lift
import Theorems.Thm_GlobalTheory_GroupGlue_base_eq
import Theorems.Thm_GlobalTheory_GroupGlue_pt_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
variable [∀ i, GrpObj (H i)]
namespace GlobalTheory.GroupGlue
namespace MulCompat
theorem _root_.solution (hm : MulCompat ψ) (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i))
    {i j : 𝒰.I₀} {S : Scheme.{0}} (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (h : u ≫ 𝒰.f i = v ≫ 𝒰.f j) :
    (1 : Over.mk u ⟶ H i).left ≫ ψ i = (1 : Over.mk v ⟶ H j).left ≫ ψ j := by
  have h1 := base_eq hψ (1 : Over.mk u ⟶ H i)
  obtain ⟨b, hb⟩ := exists_lift hψ j v ((1 : Over.mk u ⟶ H i).left ≫ ψ i) (h.symm.trans h1)
  have h2 := hm i j S u v 1 1 b b hb.symm hb.symm
  rw [_root_.mul_one, ← hb] at h2
  have h3 : b * b = b := pt_ext hψ h2.symm
  rw [_root_.mul_eq_left] at h3
  rw [← hb, h3]
end MulCompat
end GlobalTheory.GroupGlue
