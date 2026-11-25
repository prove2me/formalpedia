-- Prove2me | solution 1 for GlobalTheory.GroupGlue.MulCompat.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:40.225693+00:00
-- url     : https://prove2.me/submissions/0bea368b-fd80-4473-ad22-3ba4902b440d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_GlobalTheory_GroupGlue_exists_lift
import Theorems.Thm_GlobalTheory_GroupGlue_base_eq
import Theorems.Thm_GlobalTheory_GroupGlue_pt_ext
import Theorems.Thm_GlobalTheory_GroupGlue_MulCompat_one
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
    {i j : 𝒰.I₀} {S : Scheme.{0}} {u : S ⟶ 𝒰.X i} {v : S ⟶ 𝒰.X j} (a : Over.mk u ⟶ H i)
    (b : Over.mk v ⟶ H j) (h : a.left ≫ ψ i = b.left ≫ ψ j) : (a⁻¹).left ≫ ψ i = (b⁻¹).left ≫ ψ j := by
  have hu : u ≫ 𝒰.f i = v ≫ 𝒰.f j := by rw [base_eq hψ a, base_eq hψ b, h]
  obtain ⟨c, hc⟩ := exists_lift hψ j v ((a⁻¹).left ≫ ψ i) (hu.symm.trans (base_eq hψ a⁻¹))
  have h2 := hm i j S u v a a⁻¹ b c h hc.symm
  rw [_root_.mul_inv_cancel, MulCompat.one hm hψ u v hu] at h2
  have h3 : b * c = 1 := pt_ext hψ h2.symm
  rw [← hc, ← inv_eq_of_mul_eq_one_right h3]
end MulCompat
end GlobalTheory.GroupGlue
