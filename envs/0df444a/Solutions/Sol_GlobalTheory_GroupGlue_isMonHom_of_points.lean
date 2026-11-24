-- Prove2me | solution 1 for GlobalTheory.GroupGlue.isMonHom_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:31.446205+00:00
-- url     : https://prove2.me/submissions/0fb696df-1d99-4bc6-92e0-0da94d21a24a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
variable [GrpObj G]
namespace GlobalTheory.GroupGlue
theorem _root_.solution {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ⟶ B)
    (mul : ∀ (T : Over S) (x y : T ⟶ A), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  refine ⟨?_, ?_⟩
  · have h1 := mul (𝟙_ _) 1 1
    rw [_root_.mul_one, eq_comm, _root_.mul_eq_left] at h1
    simp only [MonObj.one_eq_one]
    exact h1
  · have h2 := mul (A ⊗ A) (fst A A) (snd A A)
    rw [← MonObj.mul_eq_mul] at h2
    rw [h2, Hom.mul_def]
    congr 1
end GlobalTheory.GroupGlue
