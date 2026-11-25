-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_comm_of_weilIs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:19.505829+00:00
-- url     : https://prove2.me/submissions/6660c915-8b97-428d-9b77-5db8640b967b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_exists_theta_pull
import Theorems.Thm_GlobalTheory_ThetaScalar_commIsOf_val
import Theorems.Thm_GlobalTheory_ThetaScalar_translT_comp
import Theorems.Thm_P2M_GlobalTheory_ThetaScalar_exists_section_overRes__e8dc21895a9a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (hL : L.IsLB) (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤)
    (θx : ThetaGrp A L k T) {y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k θx.pt y c) :
    ∃ θy : ThetaGrp A L k T, θy.pt = y ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J, Good L z J →
      thetaVal θx r z J * thetaVal θy (r ≫ (translT A θx.pt).left) z J =
        thetaVal θy r z J * thetaVal θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c := by
  obtain ⟨V, hV, ⟨-, θy, -, hy⟩, hc⟩ := h p
  obtain rfl := hp V hV
  obtain ⟨e, he⟩ := exists_section_overResι T
  obtain ⟨θy', hθy, vy⟩ := exists_theta_pull hL e θy
  obtain ⟨θx', hθx, vx⟩ := exists_theta_pull hL (overResι ⊤) θx
  have back : (e ▷ A).left ≫ (overResι ⊤ ▷ A).left = 𝟙 _ := by
    rw [← Over.comp_left, ← comp_whiskerRight, he, id_whiskerRight, Over.id_left]
  have ex : e ≫ θx'.pt = θx.pt := by rw [hθx, ← Category.assoc, he, Category.id_comp]
  refine ⟨θy', by rw [hθy, hy, ← Category.assoc, he, Category.id_comp], fun Z r z J hJ => ?_⟩
  have H := commIsOf_val (hc θx' θy hθx hy) (r ≫ (e ▷ A).left) z hJ
  have t₁ : (r ≫ (e ▷ A).left) ≫ (translT A θx'.pt).left = (r ≫ (translT A θx.pt).left) ≫ (e ▷ A).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, ← translT_comp, ex]
  have t₂ : (r ≫ (e ▷ A).left) ≫ (translT A θy.pt).left = (r ≫ (translT A θy'.pt).left) ≫ (e ▷ A).left := by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, ← translT_comp, hθy]
  have t₃ : gm ((r ≫ (e ▷ A).left) ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (unitRes ⊤ c) =
      gm (r ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull _ (overResι (T := T) ⊤).left z ⊤ trivial c).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst_assoc, he,
      Category.comp_id]
  rw [t₁, t₂, t₃, vx _ _ z J hJ, vx _ _ z J hJ, ← vy _ _ z J hJ, ← vy _ _ z J hJ, Category.assoc, Category.assoc _ _
    (overResι ⊤ ▷ A).left, back, Category.comp_id, Category.comp_id] at H
  exact H
end GlobalTheory.ThetaScalar
