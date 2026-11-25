-- Prove2me | solution 1 for GlobalTheory.LieExt.lieMult_iff_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:37.459466+00:00
-- url     : https://prove2.me/submissions/69896507-174b-4a5f-8c35-8597c8099df4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LieMultIffFinrank
import Theorems.Thm_GlobalTheory_LieExt_lieMult_of_finrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_finrank_eig_bc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_finrank_of_lieMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanBC_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.LieExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LieExt
theorem _root_.solution {k K : Type} [Field k] [Field K] [Algebra k K] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] {n : ℕ} {xc : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)
    {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) [∀ a, IsMonHom (act.act a)] (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (fB k K) ((algebraMap k K).comp χ) N ↔
      Module.finrank k (eigLat hx act.act χ) = N := by
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := k) (R' := K) G n xc hx
  have hpt : ∀ c : Fin n → k, pushR G (tvec (x := x') (algebraMap k K ∘ c)) =
      spMap (dualMapA k K) ≫ tvec (x := xc) c := fun c =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp c]; rfl)
  have hLk : ∀ a (c : Fin n → k), tmap hx' ((Over.pullback (fB k K)).map (act.act a)) (algebraMap k K ∘ c) =
      algebraMap k K ∘ tmap hx (act.act a) c := by
    intro a c
    apply tvec_inj hx'
    apply pushR_inj G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hx, Category.assoc]
  have e0 : Module.finrank k (eigLat hx act.act χ) =
      Module.finrank K (eigLat hx' (fun a => (Over.pullback (fB k K)).map (act.act a))
        (fun a => (algebraMap k K).comp χ a)) :=
    finrank_eig_bc (fun a => tmap hx (act.act a))
      (fun a => tmap hx' ((Over.pullback (fB k K)).map (act.act a))) hLk χ
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  rw [e0]
  exact ⟨finrank_of_lieMult (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _,
    lieMult_of_finrank (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _⟩
end GlobalTheory.LieExt
