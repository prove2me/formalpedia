-- Prove2me | solution 1 for GlobalTheory.lieComb_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:40:49.088204+00:00
-- url     : https://prove2.me/submissions/1edf3754-5891-49f6-bde0-573330094001

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Theorems.Thm_GlobalTheory_LieCombBaseChange_dualMap_epsScale
import Theorems.Thm_GlobalTheory_LieCombBaseChange_dualMap_over
import Theorems.Thm_GlobalTheory_LieCombBaseChange_epsScale_over
import Theorems.Thm_GlobalTheory_LieCombBaseChange_prod_left_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory
open LieCombBaseChange
namespace GlobalTheory
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap f) φ → ∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) (a : Fin n → R) (v' : Fin n → (epsR R' ⟶ G')) (w' : epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (v j).left) → IsLieComb a v w → (w'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ↔ IsLieComb (fun i => f (a i)) v' w') := by
  intro R R' _ _ f G _ G' _ φ h n v w a v' w' hv hc
  obtain ⟨u, hu, rfl⟩ := hc

  have hcomp : ∀ i, (spMap (epsScaleR (f (a i))) ≫ (v' i).left) ≫ φ =
      spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (u i).left := by
    intro i
    rw [Category.assoc, hv i, hu i, ← Category.assoc, ← Category.assoc,
      LieCombBaseChange.dualMap_epsScale]
  have hprod : ∀ u'' : Fin n → (epsR R' ⟶ G'),
      (∀ i, (u'' i).left = spMap (epsScaleR (f (a i))) ≫ (v' i).left) →
        (List.ofFn u'').prod.left ≫ φ =
          spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (List.ofFn u).prod.left := fun u'' hu'' =>
    LieCombBaseChange.prod_left_comp h _ (LieCombBaseChange.dualMap_over f) u u''
      (fun i => by rw [hu'' i]; exact hcomp i)
  constructor
  · intro hw
    let u' : Fin n → (epsR R' ⟶ G') := fun i =>
      Over.homMk (spMap (epsScaleR (f (a i))) ≫ (v' i).left) (by
        rw [Category.assoc, Over.w]
        exact LieCombBaseChange.epsScale_over _)
    refine ⟨u', fun i => rfl, ?_⟩

    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hw, hprod u' fun i => rfl]
    · rw [Over.w w', Over.w]
  · rintro ⟨u'', hu'', rfl⟩
    exact hprod u'' hu''
end GlobalTheory
