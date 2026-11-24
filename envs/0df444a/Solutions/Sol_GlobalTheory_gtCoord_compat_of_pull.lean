-- Prove2me | solution 1 for GlobalTheory.gtCoord_compat_of_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:00:40.405254+00:00
-- url     : https://prove2.me/submissions/32e908aa-6fb4-4ed2-9081-8f84e9a597a0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
import Theorems.Thm_GlobalTheory_LevelCompat_mono_fstG
import Theorems.Thm_P2M_GlobalTheory_LevelCompat_thickMap_O__cc5aa398615b
import Theorems.Thm_GlobalTheory_LevelCompat_corr_of_pmaps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open LevelCompat
namespace GlobalTheory
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (e : ℕ) (g₀ : GtCoord I D e G) (g₁ : GtCoord I D (e + 1) G) (g₀' : GtCoord I' D' e G') (g₁' : GtCoord I' D' (e + 1) G') (h₀ : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (h₁ : (thickObj R' I' (e + 1) G').left ⟶ (thickObj R I (e + 1) G).left), h₀ ≫ (fstG I e G).left = (fstG I' e G').left ≫ Ψ → h₁ ≫ (fstG I (e + 1) G).left = (fstG I' (e + 1) G').left ≫ Ψ → ((g₀').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ (g₀).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₀').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ D.Oφ (g₀).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₀').pG x) (D.Oφ (g₀).pG (hD.xe x)) Oinvε ((g₀').t x) ((g₀).t (hD.xe x)) h₀) → ((g₁').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ (g₁).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₁').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ D.Oφ (g₁).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₁').pG x) (D.Oφ (g₁).pG (hD.xe x)) Oinvε ((g₁').t x) ((g₁).t (hD.xe x)) h₁) → thickMap R I e G ≫ g₁.pG.left = g₀.pG.left → (∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g₁.t χ) (thickMap R I e G)) (g₀.t χ)) → thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left ∧ ∀ χ : D'.X, LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ (g₁'.t χ) (thickMap R' I' e G')) (g₀'.t χ) := by
  intro R R' _ _ _ _ φ D D' hD I I' G _ _ G' _ _ Ψ e g₀ g₁ g₀' g₁' h₀ h₁ hh₀ hh₁ ⟨p₀, H₀⟩ ⟨p₁, H₁⟩ hq ht
  have hm : thickMap R' I' e G' ≫ h₁ = h₀ ≫ thickMap R I e G := by
    have := mono_fstG I (e + 1) G
    rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hh₁, thickMap_fstG, hh₀,
      ← thickMap_fstG I' e G']
    exact (Category.assoc _ _ _).symm
  have hq' : thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left := by
    have h : (thickMapOver I' e G' ≫ g₁'.pG) ≫ hD.e.hom = g₀'.pG ≫ hD.e.hom := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · show ((thickMap R' I' e G' ≫ g₁'.pG.left) ≫ hD.e.hom.left) ≫ _ = (g₀'.pG.left ≫ hD.e.hom.left) ≫ _
        simp only [Category.assoc]
        exact (congrArg (thickMap R' I' e G' ≫ ·) p₁).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ g₁.pG.left) hm).trans ((Category.assoc _ _ _).trans
          ((congrArg (h₀ ≫ ·) hq).trans p₀.symm))))
      · exact (Over.w _).trans (Over.w _).symm
    exact congrArg (fun z => z.left) ((cancel_mono hD.e.hom).1 h)
  exact ⟨hq', fun χ => corr_of_pmaps D.P.isLB D'.P.isLB hD.w hm (H₀ χ).1 (H₁ χ).1
    (thickMap_Oφ g₀' g₁' hq' χ) (H₀ χ).2 (H₁ χ).2 (ht _)⟩
end GlobalTheory
