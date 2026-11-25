-- Prove2me | solution 1 for GlobalTheory.FamPull.famFE_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:59.089857+00:00
-- url     : https://prove2.me/submissions/ac42de17-663a-4b95-a630-eb409aca0f54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_GlobalTheory_FamPull_val_feUnit
import Theorems.Thm_GlobalTheory_FamPull_comp_trF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
noncomputable section
open GlobalTheory
open GlobalTheory.FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamPull
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)))
    (f : ∀ α, D.SecB k α) (hs : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s α) (D.famφB α)
      (DegPre.famε k) (f α) (DegPre.prB D F).left 1) :
    DegPre.FamFE D F k s ↔ ∀ (mu α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
      Good D.P.L z J → sval (f (α + k • mu)) (ρ ≫ DegPre.prB D F).left z J =
        sval (f α) ((ρ ≫ DegPre.prB D F) * cP D T mu).left z J *
          (feUnit D k mu α (ρ ≫ DegPre.prB D F) z J
            (fun χ => val (D.psi χ) ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)
            (val D.rigK ((ρ ≫ fst _ _).left ≫ jFK (R := R) F) z J)).val := by
  constructor
  · intro H mu α T ρ z J hJ
    obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu α
    have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (H mu α u hu hc) _ ρ.left z J hJ
    rw [hv u hu hc T ρ z J hJ, val_feUnit k mu α ρ hJ, ← secScal_sval (hs _) _ z hJ, ← secScal_sval (hs _) _ z hJ,
      comp_trF] at e
    exact e
  · intro H mu α u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have e := H mu α _ (𝟙 _) y J hJ
    rw [← val_feUnit k mu α _ hJ, ← (gen_fe (D := D) (F := F) hG k mu α).2 u hu hc _ (𝟙 _) y J hJ, ← comp_trF,
      secScal_sval (hs _) _ y hJ, Over.comp_left, secScal_sval (hs _) _ y hJ] at e
    exact e
end GlobalTheory.FamPull
