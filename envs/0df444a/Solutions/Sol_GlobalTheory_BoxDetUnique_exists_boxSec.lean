-- Prove2me | solution 1 for GlobalTheory.BoxDetUnique.exists_boxSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:59.187843+00:00
-- url     : https://prove2.me/submissions/2c029da9-f1f0-4df4-bde9-721000d767c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetKroneckerPower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec
import Theorems.Thm_P2M_GlobalTheory_BoxDetUnique_gs_sum__a1ab71d3ee53
import Theorems.Thm_P2M_GlobalTheory_BoxDetUnique_gs_prod__25b0602167a4
import Theorems.Thm_GlobalTheory_BoxDetUnique_gs_cst
import Theorems.Thm_GlobalTheory_BoxDetUnique_gs_sec_pw

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]
namespace GlobalTheory.BoxDetUnique
theorem _root_.solution {L : LB X} {m : ℤ} {N I : Type} [Fintype N] [Fintype I] (φ : N → (Y ⟶ X)) (p : Y ⟶ Sp R)
    (q : I → R) (s : I → N → LB.Sec (pw L m)) : ∃ S : LB.Sec (LB.LinComb L φ (fun _ => m)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (S.f j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
  obtain ⟨F, hF⟩ : ∃ F : ∀ j : N → L.ι, Γ(Y, LB.wchart L φ j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : N → L.ι), r z ∈ LB.wchart L φ j →
        gs r z (LB.wchart L φ j) (F j) =
          ∑ a, kv (r ≫ p) z (q a) * ∏ c, gs (r ≫ φ c) z (L.U (j c)) ((s a c).f (j c)) := by
    refine ⟨fun j => ∑ a, cst p _ (q a) * ∏ c, rs Y (LB.wchart_le L φ j c) (((φ c).app (L.U (j c))).hom ((s a c).f (j c))),
      fun Z r z j h => ?_⟩
    rw [gs_sum' r z _ h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gs_mul r z _ h, gs_cst p r z _ h, gs_prod' r z _ h]
    refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
    exact (gs_res r z _ h _).trans (gs_pull r (φ c) z _ (LB.wchart_le L φ j c h) _)
  refine ⟨⟨F, fun j j' => fn_ext fun y hy => ?_⟩, hF⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hF _ (𝟙 Y) y j hy.1).trans (Eq.trans ?_ (congrArg _ (hF _ (𝟙 Y) y j' hy.2)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_left_comm, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun c _ => ?_)
  exact gs_sec_pw _ _ y _ _ (LB.wchart_le L φ j c hy.1) (LB.wchart_le L φ j' c hy.2)
end GlobalTheory.BoxDetUnique
