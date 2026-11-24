-- Prove2me | solution 1 for GlobalTheory.TwistTranslate.gen_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:09:27.518841+00:00
-- url     : https://prove2.me/submissions/28eb2589-d862-4e14-b908-73de1c6a0684

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
import Theorems.Thm_GlobalTheory_TwistTranslate_gen_of_pull_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_spec_pt_eq


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)
namespace GlobalTheory.TwistTranslate
theorem _root_.solution (hsq : ∀ (x y : Over.mk t ⟶ P.A) (p : (Over.mk t).left), ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
        (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull
          ((fst (Over.mk t) P.A).left ⁻¹ᵁ V).ι), c.IsGen)
    (x y : Over.mk t ⟶ P.A) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd (Over.mk t) P.A).left,
      (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]), w.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hsq x y (IsLocalRing.closedPoint K)
  refine gen_of_pull_top P.isLB _ (fun z => ?_) c hc
  show (fst (Over.mk t) P.A).left z ∈ V
  rw [spec_pt_eq ((fst (Over.mk t) P.A).left z) (IsLocalRing.closedPoint K)]
  exact hpV
end GlobalTheory.TwistTranslate
