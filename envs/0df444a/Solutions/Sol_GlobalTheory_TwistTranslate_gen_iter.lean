-- Prove2me | solution 1 for GlobalTheory.TwistTranslate.gen_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:25:48.253018+00:00
-- url     : https://prove2.me/submissions/d513650a-4156-4361-a01b-fea4a6659a28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
import Theorems.Thm_GlobalTheory_TwistTranslate_gen_congr
import Theorems.Thm_GlobalTheory_TwistTranslate_gen_mul
import Theorems.Thm_GlobalTheory_TwistTranslate_gen_square
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add


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
    (d : Over.mk t ⟶ P.A) :
    ∀ n : ℕ, ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 3) ![(snd (Over.mk t) P.A).left,
      (translPt P.A (d ^ (n + 1))).left, (translPt P.A d).left] ![(n : ℤ), 1, -((n : ℤ) + 1)]), w.IsGen
  | 0 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (gen_square P t hsq d d) ⟨_, DVR.invGen_isGen _ _ _ _ (gen_square P t hsq d d).choose_spec⟩)
    simp [Fin.sum_univ_succ]
    module
  | n + 1 => by
    refine gen_congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (gen_mul (solution hsq d n) (gen_square P t hsq (d ^ (n + 1)) d))
    have e : d ^ (n + 1) * d = d ^ (n + 1 + 1) := by rw [← pow_succ]
    simp [Fin.sum_univ_succ, e]
    module
end GlobalTheory.TwistTranslate
