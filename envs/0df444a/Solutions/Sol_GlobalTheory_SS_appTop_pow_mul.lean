-- Prove2me | solution 1 for GlobalTheory.SS.appTop_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:16.214217+00:00
-- url     : https://prove2.me/submissions/03414ec1-f858-4140-b4b8-f08339d5e43d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGSplitTorusPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) (f : Γ(G.left, ⊤))
    (h : (show G ⟶ G from F ^ m).left.appTop.hom f = f ^ (q ^ m)) (j : ℕ) :
    (show G ⟶ G from F ^ (m * j)).left.appTop.hom f = f ^ (q ^ (m * j)) := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, pow_one]
    change (Scheme.Hom.appTop (𝟙 G.left)).hom f = f
    simp
  | succ j ih =>
    have e : (show G ⟶ G from F ^ (m * (j + 1))).left =
        (show G ⟶ G from F ^ m).left ≫ (show G ⟶ G from F ^ (m * j)).left := by
      rw [Nat.mul_succ, pow_add]; rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ih, map_pow, h,
      ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]
end GlobalTheory.SS
