-- Prove2me | solution 1 for GlobalTheory.WeightGen.exists_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:54.080752+00:00
-- url     : https://prove2.me/submissions/382b1717-53cb-47d2-8826-71005c1c1c6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_FunDescent_comp_appTop_apply
import Theorems.Thm_GlobalTheory_invariant_functions_descend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {S : Scheme.{0}}
variable {E : SplitExt S} {G : Over S} [GrpObj G] (d : E.GtDatum G)
attribute [local instance] SplitExt.free SplitExt.finite
namespace GlobalTheory.WeightGen
theorem _root_.solution (hG : GlobalFnsSt) (f : Γ(G.left, ⊤))
    (hf : (act d).left.appTop.hom f = (snd (splitTorus S E.X) G).left.appTop.hom f) :
    ∃ c, G.hom.appTop.hom c = f := by
  have := d.q_affine
  obtain ⟨b, hb⟩ := (invariant_functions_descend S G E.B _ d.q d.i d.q_hom d.i_hom d.q_flat
    d.q_surjective inferInstance d.isKernel ⊤).2.2 f (fun Z t g h₁ h₂ => by
      have e₁ : (t ≫ d.i) * g = lift t g ≫ act d := by
        rw [Hom.mul_def, comp_lift_assoc, lift_fst_assoc, lift_snd]
      have key : ((t ≫ d.i) * g).left.appTop.hom f = g.left.appTop.hom f := by
        rw [e₁, Over.comp_left, FunDescent.comp_appTop_apply, hf, ← FunDescent.comp_appTop_apply,
          ← Over.comp_left, lift_snd]
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.app_eq_appLE] at key
      exact key)
  obtain ⟨c, hc⟩ := (hG S E.B E.isAbelian).2 b
  refine ⟨c, ?_⟩
  rw [← Over.w d.q, FunDescent.comp_appTop_apply, hc]
  exact hb
end GlobalTheory.WeightGen
