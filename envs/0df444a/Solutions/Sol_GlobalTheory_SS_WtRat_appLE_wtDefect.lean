-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.appLE_wtDefect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:48:04.371734+00:00
-- url     : https://prove2.me/submissions/7887bab4-573a-4f1e-b9e2-bdfee7bdc889

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
namespace GlobalTheory.SS.WtRat
theorem _root_.solution {Z P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens)
    (u : Γ(G, V)) (e : Γ(T, ⊤)) (p : Z ⟶ P) {a' b' : Z ⟶ G} {c' : Z ⟶ T} (ha : p ≫ a = a')
    (hb : p ≫ b = b') (hc : p ≫ c = c') (h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V))
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ b' ⁻¹ᵁ V) :
    (p.appLE _ ⊤ h).hom (wtDefect a b c V u e) =
      (a'.appLE V ⊤ h₁).hom u - c'.appTop.hom e * (b'.appLE V ⊤ h₂).hom u := by
  subst ha hb hc
  have e₁ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p a V _ ⊤ inf_le_left h)
  have e₂ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p b V _ ⊤ inf_le_right h)
  have e₃ := congrArg (fun q => CommRingCat.Hom.hom q e)
    ((Scheme.Hom.appLE_comp_appLE p c ⊤ _ ⊤ le_top h).trans (Scheme.Hom.appLE_eq_app (p ≫ c)))
  rw [wtDefect, map_sub, map_mul]
  exact congrArg₂ (· - ·) e₁ (congrArg₂ (· * ·) e₃ e₂)
end GlobalTheory.SS.WtRat
