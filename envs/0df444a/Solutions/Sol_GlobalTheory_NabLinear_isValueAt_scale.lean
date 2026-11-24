-- Prove2me | solution 1 for GlobalTheory.NabLinear.isValueAt_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:33.475239+00:00
-- url     : https://prove2.me/submissions/ba5a1730-5bab-4c3e-a01f-1491677c0f83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ConnectionLinearInSection
import Theorems.Thm_GlobalTheory_NabLinear_gs_liftFun
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_pullSec_stalk


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.NabLinear
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)
namespace GlobalTheory.NabLinear
theorem _root_.solution {T T' : Over S0} (g : T' ⟶ T) {F F' : LB.Sec (LPow A L a T)} {r : Γ(T.left, ⊤)}
    (hF : ∀ j, F'.f j = liftFun A _ (T := T) r * F.f j) {F₁ F₂ : LB.Sec (LPow A L a T')}
    (h₁ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F F₁)
    (h₂ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F' F₂) {z : T' ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T'.left, ⊤)}
    (hv : IsValueAt A L a F₁ z τ v) : IsValueAt A L a F₂ z τ (g.left.appTop.hom r * v) := by
  intro j
  have key : (T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (F₂.f j)) =
      (T'.left.presheaf.map (homOfLE le_top).op).hom (g.left.appTop.hom r) *
      (T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (F₁.f j)) := by
    apply fn_ext
    intro x hx
    have hP := val_le A L z j hx
    have hP' : (𝟙 T'.left ≫ (ptSecT A z).left) x ∈ (LPow A L a T').U j := hP
    have hQ : ((𝟙 T'.left ≫ (ptSecT A z).left) ≫ (g ▷ A).left) x ∈ (LPow A L a T).U j :=
      chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j hP'
    have e : ((𝟙 T'.left ≫ (ptSecT A z).left) ≫ (g ▷ A).left) ≫ (fst T A).left = 𝟙 T'.left ≫ g.left := by
      rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left]
      congr 1
      simp [ptSecT]
    have t : ∀ s : LB.Sec (LPow A L a T'), gs (𝟙 _) x _
        ((T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) := fun s =>
      (gs_res (𝟙 _) x (val_le A L z j) hx _).trans (gs_pull (𝟙 _) (ptSecT A z).left x _ hP (s.f j))
    refine (t F₂).trans ((GermD.pullSec_stalk A L a h₂ _ x j hP').trans ?_)
    refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
    refine (congrArg (gs _ x _) (hF j)).trans ((gs_mul _ x _ hQ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine (gs_liftFun A _ r _ x hQ).trans ?_
      rw [e]
      exact ((gs_res (𝟙 _) x le_top hx _).trans (gs_pull (𝟙 _) g.left x ⊤ trivial r)).symm
    · exact ((t F₁).trans (GermD.pullSec_stalk A L a h₁ _ x j hP')).symm
  rw [key, hv j, map_mul]
  exact (_root_.mul_assoc _ _ _).symm
end GlobalTheory.NabLinear
