-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.jetOf_eq_of_jetPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:24.30947+00:00
-- url     : https://prove2.me/submissions/dd55e0ec-703c-4cb8-81a3-eb1e9b6aa9dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnVal.JetUniq
private theorem appLE_specMap_comp_fromSpecStalk_eq_germ {Y : Scheme.{0}} {y : Y} {R : CommRingCat.{0}}
    (φ : Y.presheaf.stalk y ⟶ R) (U : Y.Opens) (hy : y ∈ U) (hx : ⊤ ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ U) :
    (Spec.map φ ≫ Y.fromSpecStalk y).appLE U ⊤ hx = Y.presheaf.germ U y hy ≫ φ ≫ (Scheme.ΓSpecIso R).inv := by
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hy]
  have hx2 : ⊤ ≤ Spec.map φ ⁻¹ᵁ (Y.fromSpecStalk y ⁻¹ᵁ U) := hx
  change (Y.presheaf.germ U y hy ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv ≫
      (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE (le_top : Y.fromSpecStalk y ⁻¹ᵁ U ≤ ⊤)).op) ≫
      (Spec.map φ).appLE (Y.fromSpecStalk y ⁻¹ᵁ U) ⊤ hx2 = _
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE, Scheme.ΓSpecIso_inv_naturality]
  congr 2
end GlobalTheory.AnVal.JetUniq
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AnVal.JetUniq
theorem _root_.solution {g : ℕ} {Y : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (hol' : IsHolFam e') (m : ℕ) (h : PullbackSections.jetPt e hol m = PullbackSections.jetPt e' hol' m) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (hU' : e' 0 cpt ∈ U) (f : Γ(Y, U)) :
    PullbackSections.jetOf m (fun z => valAt' (e z) U f) = PullbackSections.jetOf m (fun z => valAt' (e' z) U f) := by
  have hx_of : ∀ (e₀ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (h₀ : IsHolFam e₀), e₀ 0 cpt ∈ U →
      ⊤ ≤ (PullbackSections.jetPt e₀ h₀ m) ⁻¹ᵁ U := by
    intro e₀ h₀ hU₀ p _
    have key2 : ∀ q, Y.fromSpecStalk ((e₀ 0) cpt) q ∈ U := fun q => by
      have hr : Y.fromSpecStalk ((e₀ 0) cpt) q ∈ Set.range (Y.fromSpecStalk ((e₀ 0) cpt)) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hr
      exact Specializes.mem_open hr U.isOpen hU₀
    exact key2 _
  have key : ∀ (e₀ : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (h₀ : IsHolFam e₀), e₀ 0 cpt ∈ U →
      ∀ hx : ⊤ ≤ (PullbackSections.jetPt e₀ h₀ m) ⁻¹ᵁ U,
      ((PullbackSections.jetPt e₀ h₀ m).appLE U ⊤ hx).hom f = toΓ _ (PullbackSections.jetOf m fun z => valAt' (e₀ z) U f) := by
    intro e₀ h₀ hU₀ hx
    unfold PullbackSections.jetPt nbhdPt at hx ⊢
    rw [appLE_specMap_comp_fromSpecStalk_eq_germ _ U hU₀, ← Category.assoc]
    unfold nbhdLift TopCat.Presheaf.germ
    rw [colimit.ι_desc]
    rfl
  have hx := hx_of e hol hU
  have hx' := hx_of e' hol' hU'
  have heq : ((PullbackSections.jetPt e hol m).appLE U ⊤ hx).hom f = ((PullbackSections.jetPt e' hol' m).appLE U ⊤ hx').hom f := by
    have hgen : ∀ (x x' : Sp (Jet ℂ (Fin 1 × Fin g) m) ⟶ Y) (_ : x = x') (hx : ⊤ ≤ x ⁻¹ᵁ U)
        (hx' : ⊤ ≤ x' ⁻¹ᵁ U), (x.appLE U ⊤ hx).hom f = (x'.appLE U ⊤ hx').hom f := by
      intro x x' hxx _ _
      subst hxx
      rfl
    exact hgen _ _ h hx hx'
  rw [key e hol hU hx, key e' hol' hU' hx'] at heq
  have hinj : Function.Injective (toΓ (Jet ℂ (Fin 1 × Fin g) m)) := by
    intro a b hab
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Jet ℂ (Fin 1 × Fin g) m))).hom.hom hab
    simpa [toΓ] using this
  exact hinj heq
end GlobalTheory.AnVal.JetUniq
