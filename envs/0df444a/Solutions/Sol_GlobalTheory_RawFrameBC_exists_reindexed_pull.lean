-- Prove2me | solution 1 for GlobalTheory.RawFrameBC.exists_reindexed_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:45.188957+00:00
-- url     : https://prove2.me/submissions/0f7a049f-730f-48ce-892d-05f1e3e76d27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsRawChartFramesBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RawFrameBC
private theorem pull2_lemma_9 {Z' Y' Z Y : Scheme.{0}} (a : Z' ⟶ Y') (g : Y' ⟶ Y) (r : Z' ⟶ Z) (b : Z ⟶ Y)
    (hab : a ≫ g = r ≫ b) (U : Y.Opens) (V : Y'.Opens) (hV : V ≤ g ⁻¹ᵁ U) (W1 : Z'.Opens) (hW1 : W1 ≤ a ⁻¹ᵁ V)
    (V' : Z.Opens) (hV' : V' ≤ b ⁻¹ᵁ U) (W1' : Z'.Opens) (hW1' : W1' ≤ r ⁻¹ᵁ V') (W2 : Z'.Opens)
    (h12 : W2 ≤ W1) (h12' : W2 ≤ W1') (u : Γ(Y, U)ˣ) :
    Units.map (Z'.presheaf.map (homOfLE h12).op).hom.toMonoidHom (Units.map (Z'.presheaf.map (homOfLE hW1).op).hom.toMonoidHom
      (Units.map (a.app V).hom.toMonoidHom (Units.map (Y'.presheaf.map (homOfLE hV).op).hom.toMonoidHom (Units.map (g.app U).hom.toMonoidHom u)))) =
    Units.map (Z'.presheaf.map (homOfLE h12').op).hom.toMonoidHom (Units.map (Z'.presheaf.map (homOfLE hW1').op).hom.toMonoidHom
      (Units.map (r.app V').hom.toMonoidHom (Units.map (Z.presheaf.map (homOfLE hV').op).hom.toMonoidHom (Units.map (b.app U).hom.toMonoidHom u)))) := by
  have hW : W2 ≤ (a ≫ g) ⁻¹ᵁ U := fun z hz => hV (hW1 (h12 hz))
  have hW' : W2 ≤ (r ≫ b) ⁻¹ᵁ U := fun z hz => hV' (hW1' (h12' hz))
  have e1 : g.app U ≫ Y'.presheaf.map (homOfLE hV).op ≫ a.app V ≫ Z'.presheaf.map (homOfLE hW1).op ≫
      Z'.presheaf.map (homOfLE h12).op = (a ≫ g).appLE U W2 hW := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  have e2 : b.app U ≫ Z.presheaf.map (homOfLE hV').op ≫ r.app V' ≫ Z'.presheaf.map (homOfLE hW1').op ≫
      Z'.presheaf.map (homOfLE h12').op = (r ≫ b).appLE U W2 hW' := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    rfl
  have e3 : ∀ (f f' : Z' ⟶ Y) (hf : f = f') (h : W2 ≤ f ⁻¹ᵁ U) (h' : W2 ≤ f' ⁻¹ᵁ U),
      f.appLE U W2 h = f'.appLE U W2 h' := by
    intro f f' hf h h'
    subst hf
    rfl
  have key := congrArg (fun F => F.hom (u : Γ(Y, U))) (e1.trans ((e3 _ _ hab hW hW').trans e2.symm))
  apply Units.ext
  simpa using key
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ)
end
end GlobalTheory.RawFrameBC
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawFrameBC
namespace GlobalTheory.RawFrameBC
theorem _root_.solution {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) (g : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (h : φ' = fun k => g ≫ φ k) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c' (LB.pullGen L φ ε c g) ∧
      ∀ (Z Z' : Scheme.{0}) (a : Z' ⟶ Y') (b : Z ⟶ Y) (r : Z' ⟶ Z), a ≫ g = r ≫ b →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ' ε c' a) (LB.pullGen L _ _ (LB.pullGen L φ ε c b) r) := by
  subst h
  refine ⟨LB.pullGen L φ ε c g, DVR.pullGen_isGen L φ ε c hc g, corr_of_val hL fun y J => congrFun rfl, ?_⟩
  intro Z Z' a b r hab j j' hj hj' hjj
  have hjj' : j = j' := funext fun k => hjj k k (by
    show a ≫ g ≫ φ k = r ≫ b ≫ φ k
    rw [← Category.assoc, hab, Category.assoc])
  subst hjj'
  simp only [LB.pullGen]
  unfold pullU res
  exact pull2_lemma_9 a g r b hab _ _ _ _ _ _ _ _ _ _ _ _ (c.s j)
end GlobalTheory.RawFrameBC
