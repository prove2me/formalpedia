-- Prove2me | solution 1 for GlobalTheory.ThetaVal.rig_of_frAxes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:22.743446+00:00
-- url     : https://prove2.me/submissions/65578c91-3260-4bd0-9a29-0967efaf8364

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FrameRigidificationOfCanonicalAxes
import Theorems.Thm_GlobalTheory_ThetaVal_jetAug_comp_jetSubstP
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_rigT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
namespace GlobalTheory.ThetaVal
private theorem homAt_comp_homAt_eq_homAt_comp {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A]
    [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    Formalism.L2.Pj.homAt x0 g ≫ Formalism.L2.Pj.homAt x0 f = Formalism.L2.Pj.homAt x0 (g.comp f) := by
  unfold Formalism.L2.Pj.homAt
  ext : 1
  simp only [Over.comp_left, Over.homMk_left]
  unfold spMap
  rw [← Spec.map_comp]
  rfl
end GlobalTheory.ThetaVal
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory GlobalTheory.ThetaVal
set_option maxHeartbeats 4000000
namespace GlobalTheory.ThetaVal
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∀ wP : PrimTyG t, IsPrimG t wP → Rig0G t x0 d x act e wP := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x hF hact hch e hgen htr hax wP hP
  have hL : t.PP.L.IsLB := t.PP.isLB
  unfold Rig0G eLG peG
  apply corr_of_val hL
  intro y J hJ
  rw [val_pull hJ, val_mul hJ, val_pull hJ]
  rw [val_pull hJ (φ := cφG t ![jptG t x0 d x 0 (0 : Fin 2), jptG t x0 d x 0 (1 : Fin 2)]) (ε := cε 2) (t := e 0)]
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.val_rigT _ _ _ _ _ _ _ hJ]
  have hA : (𝟙 _ ≫ Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S))) ≫
      (x 0).left = (overAt x0 S).hom ≫ eSec t.G := by
    rw [Category.id_comp, ← Over.comp_left, hch.zero 0]
    rfl
  have hB : ∀ ψ : Fin 2 × Fin d → MvPolynomial (Fin 1 × Fin d) S,
      (𝟙 _ ≫ Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S))) ≫
        Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetSubstP 0 ψ)) =
        Over.Hom.left (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 2 × Fin d) 0 →ₐ[S] S)) := by
    intro ψ
    rw [Category.id_comp, ← Over.comp_left, homAt_comp_homAt_eq_homAt_comp, jetAug_comp_jetSubstP]
  rw [hA, hB]
  rw [← hB (fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S)
      p.1 p.2)]
  rw [← val_pull hJ (φ := cφG t ![jptG t x0 d x 0 (0 : Fin 2), jptG t x0 d x 0 (1 : Fin 2)]) (ε := cε 2)
    (t := e 0)]
  rw [val_corr hJ (hax 0).1, val_one, _root_.mul_one]
  rw [← val_pull hJ wP (eSec t.G), val_corr hJ hP.2, Category.id_comp]
end GlobalTheory.ThetaVal
