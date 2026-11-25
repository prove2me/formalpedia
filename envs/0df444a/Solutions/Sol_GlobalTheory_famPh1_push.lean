-- Prove2me | solution 1 for GlobalTheory.famPh1_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:35.67985+00:00
-- url     : https://prove2.me/submissions/a74383c1-3b33-4a91-9506-32462a0b6b3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
import Theorems.Thm_GlobalTheory_PushFirstLaw_val_carries
import Theorems.Thm_GlobalTheory_PushFirstLaw_val_theta
import Theorems.Thm_GlobalTheory_PushFirstLaw_lift_cubeMap
import Theorems.Thm_GlobalTheory_PushFirstLaw_rearrange
import Theorems.Thm_GlobalTheory_PushFirstLaw_val_scaleG
import Theorems.Thm_GlobalTheory_PushFirstLaw_formal_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory
open PushFirstLaw
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh1 t (𝟙 (Sp V)) d x F ph e → FamPh1 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hw hx _ hp F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  obtain ⟨-, c, -, hc, hcar⟩ := hp m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good t.PP.L t.PP.isLB y (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  have k := val_corr hJ' hcor (𝟙 _)
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J =
        (∏ k, isoVal w y J J' ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] k) ^ cε 2 k) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J' := fun φ => by
    refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).symm.trans ((val_carries hJ hJ' hcar _).trans
      (congrArg₂ (· * ·) ?_ (val_pull hJ' _ _ _).symm)))
    rw [Category.id_comp]
  have hl := lift_cubeMap n.cm (fun i => jptG t (𝟙 (Sp V)) d x m i) (fun i => jptG t' (𝟙 (Sp V)) d x' m i) (fun i => by
    simp only [jptG, Over.comp_left, hx m, Category.assoc])
  have hs := formal_sum hch m (isoVal w y J J') _ (fun _ => rfl)
  have k2 := (val_pull hJ' _ _ _).symm.trans (k.trans ((val_scaleG t hJ' _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ' _ _ _).trans (congrArg (_ * ·) ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_scaleG t' hJ _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hpe _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _)))
        ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _))))))))).symm)
  refine (congrArg (fun r => val (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t r y J)
    ((Category.id_comp _).trans hl)).trans ((val_theta n.cm hw.2 hJ hJ' _).trans ((congrArg₂ (· * ·) hs
      ((congrArg (fun r => val (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t r y J') (Category.id_comp _)).symm.trans k2)).trans
        (rearrange _ _ _ _ _ _ _)))
end GlobalTheory
