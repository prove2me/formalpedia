-- Prove2me | solution 1 for GlobalTheory.UU.nonempty_tq_of_gtCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:35:52.96763+00:00
-- url     : https://prove2.me/submissions/da81904f-86ad-49c2-922e-9cddd1ccf2ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
private theorem gs_id_appLE_eq_gs {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Y, U))
    (z : Z) : gs (𝟙 Z) z ⊤ ((f.appLE U ⊤ h).hom a) = gs f z U a := by
  rw [gs_eq (𝟙 Z) z ⊤ (by simp), gs_eq f z U (h (by simp))]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_id, RingHom.id_apply, CommRingCat.comp_apply]
  exact Z.presheaf.germ_res_apply (homOfLE h) z _ _
private theorem gs_id_appTop_eq_gs {Y Z : Scheme.{0}} (f : Z ⟶ Y) (a : Γ(Y, ⊤)) (z : Z) :
    gs (𝟙 Z) z ⊤ (f.appTop.hom a) = gs f z ⊤ a := by
  rw [gs_eq (𝟙 Z) z ⊤ (by simp), gs_eq f z ⊤ (by simp)]
  simp [Scheme.Hom.appTop] <;> rfl
set_option maxHeartbeats 1000000 in
private theorem exists_tq_i_eq_of_isAbelianScheme {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : ∃ Q : TQ (thickObj R I e G) D.X, Q.i = g.i := by
  refine ⟨{
      B := thickObj R I e D.P.A
      isAb := hB
      q := g.q
      i := g.i
      q_hom := g.q_hom
      i_hom := g.i_hom
      q_flat := g.q_flat
      q_surj := g.q_surj
      q_affine := g.q_affine
      isKernel := g.isKernel
      loc := ?_ }, rfl⟩
  intro b χ
  have hq := g.q_hom
  have hi := g.i_hom
  have hφ : ∀ k, D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k =
      ((Over.map (thick R I e)).map g.q).left ≫ D.Oφ (DegPre.prBe I D e) χ k := by
    intro k
    fin_cases k
    · show (lift ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) (toUnit _ ≫ D.c χ) ≫ μ).left =
        ((Over.map (thick R I e)).map g.q).left ≫ (lift (DegPre.prBe I D e) (toUnit _ ≫ D.c χ) ≫ μ).left
      rw [← Over.comp_left, ← Category.assoc, comp_lift, ← Category.assoc _ (toUnit _),
        toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · show (toUnit _ ≫ D.c χ).left = ((Over.map (thick R I e)).map g.q).left ≫ (toUnit _ ≫ D.c χ).left
      rw [← Over.comp_left, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · show ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e).left = _
      rw [Over.comp_left]
      rfl
    · show (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.P.A]).left =
        ((Over.map (thick R I e)).map g.q).left ≫
          (toUnit ((Over.map (thick R I e)).obj (thickObj R I e D.P.A)) ≫ η[D.P.A]).left
      rw [← Over.comp_left, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  choose j hj using fun k => exists_chart D.P.isLB (D.Oφ (DegPre.prBe I D e) χ k b)
  refine ⟨LB.wchart D.P.L (D.Oφ (DegPre.prBe I D e) χ) j, Set.mem_iInter.2 hj, ?_⟩
  have hle : g.q.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ (DegPre.prBe I D e) χ) j ≤
      LB.wchart D.P.L (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) j := by
    intro y hy
    refine Set.mem_iInter.2 fun k => ?_
    rw [Set.mem_preimage, hφ k]
    exact Set.mem_iInter.1 hy k
  refine ⟨res hle ((g.t χ).s j), ?_⟩
  intro Z t' g' h₁ h₂
  have ht := g.t_gen χ
  have hw := g.t_weight χ
  have mz : ∀ {W : Scheme.{0}} (w : W), w ∈ (⊤ : W.Opens) := fun _ => by simp
  apply fn_ext
  intro z _
  rw [gs_mul (𝟙 Z.left) z ⊤ (mz _), gs_id_appLE_eq_gs, gs_id_appLE_eq_gs, gs_id_appTop_eq_gs,
    ]
  erw [gs_unit ((t' ≫ g.i) * g').left z _ (h₁ (mz z)), gs_unit g'.left z _ (h₂ (mz z)),
    gs_unit t'.left z ⊤ (mz _), ← Units.val_mul]
  congr 1
  erw [gm_res ((t' ≫ g.i) * g').left z hle (h₁ (mz z)), gm_res g'.left z hle (h₂ (mz z))]
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
  have h1q : (t' ≫ g.i) ≫ g.q = 1 := by
    rw [Category.assoc, g.isKernel.w, ← Category.assoc, toUnit_unique (t' ≫ toUnit _) (toUnit _)]
    rfl
  have e12 : ∀ k, ((t' ≫ g.i) * g').left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k =
      g'.left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k := by
    intro k
    rw [hφ k, ← Category.assoc, ← Category.assoc]
    congr 1
    show ((t' ≫ g.i) * g').left ≫ g.q.left = g'.left ≫ g.q.left
    rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, h1q, _root_.one_mul]
  have hc := val_corr hJ hw (lift t' g').left
  rw [val_pull hJ, val_mul hJ, val_pull hJ] at hc
  have em : (lift t' g').left ≫ (lift (fst (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X)
      (thickObj R I e G) ≫ g.i) (snd (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X)
      (thickObj R I e G)) ≫ μ).left = ((t' ≫ g.i) * g').left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
    rfl
  have es : (lift t' g').left ≫ (snd (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X)
      (thickObj R I e G)).left = g'.left := by
    rw [← Over.comp_left, lift_snd]
  rw [em, es] at hc
  have hcg : val (charGen D.X (thickObj R I e G) D.P.L χ) (lift t' g').left z J =
      gm t'.left z ⊤ (charUnit _ D.X χ) := by
    show gm _ z _ (res _ (pullU _ ⊤ (charUnit _ D.X χ))) = _
    erw [gm_res, gm_pull, ← Over.comp_left, lift_fst]
    all_goals simp [LB.wchart]
  rw [hcg] at hc
  have m1 : ((t' ≫ g.i) * g').left z ∈
      LB.wchart D.P.L (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) j := hle (h₁ (mz z))
  have m2 : g'.left z ∈
      LB.wchart D.P.L (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) j := hle (h₂ (mz z))
  erw [gen_trans ht _ z m1 (hJ.mem _ ((t' ≫ g.i) * g').left), gen_trans ht _ z m2 (hJ.mem _ g'.left)]
  have hv := hc
  simp only [val, e12] at hv
  simp only [e12]
  have etr : trF (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) Oinvε ((t' ≫ g.i) * g').left z j
      (fun k => J (g'.left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k)) =
      trF (D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ) Oinvε g'.left z j
      (fun k => J (g'.left ≫ D.Oφ ((Over.map (thick R I e)).map g.q ≫ DegPre.prBe I D e) χ k)) := by
    simp only [trF, e12]
  rw [etr, hv]
  exact _root_.mul_left_comm _ _ _
end GlobalTheory.UU
end
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : ∃ Q : TQ (thickObj R I e G) D.X, Q.i = g.i := exists_tq_i_eq_of_isAbelianScheme g hB
end GlobalTheory.UU
