-- Prove2me | solution 1 for GlobalTheory.SqZero.expBij_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:34.939024+00:00
-- url     : https://prove2.me/submissions/95baf4db-d6c5-4166-b3f8-aa489a1caf73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_awayToAwayRight_eq_of_comp
import Theorems.Thm_GlobalTheory_SqZero_awayToAwayLeft_eq_of_comp
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_IsAway_pow_mul_mem
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_away_ext
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_comp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_isAway_awayHom
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_GlobalTheory_SqZero_map_sq
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
variable {v : Fin n → (epsR R ⟶ G)}
variable [Smooth G.hom]
omit [Smooth G.hom]
namespace GlobalTheory.SqZero
theorem _root_.solution {s : Set A} (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, ∀ (T : Type) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T), IsUnit (φ f) →
      ExpBij T v) : ExpBij A v := by
  intro J hJ
  have hs' : Ideal.span (Set.range (Subtype.val : s → A)) = ⊤ := by
    rwa [Subtype.range_coe_subtype]
  let q : ∀ f : s, A →ₐ[R] Localization.Away f.1 := fun f => awayHom R f.1
  have hq : ∀ f : s, IsAway (q f) f.1 := fun f => isAway_awayHom _
  have hb := fun f : s => h f f.2 _ (q f) (hq f).unit (J.map (q f)) (map_sq hJ _)
  refine ⟨fun c c' hcJ hcJ' hc hc' hcc => funext fun i => ?_, fun y hy => ?_⟩
  · refine Localization.algebraMap_injective_of_span_eq_top s hs (funext fun f => ?_)
    have := congrArg (spMap (q f) ≫ ·) hcc
    simp only [comp_lieExp] at this
    exact congrFun ((hb f).1 _ _ (fun i => Ideal.mem_map_of_mem _ (hcJ i))
      (fun i => Ideal.mem_map_of_mem _ (hcJ' i)) _ _ this) i
  · choose d hd hdJ ed using fun f : s => (hb f).2 _
      (comp_mem_redKer hy (q f) fun a ha => Ideal.mem_map_of_mem _ ha)
    have compat : ∀ (i : Fin n) (f g : s),
        IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g : A)) f.1 g (d f i) =
          IsLocalization.Away.awayToAwayLeft g.1 f (d g i) := by
      intro i f g
      let p := awayHom R (f * g : A)
      have hp : IsAway p (f * g : A) := isAway_awayHom _
      have hpf : IsUnit (p f) := isUnit_of_mul_isUnit_left (by rw [← map_mul]; exact hp.unit)
      obtain ⟨a, ha⟩ := (hq f).lift p hpf
      obtain ⟨b, hb⟩ := (hq g).lift p
        (isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact hp.unit))
      rw [awayToAwayRight_eq_of_comp f.1 g.1 a ha, awayToAwayLeft_eq_of_comp f.1 g.1 b hb]
      have e : spMap a ≫ lieExp v (d f) (hd f) = spMap b ≫ lieExp v (d g) (hd g) := by
        rw [← ed, ← ed, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, ha, hb]
      rw [comp_lieExp, comp_lieExp] at e
      refine congrFun ((h f f.2 _ p hpf (J.map p) (map_sq hJ _)).1 _ _ (fun k => ?_) (fun k => ?_)
        _ _ e) i
      · rw [← ha, ← Ideal.map_mapₐ]
        exact Ideal.mem_map_of_mem _ (hdJ f k)
      · rw [← hb, ← Ideal.map_mapₐ]
        exact Ideal.mem_map_of_mem _ (hdJ g k)
    choose c hc using fun i => (Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs
      (fun f => d f i) (compat i)).exists
    have hcJ : ∀ i, c i ∈ J := fun i =>
      Submodule.mem_of_span_eq_top_of_smul_pow_mem J s hs _ fun f =>
        (hq f).pow_mul_mem (by
          have : q f (c i) = d f i := hc i f
          rw [this]
          exact hdJ f i)
    refine ⟨c, fun i => mul_eq_zero_of_sq hJ (hcJ i) (hcJ i), hcJ,
      away_ext hs' q hq fun f => ?_⟩
    rw [ed, comp_lieExp]
    exact lieExp_congr _ (fun i => (hc i f).symm) _ _
end GlobalTheory.SqZero
