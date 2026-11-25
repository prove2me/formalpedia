-- Prove2me | solution 1 for GlobalTheory.FrameGeo.frame_pullback_geo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:21.931489+00:00
-- url     : https://prove2.me/submissions/e30eb97a-de11-4fb9-bdf3-e5f30f8e25da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
import Theorems.Thm_GlobalTheory_FrameGeo_exists_ratio
import Theorems.Thm_GlobalTheory_FrameGeo_act_natCast_mul
import Theorems.Thm_GlobalTheory_FrameGeo_exists_gen_pull
import Theorems.Thm_GlobalTheory_FrameGeo_IsExpOf_mul
import Theorems.Thm_GlobalTheory_FrameGeo_IsExpOf_one
import Theorems.Thm_GlobalTheory_FrameGeo_IsExpOf_neg
import Theorems.Thm_GlobalTheory_FrameGeo_isExpOf_ad
import Theorems.Thm_GlobalTheory_FrameGeo_isExpOf_prod
import Theorems.Thm_GlobalTheory_FrameGeo_series_ext_one
import Theorems.Thm_GlobalTheory_FramePull_ExpIntegral_neg
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_ev_eq
import Theorems.Thm_GlobalTheory_FramePull_constantCoeff_point
import Theorems.Thm_GlobalTheory_FramePull_cz3
import Theorems.Thm_GlobalTheory_FramePull_ev_actK_hL
import Theorems.Thm_GlobalTheory_FramePull_hL_eq
import Theorems.Thm_GlobalTheory_JetSer_FBOf_ev_self
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (isCub_cubV cubV val₂)
namespace GlobalTheory.FrameGeo
theorem _root_.solution : JetAlgSt → RepSt → SerSt → SerExSt → RosIdSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Function.Surjective G.hom.appTop.hom → Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom → ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)), (∀ a, IsNormRos Lr.L _ _ (u a)) → ∀ (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ j : Lr.L.ι, ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j → ∀ B : FB R d O, IsFBOf Lr c act u x j B → ∀ (w0 : O) (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)), ρ.IsGen → ∀ (a : O) (N : ℕ), a * star a = (N : O) → (∃ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen) ∧ ∀ mu : LB.Gen (LB.LinComb Lr.L (K := Fin 2) ![𝟙 G.left, (act.act a).left] ![(N : ℤ), -1]), mu.IsGen → ∀ M r : PS R 1 d, IsSer1 x _ (mu.s (fun _ => j)).val M → IsSer1 x _ (ρ.s (fun _ => j)).val r → ∃ (w : PS R 1 d) (κ : Rˣ), w * r ^ N = C (κ : R) * M * ev (n := 1) ![B.A.act a] r ∧ ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d), B.IsCanonGauge k h → FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) := by
  intro hJet hRep _ _ _ R _ G _ _ s1 _ _ Lr c O _ _ act u hu d x hx j _ B hB w0 ρ hρ a N hN
  obtain ⟨mu₀, h₀, v₀⟩ := exists_gen_pull Lr c act a w0 N hN (u a) (hu a).1 ρ hρ
  refine ⟨⟨mu₀, h₀⟩, fun mu hmu M r hM hr => ?_⟩
  obtain ⟨α, hα, vα⟩ := exists_ratio Lr.isLB G.hom η[G].left (Over.w η[G]) s1 h₀ hmu
  have E := series_ext_one hJet hRep Lr c act u x hx j B hB
  have hκ : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom α) := hα.map _
  have e1 : ∀ s : PS R 1 d, ev ![B.A.act 1] s = s := fun s => by
    rw [B.A.one_act]
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this, FBOf.ev_self]
  have a0 : act.act 0 = 1 := by simpa using act_natCast_mul act 0 0
  have hQ : ev ![B.A.act 1, B.A.act 0, B.A.act 0] B.ph2 = 1 := E _ _ fun T z J hJ Φ y _ _ p _ => by
    rw [p, a0, MonObj.comp_one, (isCub_cubV c hJ).face₂, map_one, Units.val_one]
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← FramePull.constantCoeff_ev_eq (FramePull.cz3 (x := (0 : Pt R 2 d)) (fun _ => by simp)
      (FramePull.constantCoeff_point 0) (FramePull.constantCoeff_point 1)), B.cocycleRight_zero_fst, map_one]
  obtain ⟨P, hP⟩ : ∃ P : PS R 1 d,
      P = ∏ i ∈ Finset.range N, ev ![B.A.act 1, B.A.act ((i : O) * w0), B.A.act w0] B.ph2 := ⟨_, rfl⟩
  have P1 : constantCoeff P = 1 := by
    rw [hP, map_prod]
    exact Finset.prod_eq_one fun i _ => by
      rw [FramePull.constantCoeff_ev_eq (FramePull.cz3 (B.A.const _) (B.A.const _) (B.A.const _)), w1]
  have PQ : P * invOfUnit P 1 = 1 := mul_invOfUnit P 1 (by simpa using P1)
  have main : ev ![B.A.act 1, B.A.act (w0 * a)] (B.ad a) * r ^ N =
      C (hκ.unit : R) * M * ev (n := 1) ![B.A.act a] r * P := E _ _ fun T z J hJ Φ y q₀ q₁ q₃ q₂ => by
    have m₁ := q₁ _ _ _ mu M hM 1
    have m₂ := q₁ _ _ _ ρ r hr 1
    rw [e1, act.one, Category.comp_id] at m₁ m₂
    have eα : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (hκ.unit : R) = α :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply α
    have v := congrArg Units.val (v₀ T y z J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, vα _ _ z J hJ, Over.w, Units.val_pow_eq_pow_val,
      Units.coe_prod] at v
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, hP, map_prod, q₀, q₂, q₁ _ _ _ ρ r hr, m₁, m₂, eα, act.one,
      Category.comp_id, ← v]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [q₃, act.one, Category.comp_id]
  refine ⟨ev ![B.A.act 1, B.A.act (w0 * a)] (B.ad a) * invOfUnit P 1, hκ.unit, ?_, fun k _ _ _ h hh => ?_⟩
  · rw [mul_right_comm, main, _root_.mul_assoc _ P, PQ, _root_.mul_one]
  · have h1 := isExpOf_ad hh a 1 (w0 * a)
    have h2 := isExpOf_prod hh 1 w0 hQ N
    rw [← hP] at h2
    have e : star a * (w0 * a) = (N : O) * w0 := by rw [← hN]; ring
    rw [e, _root_.mul_one] at h1
    have h3 := (h1.mul (h2.neg PQ)).2
    rw [FramePull.ev_actK_hL, FramePull.hL_eq, h3]
    congr 1
    ring
end GlobalTheory.FrameGeo
