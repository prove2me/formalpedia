-- Prove2me | solution 1 for GlobalTheory.JetSer.FBOf.fbOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:59:26.753016+00:00
-- url     : https://prove2.me/submissions/46f56cce-ba7c-442d-8f9b-e11a3129d58d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Theorems.Thm_GlobalTheory_JetSer_FBOf_series_ext
import Theorems.Thm_GlobalTheory_JetSer_FBOf_unit_mem_cube
import Theorems.Thm_GlobalTheory_JetSer_FBOf_unit_mem_ros
import Theorems.Thm_GlobalTheory_JetSer_FBOf_ev_self2
import Theorems.Thm_GlobalTheory_JetSer_FBOf_ev_self3
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_val val val_of Good cubV val₂ IsCub isCub_cubV exists_chart psum_hom preHom)
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FBOf
namespace GlobalTheory.JetSer.FBOf
theorem _root_.solution : JetAlgSt → RepSt → LawSt → MapSt → ActSt → SerSt → SerExSt → ValSerSt → RosIdSt → FBOfSt := by
  intro hJet hRep hLaw _ hAct _ hSer _ hRos R _ G _ _ s2 s3 Lr c O _ _ act u hu d x hx j hj
  obtain ⟨⟨Gl, hF⟩, -⟩ := hLaw R G d x hx
  obtain ⟨A, hA⟩ := hAct R G d x hx O act Gl hF
  obtain ⟨-, e2, e3⟩ := hSer R G d x hx
  obtain ⟨ph, hph, -⟩ := e3 _ (unit_mem_cube Lr.L j hj) (c.t.s (fun _ => j)).val
  have exad := fun a : O => (e2 _ (@unit_mem_ros _ _ _ _ _ Lr.L j hj _ _ (act.hom a) (act.hom (star a)))
    ((u a).s (fun _ => j))⁻¹.val).exists
  choose ad had using exad
  have K := series_ext hJet hRep Lr c act u x hx j Gl.F hF A.act hA ph hph ad had
  have Ro := hRos _ G s2 s3 Lr c O act u hu
  have gA : ∀ {n} {a b : Pt R n d}, GP a → GP b → GP (addOf Gl.F a b) := fun ha hb => gp_addOf _ Gl.const _ _ ha hb
  have gC : ∀ {n} (o) {a : Pt R n d}, GP a → GP (comp1 (A.act o) a) := fun o _ ha => gp_comp1 _ _ (A.const o) ha
  have g0 : ∀ {n}, GP (0 : Pt R n d) := gp_zero₂
  have gp : ∀ {n} (i : Fin n), GP (pt R d i) := fun i => gp_pt i
  have face : ∀ {n} (a b : Pt R n d), GP a → GP b → ev ![0, a, b] ph = 1 := fun a b ha hb =>
    K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [p _ _ _ g0 ha hb, y0, (isCub_cubV c hJ).face, map_one, Units.val_one]
  have s01 : ∀ {n} (a b e : Pt R n d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![b, a, e] ph := fun a b e ha hb he =>
    K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [p _ _ _ ha hb he, p _ _ _ hb ha he, (isCub_cubV c hJ).s01]
  have s12 : ∀ {n} (a b e : Pt R n d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![a, e, b] ph := fun a b e ha hb he =>
    K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [p _ _ _ ha hb he, p _ _ _ ha he hb, (isCub_cubV c hJ).s12]
  have coc : ∀ {n} (a b e f : Pt R n d), GP a → GP b → GP e → GP f →
      ev ![a, b, f] ph * ev ![addOf Gl.F a b, e, f] ph = ev ![b, e, f] ph * ev ![a, addOf Gl.F b e, f] ph :=
    fun a b e f ha hb he hf => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, p _ _ _ ha hb hf, p _ _ _ (gA ha hb) he hf, p _ _ _ hb he hf, p _ _ _ ha (gA hb he) hf,
        ya _ _ ha hb, ya _ _ hb he, ← Units.val_mul, ← Units.val_mul, _root_.mul_comm, (isCub_cubV c hJ).coc,
        _root_.mul_comm]
  have cpt : ∀ {n} (a b e f : Pt R n d), GP a → GP b → GP e → GP f →
      ev ![a, b, e] ph * ev ![a, b, f] ph * ev ![addOf Gl.F a b, e, f] ph =
        ev ![a, e, f] ph * ev ![b, e, f] ph * ev ![a, b, addOf Gl.F e f] ph :=
    fun a b e f ha hb he hf => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, map_mul, p _ _ _ ha hb he, p _ _ _ ha hb hf, p _ _ _ (gA ha hb) he hf,
        p _ _ _ ha he hf, p _ _ _ hb he hf, p _ _ _ ha hb (gA he hf), ya _ _ ha hb, ya _ _ he hf]
      have := congrArg Units.val ((isCub_cubV c hJ).compat (y a) (y b) (y e) (y f))
      simp only [Units.val_mul] at this
      linear_combination this
  have inv3 : ∀ {U : Type} [CommGroup U] {a b e s t : U}, a * s = t * (b * e) → t * a⁻¹ = b⁻¹ * e⁻¹ * s := by
    intro U _ a b e s t h
    have : s = a⁻¹ * (t * (b * e)) := by rw [← h, inv_mul_cancel_left]
    rw [this]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have l1 : ∀ {n} (o) (a b e : Pt R n d), GP a → GP b → GP e →
      ev ![comp1 (A.act o) a, comp1 (A.act o) b, e] ph * ev ![addOf Gl.F a b, e] (ad o) =
        ev ![a, e] (ad o) * ev ![b, e] (ad o) * ev ![a, b, comp1 (A.act (star o)) e] ph :=
    fun o a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, p _ _ _ (gC o ha) (gC o hb) he, p _ _ _ ha hb (gC _ he), q _ _ _ (gA ha hb) he,
        q _ _ _ ha he, q _ _ _ hb he, ya _ _ ha hb, yc _ _ ha, yc _ _ hb, yc _ _ he, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul]
      exact congrArg Units.val (inv3 ((Ro T z J hJ).1 o _ _ _))
  have l2 : ∀ {n} (o) (a b e : Pt R n d), GP a → GP b → GP e →
      ev ![comp1 (A.act o) a, b, e] ph * ev ![a, addOf Gl.F b e] (ad o) =
        ev ![a, b] (ad o) * ev ![a, e] (ad o) * ev ![a, comp1 (A.act (star o)) b, comp1 (A.act (star o)) e] ph :=
    fun o a b e ha hb he => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, p _ _ _ (gC o ha) hb he, p _ _ _ ha (gC _ hb) (gC _ he), q _ _ _ ha (gA hb he),
        q _ _ _ ha hb, q _ _ _ ha he, ya _ _ hb he, yc _ _ ha, yc _ _ hb, yc _ _ he, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul]
      exact congrArg Units.val (inv3 ((Ro T z J hJ).2.1 o _ _ _))
  have a1 : ∀ {n} (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad 1) = 1 :=
    fun a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [q _ _ _ ha hb, map_one]
      exact congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.1 _ _)
  have am : ∀ {n} (o o') (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad (o * o')) =
      ev ![comp1 (A.act o') a, b] (ad o) * ev ![a, comp1 (A.act (star o)) b] (ad o') :=
    fun o o' a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, q _ _ _ ha hb, q _ _ _ (gC _ ha) hb, q _ _ _ ha (gC _ hb), yc _ _ ha, yc _ _ hb, ← Units.val_mul,
        ← mul_inv]
      exact congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.2.1 _ _ _ _)
  have aa : ∀ {n} (o o') (a b : Pt R n d), GP a → GP b →
      ev ![comp1 (A.act o) a, comp1 (A.act o') a, b] ph * ev ![a, b] (ad (o + o')) =
        ev ![a, b] (ad o) * ev ![a, b] (ad o') * ev ![a, comp1 (A.act (star o)) b, comp1 (A.act (star o')) b] ph :=
    fun o o' a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, map_mul, map_mul, p _ _ _ (gC _ ha) (gC _ ha) hb, p _ _ _ ha (gC _ hb) (gC _ hb), q _ _ _ ha hb,
        q _ _ _ ha hb, q _ _ _ ha hb, yc _ _ ha, yc _ _ ha, yc _ _ hb, yc _ _ hb, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_mul]
      exact congrArg Units.val (inv3 ((Ro T z J hJ).2.2.2.2.1 _ _ _ _))
  have as : ∀ {n} (o) (a b : Pt R n d), GP a → GP b → ev ![a, b] (ad o) * ev ![b, a] (ad (star o)) = 1 :=
    fun o a b ha hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [map_mul, q _ _ _ ha hb, q _ _ _ hb ha, ← Units.val_mul, ← mul_inv, map_one]
      exact congrArg (fun t => t⁻¹.val) ((Ro T z J hJ).2.2.2.2.2 _ _ _)
  have x0 : ∀ {n} (o) (b : Pt R n d), GP b → ev ![0, b] (ad o) = 1 :=
    fun o b hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [q _ _ _ g0 hb, y0, map_one]
      have h := (Ro T z J hJ).1 o 1 1 (y b)
      have := act.hom o
      beta_reduce at h
      rw [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face, (isCub_cubV c hJ).face, _root_.mul_one,
        _root_.one_mul] at h
      exact congrArg (fun t => t⁻¹.val) (left_eq_mul.1 h)
  have x1 : ∀ {n} (o) (b : Pt R n d), GP b → ev ![b, 0] (ad o) = 1 :=
    fun o b hb => K _ _ _ fun T z J hJ Φ y y0 ya yc p q => by
      rw [q _ _ _ hb g0, y0, map_one]
      have h := (Ro T z J hJ).2.1 o (y b) 1 1
      have := act.hom (star o)
      beta_reduce at h
      rw [_root_.mul_one, MonObj.one_comp, (isCub_cubV c hJ).face₂, (isCub_cubV c hJ).face₂, _root_.mul_one,
        _root_.one_mul] at h
      exact congrArg (fun t => t⁻¹.val) (left_eq_mul.1 h)
  have f0 : ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 := face _ _ (gp 0) (gp 1)
  have f1 : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 := (s01 _ _ _ (gp 0) g0 (gp 1)).trans f0
  have f2 : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph = 1 := (s12 _ _ _ (gp 0) (gp 1) g0).trans f1
  refine ⟨{ G := Gl, A := A, ph1 := ph, ph2 := ph, sy := 1, ad := ad
            cocycleLeft_zero_fst := f0, cocycleLeft_zero_snd := f1, cocycleLeft_zero_thd := f2, cocycleRight_zero_fst := f0, cocycleRight_zero_snd := f1, cocycleRight_zero_thd := f2
            symmetry_zero_fst := ev_one _, symmetry_zero_snd := ev_one _
            adjoint_zero_fst := fun a => x0 a _ (gp 0), adjoint_zero_snd := fun a => x1 a _ (gp 0)
            cocycleLeft_assoc := coc _ _ _ _ (gp 0) (gp 1) (gp 2) (gp 3)
            cocycleLeft_comm := (s01 _ _ _ (gp 1) (gp 0) (gp 2)).trans (ev_self3 _)
            cocycleRight_assoc := ?_
            cocycleRight_comm := (s12 _ _ _ (gp 0) (gp 2) (gp 1)).trans (ev_self3 _)
            interchange := cpt _ _ _ _ (gp 0) (gp 1) (gp 2) (gp 3)
            sy_inv := by rw [ev_one, _root_.mul_one]
            sy_law := ?_
            adjoint_compat_left := fun a => l1 a _ _ _ (gp 0) (gp 1) (gp 2)
            adjoint_compat_right := fun a => l2 a _ _ _ (gp 0) (gp 1) (gp 2)
            ad_one := (ev_self2 _).symm.trans (a1 _ _ (gp 0) (gp 1))
            ad_mul := fun a b => (ev_self2 _).symm.trans (am a b _ _ (gp 0) (gp 1))
            ad_add := fun a b => ?_
            ad_sy := fun a => ?_ }, hF, hA, hph, rfl, rfl, had⟩
  · have rot : ∀ (a b e : Pt R 4 d), GP a → GP b → GP e → ev ![a, b, e] ph = ev ![b, e, a] ph := fun a b e ha hb he =>
      (s01 _ _ _ ha hb he).trans (s12 _ _ _ hb ha he)
    rw [rot _ _ _ (gp 0) (gp 1) (gp 2), rot _ _ _ (gp 0) (gA (gp 1) (gp 2)) (gp 3), rot _ _ _ (gp 0) (gp 2) (gp 3),
      rot _ _ _ (gp 0) (gp 1) (gA (gp 2) (gp 3))]
    exact coc _ _ _ _ (gp 1) (gp 2) (gp 3) (gp 0)
  · rw [ev_one, ev_one, ev_one, _root_.mul_one, _root_.mul_one, _root_.one_mul]
    exact (ev_self3 _).symm.trans ((s01 _ _ _ (gp 0) (gp 1) (gp 2)).trans (s12 _ _ _ (gp 1) (gp 0) (gp 2)))
  · have := aa a b _ _ (gp (0 : Fin 2)) (gp 1)
    rwa [ev_self2, ev_self2, ev_self2] at this
  · have := as a _ _ (gp (0 : Fin 2)) (gp 1)
    rw [ev_self2] at this
    rw [ev_one, ev_one, _root_.mul_one, this]
end GlobalTheory.JetSer.FBOf
