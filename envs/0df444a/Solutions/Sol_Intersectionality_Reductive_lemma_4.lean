-- Prove2me | solution 1 for Intersectionality.Reductive.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:36:28.77278+00:00
-- url     : https://prove2.me/submissions/17b347fc-4d8c-4de1-9cf6-61b167579653

import Mathlib
import Definitions.Def_Intersectionality_Reductive_Setting

open MeasureTheory Filter Topology Set
open Intersectionality.Generic Intersectionality.Reductive

namespace IsectCore

section Alg
variable {X : Set ℝ} {Q : Set (↥X → ↥X)}

lemma uniq (hQ : IsPolicyFamily Q) {q q' : ↥X → ↥X} (hq : q ∈ Q) (hq' : q' ∈ Q) (x : ↥X)
    (h : q x = q' x) : q = q' := by
  funext y
  obtain ⟨s, hs, hsx⟩ := hQ.rich x y
  have h1 := congrFun (hQ.comm q hq s hs) x
  have h2 := congrFun (hQ.comm q' hq' s hs) x
  simp only [Function.comp] at h1 h2
  rw [← hsx, h1, h2, h]

lemma id_mem (hQ : IsPolicyFamily Q) (x : ↥X) : (id : ↥X → ↥X) ∈ Q := by
  obtain ⟨q, hq, hqx⟩ := hQ.rich x x
  have : q = id := by
    funext y
    obtain ⟨s, hs, hsx⟩ := hQ.rich x y
    have h1 := congrFun (hQ.comm q hq s hs) x
    simp only [Function.comp] at h1
    rw [← hsx, h1, hqx]; rfl
  rwa [this] at hq

lemma comp_mem (hQ : IsPolicyFamily Q) {q q' : ↥X → ↥X} (hq : q ∈ Q) (hq' : q' ∈ Q) (x0 : ↥X) :
    q ∘ q' ∈ Q := by
  obtain ⟨r, hr, hrx⟩ := hQ.rich x0 (q (q' x0))
  have : r = q ∘ q' := by
    funext y
    obtain ⟨s, hs, hsx⟩ := hQ.rich x0 y
    have h1 := congrFun (hQ.comm r hr s hs) x0
    have h2 := congrFun (hQ.comm q hq s hs) (q' x0)
    have h3 := congrFun (hQ.comm q' hq' s hs) x0
    simp only [Function.comp] at h1 h2 h3 ⊢
    rw [← hsx, h1, hrx, ← h2, ← h3]
  rwa [this] at hr

lemma param_spec (hQ : IsPolicyFamily Q) (x0 y : ↥X) : param Q x0 y ∈ Q ∧ param Q x0 y x0 = y := by
  have h : ∃ q ∈ Q, q x0 = y := hQ.rich x0 y
  unfold param Intersectionality.Generic.transport
  rw [dif_pos h]
  exact Classical.choose_spec h

lemma param_mem (hQ : IsPolicyFamily Q) (x0 y : ↥X) : param Q x0 y ∈ Q := (param_spec hQ x0 y).1

lemma param_x0 (hQ : IsPolicyFamily Q) (x0 y : ↥X) : param Q x0 y x0 = y := (param_spec hQ x0 y).2

lemma eq_param (hQ : IsPolicyFamily Q) (x0 : ↥X) {q : ↥X → ↥X} (hq : q ∈ Q) : q = param Q x0 (q x0) :=
  uniq hQ hq (param_mem hQ x0 _) x0 (by rw [param_x0 hQ])

lemma param_self (hQ : IsPolicyFamily Q) (x0 : ↥X) : param Q x0 x0 = id :=
  uniq hQ (param_mem hQ x0 x0) (id_mem hQ x0) x0 (by rw [param_x0 hQ]; rfl)

lemma param_comm (hQ : IsPolicyFamily Q) (x0 a b : ↥X) (x : ↥X) :
    param Q x0 a (param Q x0 b x) = param Q x0 b (param Q x0 a x) := by
  have := congrFun (hQ.comm _ (param_mem hQ x0 a) _ (param_mem hQ x0 b)) x
  simpa only [Function.comp] using this

lemma param_symm (hQ : IsPolicyFamily Q) (x0 a b : ↥X) : param Q x0 a b = param Q x0 b a := by
  have := param_comm hQ x0 a b x0
  rwa [param_x0 hQ, param_x0 hQ] at this

lemma param_strictMono (hQ : IsPolicyFamily Q) (x0 a : ↥X) : StrictMono (param Q x0 a) :=
  hQ.strictMono _ (param_mem hQ x0 a)

lemma param_strictMono_left (hQ : IsPolicyFamily Q) (x0 x : ↥X) :
    StrictMono (fun a => param Q x0 a x) := by
  intro a b hab
  simp only
  rw [param_symm hQ x0 a x, param_symm hQ x0 b x]
  exact param_strictMono hQ x0 x hab

lemma param_continuous (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 a : ↥X) :
    Continuous (param Q x0 a) := by
  haveI := hX
  exact (StrictMono.orderIsoOfSurjective _ (hQ.strictMono _ (param_mem hQ x0 a))
    (hQ.bijective _ (param_mem hQ x0 a)).2).continuous

lemma mem_continuous (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) {q : ↥X → ↥X}
    (hq : q ∈ Q) : Continuous q := by
  haveI := hX
  exact (StrictMono.orderIsoOfSurjective q (hQ.strictMono q hq) (hQ.bijective q hq).2).continuous

/-- Points strictly between. -/
lemma upper_aux (hX : X.OrdConnected) (g : ↥X → ↥X) (a u : ↥X) (hg : ContinuousAt g a)
    (hu : g a < u) : ∃ c, a ≤ c ∧ g c < u ∧ Iic c ∈ 𝓝 a := by
  haveI := hX
  by_cases hd : ∃ d, a < d
  · have hs : {y | g y < u} ∈ 𝓝 a := hg (Iio_mem_nhds hu)
    obtain ⟨d', hd', hsub⟩ := exists_Ico_subset_of_mem_nhds hs hd
    obtain ⟨c, hac, hcd⟩ := exists_between hd'
    exact ⟨c, hac.le, hsub ⟨hac.le, hcd⟩, mem_of_superset (Iio_mem_nhds hac) Iio_subset_Iic_self⟩
  · push_neg at hd
    refine ⟨a, le_rfl, hu, ?_⟩
    have : Iic a = univ := eq_univ_of_forall hd
    rw [this]; exact univ_mem

lemma lower_aux (hX : X.OrdConnected) (g : ↥X → ↥X) (a l : ↥X) (hg : ContinuousAt g a)
    (hl : l < g a) : ∃ c, c ≤ a ∧ l < g c ∧ Ici c ∈ 𝓝 a := by
  haveI := hX
  by_cases hd : ∃ d, d < a
  · have hs : {y | l < g y} ∈ 𝓝 a := hg (Ioi_mem_nhds hl)
    obtain ⟨d', hd', hsub⟩ := exists_Ioc_subset_of_mem_nhds hs hd
    obtain ⟨c, hdc, hca⟩ := exists_between hd'
    exact ⟨c, hca.le, hsub ⟨hdc, hca.le⟩, mem_of_superset (Ioi_mem_nhds hca) Ioi_subset_Ici_self⟩
  · push_neg at hd
    refine ⟨a, le_rfl, hl, ?_⟩
    have : Ici a = univ := eq_univ_of_forall hd
    rw [this]; exact univ_mem

lemma joint_continuous (hX : X.OrdConnected) (f : ↥X → ↥X → ↥X)
    (hm1 : ∀ b, Monotone (fun a => f a b)) (hm2 : ∀ a, Monotone (f a))
    (hc1 : ∀ b, Continuous (fun a => f a b)) (hc2 : ∀ a, Continuous (f a)) :
    Continuous (fun p : ↥X × ↥X => f p.1 p.2) := by
  haveI := hX
  rw [continuous_iff_continuousAt]
  rintro ⟨a, b⟩
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · obtain ⟨c, hca, hlc, hc⟩ := lower_aux hX (fun a => f a b) a l (hc1 b).continuousAt hl
    obtain ⟨d, hdb, hld, hd⟩ := lower_aux hX (f c) b l (hc2 c).continuousAt hlc
    have : Ici c ×ˢ Ici d ∈ 𝓝 (a, b) := prod_mem_nhds hc hd
    filter_upwards [this] with p hp
    exact lt_of_lt_of_le hld ((hm1 d hp.1).trans (hm2 p.1 hp.2))
  · obtain ⟨c, hca, hlc, hc⟩ := upper_aux hX (fun a => f a b) a u (hc1 b).continuousAt hu
    obtain ⟨d, hdb, hld, hd⟩ := upper_aux hX (f c) b u (hc2 c).continuousAt hlc
    have : Iic c ×ˢ Iic d ∈ 𝓝 (a, b) := prod_mem_nhds hc hd
    filter_upwards [this] with p hp
    exact lt_of_le_of_lt ((hm2 p.1 hp.2).trans (hm1 d hp.1)) hld

lemma param_joint (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) :
    Continuous (fun p : ↥X × ↥X => param Q x0 p.1 p.2) := by
  refine joint_continuous hX (param Q x0) (fun b => (param_strictMono_left hQ x0 b).monotone)
    (fun a => (param_strictMono hQ x0 a).monotone) (fun b => ?_) (param_continuous hX hQ x0)
  have : (fun a => param Q x0 a b) = param Q x0 b := by
    funext a; exact param_symm hQ x0 a b
  rw [this]; exact param_continuous hX hQ x0 b

end Alg

section Grp
variable {X : Set ℝ} {Q : Set (↥X → ↥X)} {n : ℕ}

/-- The foldr defining `grpMap`, over an arbitrary list of indices. -/
noncomputable def F (Q : Set (↥X → ↥X)) (x0 : ↥X) (θ : Fin n → ↥X) (g : Grp n) (L : List (Fin n)) :
    ↥X → ↥X :=
  L.foldr (fun i f => param Q x0 (if g i then θ i else x0) ∘ f) id

lemma grpMap_eq (x0 : ↥X) (θ : Fin n → ↥X) (g : Grp n) :
    grpMap Q x0 θ g = F Q x0 θ g (List.finRange n) := rfl

lemma F_cons (x0 : ↥X) (θ : Fin n → ↥X) (g : Grp n) (i : Fin n) (L : List (Fin n)) :
    F Q x0 θ g (i :: L) = param Q x0 (if g i then θ i else x0) ∘ F Q x0 θ g L := rfl

lemma F_mem (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) (g : Grp n) (L : List (Fin n)) :
    F Q x0 θ g L ∈ Q := by
  induction L with
  | nil => exact id_mem hQ x0
  | cons i L ih => rw [F_cons]; exact comp_mem hQ (param_mem hQ _ _) ih x0

lemma grpMap_mem (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) (g : Grp n) :
    grpMap Q x0 θ g ∈ Q := F_mem hQ x0 θ g _

lemma F_split (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) (g g' g'' : Grp n)
    (hs : IsGroupSum g g' g'') (L : List (Fin n)) :
    F Q x0 θ g L = F Q x0 θ g' L ∘ F Q x0 θ g'' L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have hi : param Q x0 (if g i then θ i else x0) =
        param Q x0 (if g' i then θ i else x0) ∘ param Q x0 (if g'' i then θ i else x0) := by
      have := hs i
      cases h1 : g' i <;> cases h2 : g'' i <;> cases h0 : g i <;>
        simp_all [Bool.toNat, param_self hQ x0]
    have hc : param Q x0 (if g'' i then θ i else x0) ∘ F Q x0 θ g' L =
        F Q x0 θ g' L ∘ param Q x0 (if g'' i then θ i else x0) :=
      hQ.comm _ (param_mem hQ _ _) _ (F_mem hQ x0 θ g' L)
    rw [F_cons, F_cons, F_cons, ih, hi]
    funext x
    have := congrFun hc (F Q x0 θ g'' L x)
    simp only [Function.comp] at this ⊢
    rw [this]

lemma grpMap_nonint (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) :
    IsNonintersectional (grpMap Q x0 θ) := by
  intro g g' g'' hs
  exact F_split hQ x0 θ g g' g'' hs _

lemma F_mono (hQ : IsPolicyFamily Q) (x0 : ↥X) {θ θ' : Fin n → ↥X} (h : θ ≤ θ') (g : Grp n)
    (L : List (Fin n)) (x : ↥X) : F Q x0 θ g L x ≤ F Q x0 θ' g L x := by
  induction L with
  | nil => exact le_rfl
  | cons i L ih =>
    rw [F_cons, F_cons]
    simp only [Function.comp]
    have hc : (if g i then θ i else x0) ≤ (if g i then θ' i else x0) := by
      split_ifs
      · exact h i
      · exact le_rfl
    exact ((param_strictMono_left hQ x0 _).monotone hc).trans ((param_strictMono hQ x0 _).monotone ih)

lemma grpMap_mono (hQ : IsPolicyFamily Q) (x0 : ↥X) {θ θ' : Fin n → ↥X} (h : θ ≤ θ') (g : Grp n)
    (x : ↥X) : grpMap Q x0 θ g x ≤ grpMap Q x0 θ' g x := F_mono hQ x0 h g _ x

lemma F_cont (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) (g : Grp n)
    (L : List (Fin n)) (x : ↥X) : Continuous (fun θ : Fin n → ↥X => F Q x0 θ g L x) := by
  induction L with
  | nil => exact continuous_const
  | cons i L ih =>
    simp only [F_cons, Function.comp]
    have hci : Continuous (fun θ : Fin n → ↥X => (if g i then θ i else x0)) := by
      split_ifs
      · exact continuous_apply i
      · exact continuous_const
    exact (param_joint hX hQ x0).comp (hci.prodMk ih)

lemma grpMap_cont (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) (g : Grp n) (x : ↥X) :
    Continuous (fun θ : Fin n → ↥X => grpMap Q x0 θ g x) := F_cont hX hQ x0 g _ x

end Grp

section Meas
variable {X : Set ℝ} {n : ℕ}

lemma mset_grp (g : Grp n) : MeasurableSet {z : ScoreGrp X n | z.2 = g} :=
  measurable_snd (measurableSet_singleton g)

lemma mset_acc (hX : X.OrdConnected) (g : Grp n) (xs : ↥X) {h : ↥X → ↥X} (hh : Monotone h) :
    MeasurableSet {z : ScoreGrp X n | z.2 = g ∧ xs ≤ h z.1} := by
  haveI := hX
  refine (mset_grp g).inter ?_
  exact measurable_fst (hh.measurable measurableSet_Ici)

/-- The fibre of a strictly monotone adjustment over a point is null. -/
lemma null_fibre (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n)
    {h : ↥X → ↥X} (hh : StrictMono h) (c : ↥X) :
    (p : Measure (ScoreGrp X n)) {z | z.2 = g ∧ h z.1 = c} = 0 := by
  set μ := (p : Measure (ScoreGrp X n))
  rcases (measureReal_nonneg : 0 ≤ μ.real {z : ScoreGrp X n | z.2 = g}).eq_or_lt with h0 | hpos
  · have : μ {z : ScoreGrp X n | z.2 = g} = 0 := (measureReal_eq_zero_iff).1 h0.symm
    exact measure_mono_null (fun z hz => hz.1) this
  · by_cases hex : ∃ x, h x = c
    · obtain ⟨x, hx⟩ := hex
      have h1 := (hp g hpos).1 x
      have h2 : μ {z : ScoreGrp X n | z.1 = x ∧ z.2 = g} = 0 := (measureReal_eq_zero_iff).1 h1
      refine measure_mono_null (fun z hz => ?_) h2
      exact ⟨hh.injective (hz.2.trans hx.symm), hz.1⟩
    · push_neg at hex
      have : {z : ScoreGrp X n | z.2 = g ∧ h z.1 = c} = ∅ := by
        ext z; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun _ => hex z.1
      rw [this, measure_empty]

/-- Continuity of accepted mass in parameters. -/
lemma acc_cont (hX : X.OrdConnected) {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n) (h : Y → ↥X → ↥X)
    (hmono : ∀ y, StrictMono (h y)) (hc : ∀ x, Continuous fun y => h y x) (xs : Y → ↥X)
    (hxs : Continuous xs) :
    Continuous (fun y => (p : Measure (ScoreGrp X n)).real {z | z.2 = g ∧ xs y ≤ h y z.1}) := by
  set μ := (p : Measure (ScoreGrp X n))
  rw [continuous_iff_continuousAt]
  intro y0
  have hN := null_fibre p hp g (hmono y0) (xs y0)
  have hae : ∀ᵐ z ∂μ, z ∉ {z : ScoreGrp X n | z.2 = g ∧ h y0 z.1 = xs y0} :=
    measure_eq_zero_iff_ae_notMem.1 hN
  have hlim : ∀ᵐ z ∂μ, ∀ᶠ y in 𝓝 y0, (z ∈ {z : ScoreGrp X n | z.2 = g ∧ xs y ≤ h y z.1} ↔
      z ∈ {z : ScoreGrp X n | z.2 = g ∧ xs y0 ≤ h y0 z.1}) := by
    filter_upwards [hae] with z hz
    simp only [mem_setOf_eq, not_and] at hz ⊢
    by_cases hzg : z.2 = g
    · have hne := hz hzg
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hev := ((hc z.1).continuousAt.tendsto).eventually_lt (hxs.continuousAt.tendsto) hlt
        filter_upwards [hev] with y hy
        simp only [hzg, true_and]
        exact ⟨fun h1 => absurd h1 (not_le.2 hy), fun h1 => absurd h1 (not_le.2 hlt)⟩
      · have hev := (hxs.continuousAt.tendsto).eventually_lt ((hc z.1).continuousAt.tendsto) hgt
        filter_upwards [hev] with y hy
        simp only [hzg, true_and]
        exact ⟨fun _ => hgt.le, fun _ => hy.le⟩
    · exact Eventually.of_forall fun y => by simp [hzg]
  have hmeas : ∀ y, MeasurableSet {z : ScoreGrp X n | z.2 = g ∧ xs y ≤ h y z.1} :=
    fun y => mset_acc hX g (xs y) (hmono y).monotone
  have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 y0) (hmeas y0) hmeas hlim
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this

lemma acc_anti (hX : X.OrdConnected) (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n)
    {h : ↥X → ↥X} {xs xs' : ↥X} (hle : xs ≤ xs') :
    (p : Measure (ScoreGrp X n)).real {z | z.2 = g ∧ xs' ≤ h z.1} ≤
      (p : Measure (ScoreGrp X n)).real {z | z.2 = g ∧ xs ≤ h z.1} :=
  measureReal_mono (fun z hz => ⟨hz.1, hle.trans hz.2⟩)

lemma acc_strict (hX : X.OrdConnected) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p)
    (g : Grp n) (hg : 0 < groupMass p g) {h : ↥X → ↥X} (hh : StrictMono h)
    (hs : Function.Surjective h) {xs xs' : ↥X} (hlt : xs < xs') :
    (p : Measure (ScoreGrp X n)).real {z | z.2 = g ∧ xs' ≤ h z.1} <
      (p : Measure (ScoreGrp X n)).real {z | z.2 = g ∧ xs ≤ h z.1} := by
  set μ := (p : Measure (ScoreGrp X n))
  obtain ⟨a, ha⟩ := hs xs
  obtain ⟨b, hb⟩ := hs xs'
  have hab : a < b := by
    rw [← ha, ← hb] at hlt; exact hh.lt_iff_lt.1 hlt
  have hD := (hp g hg).2 a b hab
  set D := {z : ScoreGrp X n | a < z.1 ∧ z.1 < b ∧ z.2 = g}
  have hDm : MeasurableSet D := by
    haveI := hX
    refine (measurable_fst measurableSet_Ioi).inter ((measurable_fst measurableSet_Iio).inter
      (mset_grp g))
  have hdisj : Disjoint {z : ScoreGrp X n | z.2 = g ∧ xs' ≤ h z.1} D := by
    rw [Set.disjoint_left]
    rintro z ⟨_, hz⟩ ⟨_, hzb, _⟩
    rw [← hb] at hz
    exact absurd (hh.le_iff_le.1 hz) (not_le.2 hzb)
  have hsub : {z : ScoreGrp X n | z.2 = g ∧ xs' ≤ h z.1} ∪ D ⊆
      {z : ScoreGrp X n | z.2 = g ∧ xs ≤ h z.1} := by
    rintro z (⟨hz1, hz2⟩ | ⟨hza, _, hzg⟩)
    · exact ⟨hz1, hlt.le.trans hz2⟩
    · refine ⟨hzg, ?_⟩
      rw [← ha]; exact hh.monotone hza.le
  have := measureReal_mono (μ := μ) hsub
  rw [measureReal_union hdisj hDm] at this
  linarith

lemma sum_groupMass (p : ProbabilityMeasure (ScoreGrp X n)) :
    ∑ g, groupMass p g = 1 := by
  unfold groupMass
  have := sum_measureReal_preimage_singleton (μ := (p : Measure (ScoreGrp X n)))
    (Finset.univ : Finset (Grp n)) (f := Prod.snd) (fun y _ => measurable_snd (measurableSet_singleton y))
  simp only [Finset.coe_univ, preimage_univ, probReal_univ] at this
  rw [← this]
  rfl

lemma exists_pos_group (p : ProbabilityMeasure (ScoreGrp X n)) : ∃ g, 0 < groupMass p g := by
  by_contra hcon
  push_neg at hcon
  have h1 := sum_groupMass p
  have : ∑ g, groupMass p g ≤ 0 := Finset.sum_nonpos (fun g _ => hcon g)
  linarith

end Meas

section Thr
variable {X : Set ℝ} {Q : Set (↥X → ↥X)} {n : ℕ}

lemma acc_cont_theta (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n) :
    Continuous (fun y : (Fin n → ↥X) × ↥X => accMass p (grpMap Q x0 y.1) y.2 g) :=
  acc_cont (Y := (Fin n → ↥X) × ↥X) hX p hp g (fun y => grpMap Q x0 y.1 g)
    (fun y => hQ.strictMono _ (grpMap_mem hQ x0 y.1 g))
    (fun x => (grpMap_cont hX hQ x0 g x).comp continuous_fst) Prod.snd continuous_snd

lemma total_cont (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) :
    Continuous (fun y : (Fin n → ↥X) × ↥X => totalRate p Q x0 y.1 y.2) := by
  unfold totalRate
  exact continuous_finsetSum _ (fun g _ => acc_cont_theta hX hQ x0 p hp g)

lemma total_strictAnti (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (θ : Fin n → ↥X) :
    StrictAnti (fun xs => totalRate p Q x0 θ xs) := by
  intro xs xs' hlt
  obtain ⟨g0, hg0⟩ := exists_pos_group p
  unfold totalRate
  refine Finset.sum_lt_sum (fun g _ => acc_anti hX p g hlt.le) ⟨g0, Finset.mem_univ _, ?_⟩
  exact acc_strict hX p hp g0 hg0 (hQ.strictMono _ (grpMap_mem hQ x0 θ g0))
    (hQ.bijective _ (grpMap_mem hQ x0 θ g0)).2 hlt

lemma total_atBot (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (p : ProbabilityMeasure (ScoreGrp X n)) (θ : Fin n → ↥X) :
    Tendsto (fun xs => totalRate p Q x0 θ xs) atBot (𝓝 1) := by
  haveI := hX
  rw [← sum_groupMass p]
  unfold totalRate
  refine tendsto_finsetSum _ (fun g _ => ?_)
  have hmeas : ∀ xs : ↥X, MeasurableSet {z : ScoreGrp X n | z.2 = g ∧ xs ≤ grpMap Q x0 θ g z.1} :=
    fun xs => mset_acc hX g xs (hQ.strictMono _ (grpMap_mem hQ x0 θ g)).monotone
  have hlim : ∀ᵐ z ∂(p : Measure (ScoreGrp X n)), ∀ᶠ xs in (atBot : Filter ↥X),
      (z ∈ {z : ScoreGrp X n | z.2 = g ∧ xs ≤ grpMap Q x0 θ g z.1} ↔ z ∈ {z : ScoreGrp X n | z.2 = g}) := by
    refine ae_of_all _ (fun z => ?_)
    filter_upwards [eventually_le_atBot (grpMap Q x0 θ g z.1)] with xs hxs
    exact ⟨fun h => h.1, fun h => ⟨h, hxs⟩⟩
  have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atBot (mset_grp g) hmeas hlim
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this

lemma total_atTop (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (θ : Fin n → ↥X) :
    Tendsto (fun xs => totalRate p Q x0 θ xs) atTop (𝓝 0) := by
  haveI := hX
  have h0 : (0 : ℝ) = ∑ _g : Grp n, (0 : ℝ) := by simp
  rw [h0]
  unfold totalRate
  refine tendsto_finsetSum _ (fun g _ => ?_)
  have hmeas : ∀ xs : ↥X, MeasurableSet {z : ScoreGrp X n | z.2 = g ∧ xs ≤ grpMap Q x0 θ g z.1} :=
    fun xs => mset_acc hX g xs (hQ.strictMono _ (grpMap_mem hQ x0 θ g)).monotone
  have hlim : ∀ᵐ z ∂(p : Measure (ScoreGrp X n)), ∀ᶠ xs in (atTop : Filter ↥X),
      (z ∈ {z : ScoreGrp X n | z.2 = g ∧ xs ≤ grpMap Q x0 θ g z.1} ↔ z ∈ (∅ : Set (ScoreGrp X n))) := by
    by_cases htop : ∃ T : ↥X, IsTop T
    · obtain ⟨T, hT⟩ := htop
      have hN := null_fibre p hp g (hQ.strictMono _ (grpMap_mem hQ x0 θ g)) T
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with z hz
      simp only [mem_setOf_eq, not_and] at hz
      by_cases hzg : z.2 = g
      · have hlt : grpMap Q x0 θ g z.1 < T := lt_of_le_of_ne (hT _) (hz hzg)
        filter_upwards [eventually_ge_atTop T] with xs hxs
        simp only [mem_empty_iff_false, iff_false]
        exact fun h => absurd (lt_of_lt_of_le hlt hxs) (not_lt.2 h.2)
      · exact Eventually.of_forall fun xs => by simp [hzg]
    · refine ae_of_all _ (fun z => ?_)
      have hnt : ¬ IsTop (grpMap Q x0 θ g z.1) := fun h => htop ⟨_, h⟩
      simp only [IsTop, not_forall, not_le] at hnt
      obtain ⟨T, hT⟩ := hnt
      filter_upwards [eventually_ge_atTop T] with xs hxs
      simp only [mem_empty_iff_false, iff_false]
      exact fun h => absurd (lt_of_lt_of_le hT hxs) (not_lt.2 h.2)
  have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hmeas hlim
  have := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  rw [measure_empty, ENNReal.toReal_zero] at this
  exact this

lemma thr_exists_unique (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p)
    (θ : Fin n → ↥X) : ∃! xs : ↥X, totalRate p Q x0 θ xs = α := by
  haveI := hX
  haveI : Nonempty ↥X := ⟨x0⟩
  obtain ⟨lo, hlo⟩ := ((total_atBot hX hQ x0 p θ).eventually (lt_mem_nhds hα1)).exists
  obtain ⟨hi, hhi⟩ := ((total_atTop hX hQ x0 p hp θ).eventually (gt_mem_nhds hα0)).exists
  have hcont : Continuous (fun xs => totalRate p Q x0 θ xs) :=
    (total_cont hX hQ x0 p hp).comp (continuous_const.prodMk continuous_id)
  haveI : PreconnectedSpace ↥X := Subtype.preconnectedSpace hX.isPreconnected
  obtain ⟨xs, hxs⟩ := intermediate_value_univ hi lo hcont ⟨hhi.le, hlo.le⟩
  refine ⟨xs, hxs, fun y hy => ?_⟩
  exact (total_strictAnti hX hQ x0 p hp θ).injective (hy.trans hxs.symm)

lemma thr_spec (hX : X.OrdConnected) [Nonempty ↥X] (hQ : IsPolicyFamily Q) (x0 : ↥X) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p)
    (θ : Fin n → ↥X) : totalRate p Q x0 θ (thr p Q x0 α θ) = α := by
  obtain ⟨xs, hxs, _⟩ := thr_exists_unique hX hQ x0 hα0 hα1 p hp θ
  exact Classical.epsilon_spec (p := fun xs => totalRate p Q x0 θ xs = α) ⟨xs, hxs⟩

lemma thr_cont (hX : X.OrdConnected) [Nonempty ↥X] (hQ : IsPolicyFamily Q) (x0 : ↥X) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) :
    Continuous (fun θ => thr p Q x0 α θ) := by
  haveI := hX
  rw [continuous_iff_continuousAt]
  intro θ0
  have hspec := thr_spec hX hQ x0 hα0 hα1 p hp
  have hanti := total_strictAnti hX hQ x0 p hp
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have h1 : α < totalRate p Q x0 θ0 l := by
      rw [← hspec θ0]; exact hanti θ0 hl
    have hc : Continuous (fun θ => totalRate p Q x0 θ l) :=
      (total_cont hX hQ x0 p hp).comp (continuous_id.prodMk continuous_const)
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds h1)] with θ hθ
    by_contra hle
    push_neg at hle
    have := (hanti θ).antitone hle
    rw [hspec θ] at this
    linarith
  · have h1 : totalRate p Q x0 θ0 u < α := by
      rw [← hspec θ0]; exact hanti θ0 hu
    have hc : Continuous (fun θ => totalRate p Q x0 θ u) :=
      (total_cont hX hQ x0 p hp).comp (continuous_id.prodMk continuous_const)
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds h1)] with θ hθ
    by_contra hle
    push_neg at hle
    have := (hanti θ).antitone hle
    rw [hspec θ] at this
    linarith

lemma catRate_thr_cont (hX : X.OrdConnected) [Nonempty ↥X] (hQ : IsPolicyFamily Q) (x0 : ↥X) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (i : Fin n) :
    Continuous (fun θ => catRate p Q x0 θ (thr p Q x0 α θ) i) := by
  unfold catRate
  refine Continuous.div_const ?_ _
  refine continuous_finsetSum _ (fun g _ => ?_)
  exact (acc_cont_theta hX hQ x0 p hp g).comp
    (continuous_id.prodMk (thr_cont hX hQ x0 hα0 hα1 p hp))

end Thr

section Weak
variable {X : Set ℝ} {Q : Set (↥X → ↥X)} {n : ℕ}

lemma real_tendsto_of_null_frontier {ι : Type*} {L : Filter ι}
    {ps : ι → ProbabilityMeasure (ScoreGrp X n)} {p : ProbabilityMeasure (ScoreGrp X n)}
    (h : Tendsto ps L (𝓝 p)) {E : Set (ScoreGrp X n)} (hE : (p : Measure (ScoreGrp X n)) (frontier E) = 0) :
    Tendsto (fun i => (ps i : Measure (ScoreGrp X n)).real E) L
      (𝓝 ((p : Measure (ScoreGrp X n)).real E)) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hE)

lemma isClopen_grp (g : Grp n) : IsClopen {z : ScoreGrp X n | z.2 = g} :=
  (isClopen_discrete {g}).preimage continuous_snd

lemma frontier_acc {h : ↥X → ↥X} (hc : Continuous h) (g : Grp n) (xs : ↥X) :
    frontier {z : ScoreGrp X n | z.2 = g ∧ xs ≤ h z.1} ⊆ {z | z.2 = g ∧ h z.1 = xs} := by
  have e : {z : ScoreGrp X n | z.2 = g ∧ xs ≤ h z.1} =
      {z : ScoreGrp X n | z.2 = g} ∩ {z | xs ≤ h z.1} := rfl
  rw [e]
  refine (frontier_inter_subset _ _).trans ?_
  rw [(isClopen_grp (X := X) g).frontier_eq, (isClopen_grp (X := X) g).isClosed.closure_eq]
  rintro z (⟨hz, _⟩ | ⟨hz1, hz2⟩)
  · exact absurd hz (Set.notMem_empty z)
  · have := frontier_le_subset_eq (continuous_const (y := xs)) (hc.comp continuous_fst) hz2
    exact ⟨hz1, this.symm⟩

lemma corner_up (hX : X.OrdConnected) {a : ↥X} {U : Set ↥X} (hU : U ∈ 𝓝 a) :
    ∃ c ∈ U, Iic c ∈ 𝓝 a := by
  haveI := hX
  by_cases hd : ∃ d, a < d
  · obtain ⟨d', hd', hsub⟩ := exists_Ico_subset_of_mem_nhds hU hd
    obtain ⟨c, hac, hcd⟩ := exists_between hd'
    exact ⟨c, hsub ⟨hac.le, hcd⟩, mem_of_superset (Iio_mem_nhds hac) Iio_subset_Iic_self⟩
  · push_neg at hd
    refine ⟨a, mem_of_mem_nhds hU, ?_⟩
    have : Iic a = univ := eq_univ_of_forall hd
    rw [this]; exact univ_mem

lemma corner_down (hX : X.OrdConnected) {a : ↥X} {U : Set ↥X} (hU : U ∈ 𝓝 a) :
    ∃ c ∈ U, Ici c ∈ 𝓝 a := by
  haveI := hX
  by_cases hd : ∃ d, d < a
  · obtain ⟨d', hd', hsub⟩ := exists_Ioc_subset_of_mem_nhds hU hd
    obtain ⟨c, hdc, hca⟩ := exists_between hd'
    exact ⟨c, hsub ⟨hdc, hca.le⟩, mem_of_superset (Ioi_mem_nhds hca) Ioi_subset_Ici_self⟩
  · push_neg at hd
    refine ⟨a, mem_of_mem_nhds hU, ?_⟩
    have : Ici a = univ := eq_univ_of_forall hd
    rw [this]; exact univ_mem

lemma corner_pi_up (hX : X.OrdConnected) {θ0 : Fin n → ↥X} {V : Set (Fin n → ↥X)} (hV : V ∈ 𝓝 θ0) :
    ∃ c ∈ V, Iic c ∈ 𝓝 θ0 := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, _, t, ht, hsub⟩ := hV
  choose c hc hcn using fun j => corner_up hX (ht j)
  refine ⟨c, hsub (fun j _ => hc j), ?_⟩
  have : Iic c = univ.pi (fun j => Iic (c j)) := by
    ext θ; simp [Pi.le_def]
  rw [this]
  exact set_pi_mem_nhds finite_univ (fun j _ => hcn j)

lemma corner_pi_down (hX : X.OrdConnected) {θ0 : Fin n → ↥X} {V : Set (Fin n → ↥X)} (hV : V ∈ 𝓝 θ0) :
    ∃ c ∈ V, Ici c ∈ 𝓝 θ0 := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, _, t, ht, hsub⟩ := hV
  choose c hc hcn using fun j => corner_down hX (ht j)
  refine ⟨c, hsub (fun j _ => hc j), ?_⟩
  have : Ici c = univ.pi (fun j => Ici (c j)) := by
    ext θ; simp [Pi.le_def]
  rw [this]
  exact set_pi_mem_nhds finite_univ (fun j _ => hcn j)

/-- Joint continuity of the accepted mass in `(p, θ, x*)` at a distribution of `P`. -/
lemma acc_joint (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (pbar : ProbabilityMeasure (ScoreGrp X n)) (hp : InP pbar) (g : Grp n)
    (y0 : (Fin n → ↥X) × ↥X) :
    ContinuousAt (fun w : ProbabilityMeasure (ScoreGrp X n) × ((Fin n → ↥X) × ↥X) =>
      accMass w.1 (grpMap Q x0 w.2.1) w.2.2 g) (pbar, y0) := by
  have hcont := (acc_cont_theta hX hQ x0 pbar hp g).continuousAt (x := y0)
  have hmono : ∀ {θ θ' : Fin n → ↥X} {xs xs' : ↥X}, θ ≤ θ' → xs' ≤ xs →
      {z : ScoreGrp X n | z.2 = g ∧ xs ≤ grpMap Q x0 θ g z.1} ⊆
        {z : ScoreGrp X n | z.2 = g ∧ xs' ≤ grpMap Q x0 θ' g z.1} := by
    intro θ θ' xs xs' hθ hxs z hz
    exact ⟨hz.1, hxs.trans (hz.2.trans (grpMap_mono hQ x0 hθ g z.1))⟩
  have hfr : ∀ θ xs, (pbar : Measure (ScoreGrp X n))
      (frontier {z : ScoreGrp X n | z.2 = g ∧ xs ≤ grpMap Q x0 θ g z.1}) = 0 := by
    intro θ xs
    exact measure_mono_null (frontier_acc (mem_continuous hX hQ x0 (grpMap_mem hQ x0 θ g)) g xs)
      (null_fibre pbar hp g (hQ.strictMono _ (grpMap_mem hQ x0 θ g)) xs)
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have hV : {y : (Fin n → ↥X) × ↥X | l < accMass pbar (grpMap Q x0 y.1) y.2 g} ∈ 𝓝 y0 :=
      hcont.eventually (Ioi_mem_nhds hl)
    rw [nhds_prod_eq] at hV
    obtain ⟨V1, hV1, V2, hV2, hsub⟩ := Filter.mem_prod_iff.1 hV
    obtain ⟨c1, hc1, hc1n⟩ := corner_pi_down hX hV1
    obtain ⟨c2, hc2, hc2n⟩ := corner_up hX hV2
    have hlc : l < accMass pbar (grpMap Q x0 c1) c2 g := hsub (Set.mk_mem_prod hc1 hc2)
    have hev := (real_tendsto_of_null_frontier (L := 𝓝 pbar) tendsto_id (hfr c1 c2)).eventually
      (Ioi_mem_nhds hlc)
    have hbox : Ici c1 ×ˢ Iic c2 ∈ 𝓝 y0 := by
      rw [nhds_prod_eq]; exact prod_mem_prod hc1n hc2n
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod hev hbox] with w hw
    obtain ⟨hw1, hw2, hw3⟩ := hw
    exact lt_of_lt_of_le hw1 (measureReal_mono (hmono hw2 hw3))
  · have hV : {y : (Fin n → ↥X) × ↥X | accMass pbar (grpMap Q x0 y.1) y.2 g < u} ∈ 𝓝 y0 :=
      hcont.eventually (Iio_mem_nhds hu)
    rw [nhds_prod_eq] at hV
    obtain ⟨V1, hV1, V2, hV2, hsub⟩ := Filter.mem_prod_iff.1 hV
    obtain ⟨c1, hc1, hc1n⟩ := corner_pi_up hX hV1
    obtain ⟨c2, hc2, hc2n⟩ := corner_down hX hV2
    have hlc : accMass pbar (grpMap Q x0 c1) c2 g < u := hsub (Set.mk_mem_prod hc1 hc2)
    have hev := (real_tendsto_of_null_frontier (L := 𝓝 pbar) tendsto_id (hfr c1 c2)).eventually
      (Iio_mem_nhds hlc)
    have hbox : Iic c1 ×ˢ Ici c2 ∈ 𝓝 y0 := by
      rw [nhds_prod_eq]; exact prod_mem_prod hc1n hc2n
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod hev hbox] with w hw
    obtain ⟨hw1, hw2, hw3⟩ := hw
    exact lt_of_le_of_lt (measureReal_mono (hmono hw2 hw3)) hw1

end Weak

section Joint
variable {X : Set ℝ} {Q : Set (↥X → ↥X)} {n : ℕ}

lemma total_joint (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X)
    (pbar : ProbabilityMeasure (ScoreGrp X n)) (hp : InP pbar) (θ0 : Fin n → ↥X) (xs : ↥X) :
    ContinuousAt (fun w : ProbabilityMeasure (ScoreGrp X n) × (Fin n → ↥X) =>
      totalRate w.1 Q x0 w.2 xs) (pbar, θ0) := by
  unfold totalRate
  refine tendsto_finsetSum _ (fun g _ => ?_)
  exact (acc_joint hX hQ x0 pbar hp g (θ0, xs)).comp_of_eq
    (by fun_prop : Continuous fun w : ProbabilityMeasure (ScoreGrp X n) × (Fin n → ↥X) =>
      (w.1, (w.2, xs))).continuousAt rfl

lemma thr_joint (hX : X.OrdConnected) [Nonempty ↥X] (hQ : IsPolicyFamily Q) (x0 : ↥X) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (pbar : DistSpace X n) (θ0 : Fin n → ↥X) :
    ContinuousAt (fun w : DistSpace X n × (Fin n → ↥X) => thr w.1.1 Q x0 α w.2) (pbar, θ0) := by
  haveI := hX
  have hc : ∀ xs : ↥X, ContinuousAt (fun w : DistSpace X n × (Fin n → ↥X) =>
      totalRate w.1.1 Q x0 w.2 xs) (pbar, θ0) := fun xs =>
    ContinuousAt.comp (f := fun w : DistSpace X n × (Fin n → ↥X) => (w.1.1, w.2))
      (g := fun w : ProbabilityMeasure (ScoreGrp X n) × (Fin n → ↥X) => totalRate w.1 Q x0 w.2 xs)
      (total_joint hX hQ x0 pbar.1 pbar.2 θ0 xs)
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
  refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
  · have h1 : α < totalRate pbar.1 Q x0 θ0 l := by
      rw [← thr_spec hX hQ x0 hα0 hα1 pbar.1 pbar.2 θ0]
      exact total_strictAnti hX hQ x0 pbar.1 pbar.2 θ0 hl
    filter_upwards [(hc l).eventually (lt_mem_nhds h1)] with w hw
    by_contra hle
    push_neg at hle
    have := (total_strictAnti hX hQ x0 w.1.1 w.1.2 w.2).antitone hle
    rw [thr_spec hX hQ x0 hα0 hα1 w.1.1 w.1.2 w.2] at this
    linarith
  · have h1 : totalRate pbar.1 Q x0 θ0 u < α := by
      rw [← thr_spec hX hQ x0 hα0 hα1 pbar.1 pbar.2 θ0]
      exact total_strictAnti hX hQ x0 pbar.1 pbar.2 θ0 hu
    filter_upwards [(hc u).eventually (gt_mem_nhds h1)] with w hw
    by_contra hle
    push_neg at hle
    have := (total_strictAnti hX hQ x0 w.1.1 w.1.2 w.2).antitone hle
    rw [thr_spec hX hQ x0 hα0 hα1 w.1.1 w.1.2 w.2] at this
    linarith

lemma catMass_cont (i : Fin n) :
    Continuous (fun p : ProbabilityMeasure (ScoreGrp X n) => catMass p i) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hcl : IsClopen {z : ScoreGrp X n | z.2 i = true} :=
    (isClopen_discrete {g : Grp n | g i = true}).preimage continuous_snd
  have hE : (p : Measure (ScoreGrp X n)) (frontier {z : ScoreGrp X n | z.2 i = true}) = 0 := by
    rw [hcl.frontier_eq, measure_empty]
  exact real_tendsto_of_null_frontier (L := 𝓝 p) tendsto_id hE

lemma catRate_joint (hX : X.OrdConnected) [Nonempty ↥X] (hQ : IsPolicyFamily Q) (x0 : ↥X)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (pbar : DistSpace X n) (θ0 : Fin n → ↥X) (i : Fin n)
    (hm : catMass pbar.1 i ≠ 0) :
    ContinuousAt (fun w : DistSpace X n × (Fin n → ↥X) =>
      catRate w.1.1 Q x0 w.2 (thr w.1.1 Q x0 α w.2) i) (pbar, θ0) := by
  unfold catRate
  have hin : ContinuousAt (fun w : DistSpace X n × (Fin n → ↥X) =>
      (w.1.1, (w.2, thr w.1.1 Q x0 α w.2))) (pbar, θ0) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
      (continuous_snd.continuousAt.prodMk (thr_joint hX hQ x0 hα0 hα1 pbar θ0))
  refine ContinuousAt.div ?_ ?_ hm
  · refine tendsto_finsetSum _ (fun g _ => ?_)
    exact ContinuousAt.comp (f := fun w : DistSpace X n × (Fin n → ↥X) =>
      (w.1.1, (w.2, thr w.1.1 Q x0 α w.2)))
      (g := fun w : ProbabilityMeasure (ScoreGrp X n) × ((Fin n → ↥X) × ↥X) =>
        accMass w.1 (grpMap Q x0 w.2.1) w.2.2 g)
      (acc_joint hX hQ x0 pbar.1 pbar.2 g (θ0, thr pbar.1 Q x0 α θ0)) hin
  · exact ((catMass_cont i).comp (continuous_subtype_val.comp continuous_fst)).continuousAt

end Joint

section Mono
variable {X : Set ℝ} {Q : Set (↥X → ↥X)} {n : ℕ}

lemma F_zero (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) (L : List (Fin n)) :
    F Q x0 θ (zeroGrp n) L = id := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [F_cons, ih]
    simp [zeroGrp, param_self hQ x0]

lemma F_unit (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) (k : Fin n) (L : List (Fin n))
    (hL : L.Nodup) : F Q x0 θ (unitGrp k) L = if k ∈ L then param Q x0 (θ k) else id := by
  induction L with
  | nil => simp [F]
  | cons i L ih =>
    rw [F_cons, ih (List.nodup_cons.1 hL).2]
    by_cases hik : i = k
    · subst hik
      have hnot : i ∉ L := (List.nodup_cons.1 hL).1
      simp [unitGrp, hnot]
    · have hki : k ≠ i := fun h => hik h.symm
      simp only [unitGrp, decide_eq_true_eq, hik, if_false, param_self hQ x0, List.mem_cons, hki,
        false_or]
      rfl

lemma grpMap_zero (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) :
    grpMap Q x0 θ (zeroGrp n) = id := F_zero hQ x0 θ _

lemma grpMap_unit (hQ : IsPolicyFamily Q) (x0 : ↥X) (θ : Fin n → ↥X) (k : Fin n) :
    grpMap Q x0 θ (unitGrp k) = param Q x0 (θ k) := by
  rw [grpMap_eq, F_unit hQ x0 θ k _ (List.nodup_finRange n)]
  simp

lemma total_mono_theta (hQ : IsPolicyFamily Q) (x0 : ↥X) (p : ProbabilityMeasure (ScoreGrp X n))
    {θ θ' : Fin n → ↥X} (h : θ ≤ θ') (xs : ↥X) :
    totalRate p Q x0 θ xs ≤ totalRate p Q x0 θ' xs := by
  unfold totalRate accMass
  exact Finset.sum_le_sum (fun g _ => measureReal_mono
    (fun z hz => ⟨hz.1, hz.2.trans (grpMap_mono hQ x0 h g z.1)⟩))

lemma thr_mono (hX : X.OrdConnected) [Nonempty ↥X] (hQ : IsPolicyFamily Q) (x0 : ↥X) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p)
    {θ θ' : Fin n → ↥X} (h : θ ≤ θ') : thr p Q x0 α θ ≤ thr p Q x0 α θ' := by
  by_contra hlt
  push_neg at hlt
  have h1 : totalRate p Q x0 θ' (thr p Q x0 α θ) < totalRate p Q x0 θ' (thr p Q x0 α θ') :=
    total_strictAnti hX hQ x0 p hp θ' hlt
  have h2 := total_mono_theta hQ x0 p h (thr p Q x0 α θ)
  rw [thr_spec hX hQ x0 hα0 hα1 p hp θ'] at h1
  rw [thr_spec hX hQ x0 hα0 hα1 p hp θ] at h2
  linarith

end Mono

end IsectCore

open IsectCore


open MeasureTheory Filter Topology Set ProbabilityTheory

namespace IsectNu

lemma exists_nu (X : Set ℝ) (hX : X.OrdConnected) (hXnt : X.Nontrivial) :
    ∃ ν : Measure ↥X, IsProbabilityMeasure ν ∧ (∀ y : ↥X, ν {y} = 0) ∧
      (∀ a b : ↥X, a < b → 0 < ν (Ioo a b)) := by
  have hXm : MeasurableSet X := hX.measurableSet
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : ∀ a b : ℝ, a < b → γ (Ioo a b) ≠ 0 := by
    intro a b hab h0
    have := (gaussianReal_absolutelyContinuous' 0 hv) h0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    linarith
  have hnull : ∀ y : ℝ, γ {y} = 0 := by
    intro y
    haveI := nullSingletonClass_gaussianReal (μ := 0) hv
    exact measure_singleton y
  have hemb : MeasurableEmbedding (Subtype.val : ↥X → ℝ) := MeasurableEmbedding.subtype_coe hXm
  set ν0 : Measure ↥X := Measure.comap Subtype.val γ with hν0
  have hν0 : ∀ s : Set ↥X, ν0 s = γ (Subtype.val '' s) := fun s => hemb.comap_apply γ s
  obtain ⟨x1, hx1, x2, hx2, hne⟩ := hXnt
  have hlt : ∃ u v : ℝ, u < v ∧ u ∈ X ∧ v ∈ X := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x1, x2, h, hx1, hx2⟩
    · exact ⟨x2, x1, h, hx2, hx1⟩
  obtain ⟨u, v, huv, hu, hv'⟩ := hlt
  have hIoo : ∀ a b : ↥X, Subtype.val '' (Ioo a b) = Ioo (a : ℝ) b := by
    intro a b
    ext t
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨t, hX.out a.2 b.2 ⟨h1.le, h2.le⟩⟩, ⟨h1, h2⟩, rfl⟩
  have huniv_pos : ν0 univ ≠ 0 := by
    intro h0
    have hsub : Ioo (⟨u, hu⟩ : ↥X) ⟨v, hv'⟩ ⊆ univ := subset_univ _
    have := measure_mono_null hsub h0
    rw [hν0, hIoo] at this
    exact hpos u v huv this
  have huniv_fin : ν0 univ ≠ ⊤ := by
    rw [hν0]; exact measure_ne_top _ _
  refine ⟨(ν0 univ)⁻¹ • ν0, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel huniv_pos huniv_fin]
  · intro y
    rw [Measure.smul_apply, hν0 {y}, image_singleton, hnull, smul_zero]
  · intro a b hab
    rw [Measure.smul_apply, hν0 (Ioo a b), hIoo, smul_eq_mul]
    refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 huniv_fin) (hpos _ _ hab)

end IsectNu

open MeasureTheory Filter Topology Set
open Intersectionality.Generic Intersectionality.Reductive

namespace IsectL4
open IsectCore

variable {X : Set ℝ} {n : ℕ}

noncomputable def pbarM (ν : Measure ↥X) (h0 : ↥X → ↥X) (n : ℕ) : Measure (ScoreGrp X n) :=
  ENNReal.ofReal (1/2) • ν.map (fun x => (h0 x, zeroGrp n)) +
    ∑ k : Fin n, ENNReal.ofReal (1/(2*n)) • ν.map (fun x => (x, unitGrp k))

lemma pbarM_apply (ν : Measure ↥X) {h0 : ↥X → ↥X} (hh0 : Measurable h0) {A : Set (ScoreGrp X n)}
    (hA : MeasurableSet A) :
    pbarM ν h0 n A = ENNReal.ofReal (1/2) * ν ((fun x => (h0 x, zeroGrp n)) ⁻¹' A) +
      ∑ k : Fin n, ENNReal.ofReal (1/(2*n)) * ν ((fun x => (x, unitGrp k)) ⁻¹' A) := by
  unfold pbarM
  rw [Measure.add_apply, Measure.smul_apply, Measure.map_apply (hh0.prodMk measurable_const) hA,
    Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Measure.smul_apply, Measure.map_apply measurable_prodMk_right hA, smul_eq_mul]

lemma pbarM_real (ν : Measure ↥X) [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0)
    {A : Set (ScoreGrp X n)} (hA : MeasurableSet A) :
    (pbarM ν h0 n).real A = (1/2) * ν.real ((fun x => (h0 x, zeroGrp n)) ⁻¹' A) +
      ∑ k : Fin n, (1/(2*n)) * ν.real ((fun x => (x, unitGrp k)) ⁻¹' A) := by
  rw [measureReal_def, pbarM_apply ν hh0 hA, ENNReal.toReal_add, ENNReal.toReal_sum,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  · congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  · intro k _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · exact (ENNReal.sum_lt_top.2 (fun k _ =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))).ne

lemma pbarM_prob (ν : Measure ↥X) [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0)
    (hn : 1 ≤ n) : IsProbabilityMeasure (pbarM ν h0 n) := by
  constructor
  rw [pbarM_apply ν hh0 MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have : (1 : ℝ) / 2 + n * (1 / (2 * n)) = 1 := by field_simp; ring
  rw [this, ENNReal.ofReal_one]

lemma real_ite (ν : Measure ↥X) (c g : Grp n) (P : Grp n → ↥X → Prop) :
    ν.real {x | c = g ∧ P g x} = if c = g then ν.real {x | P c x} else 0 := by
  by_cases h : c = g
  · subst h; simp
  · simp [h]

variable {Q : Set (↥X → ↥X)}

lemma pbar_acc (hX : X.OrdConnected) (ν : Measure ↥X) [IsProbabilityMeasure ν] {h0 : ↥X → ↥X}
    (hh0 : Measurable h0) (hn : 1 ≤ n) (q : Grp n → ↥X → ↥X) (hq : ∀ g, Monotone (q g))
    (t : ↥X) (g : Grp n) :
    accMass (⟨pbarM ν h0 n, pbarM_prob ν hh0 hn⟩ : ProbabilityMeasure (ScoreGrp X n)) q t g =
      (1/2) * (if zeroGrp n = g then ν.real {x | t ≤ q (zeroGrp n) (h0 x)} else 0) +
      ∑ k : Fin n, (1/(2*n)) * (if unitGrp k = g then ν.real {x | t ≤ q (unitGrp k) x} else 0) := by
  unfold accMass
  rw [ProbabilityMeasure.coe_mk, pbarM_real ν hh0 (mset_acc hX g t (hq g))]
  rw [← real_ite ν (zeroGrp n) g (fun g x => t ≤ q g (h0 x))]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← real_ite ν (unitGrp k) g (fun g x => t ≤ q g x)]
  rfl

noncomputable def pbarP (ν : Measure ↥X) [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0)
    (hn : 1 ≤ n) : ProbabilityMeasure (ScoreGrp X n) := ⟨pbarM ν h0 n, pbarM_prob ν hh0 hn⟩

lemma pbar_total (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) (ν : Measure ↥X)
    [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0) (hn : 1 ≤ n)
    (θ : Fin n → ↥X) (t : ↥X) :
    totalRate (pbarP ν hh0 hn) Q x0 θ t =
      (1/2) * ν.real {x | t ≤ grpMap Q x0 θ (zeroGrp n) (h0 x)} +
      ∑ k : Fin n, (1/(2*n)) * ν.real {x | t ≤ grpMap Q x0 θ (unitGrp k) x} := by
  unfold totalRate pbarP
  rw [Finset.sum_congr rfl (fun g _ => pbar_acc hX ν hh0 hn (grpMap Q x0 θ)
    (fun g => (hQ.strictMono _ (grpMap_mem hQ x0 θ g)).monotone) t g)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma pbar_catMass (ν : Measure ↥X) [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0)
    (hn : 1 ≤ n) (i : Fin n) : catMass (pbarP ν hh0 hn) i = 1/(2*n) := by
  unfold catMass pbarP
  have hm : MeasurableSet {z : ScoreGrp X n | z.2 i = true} :=
    measurable_snd (Set.toFinite {g : Grp n | g i = true}).measurableSet
  rw [ProbabilityMeasure.coe_mk, pbarM_real ν hh0 hm]
  have h1 : (fun x : ↥X => (h0 x, zeroGrp n)) ⁻¹' {z : ScoreGrp X n | z.2 i = true} = ∅ := by
    ext x; simp [zeroGrp]
  have h2 : ∀ k : Fin n, (fun x : ↥X => (x, unitGrp k)) ⁻¹' {z : ScoreGrp X n | z.2 i = true} =
      if i = k then univ else ∅ := by
    intro k; ext x; by_cases h : i = k <;> simp [unitGrp, h]
  rw [h1]
  simp only [h2, measureReal_empty, mul_zero, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · simp

lemma pbar_catRate (hX : X.OrdConnected) (hQ : IsPolicyFamily Q) (x0 : ↥X) (ν : Measure ↥X)
    [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0) (hn : 1 ≤ n)
    (θ : Fin n → ↥X) (t : ↥X) (i : Fin n) :
    catRate (pbarP ν hh0 hn) Q x0 θ t i = ν.real {x | t ≤ param Q x0 (θ i) x} := by
  unfold catRate
  rw [pbar_catMass ν hh0 hn i]
  have hnum : ∑ g ∈ Finset.univ.filter (fun g : Grp n => g i = true),
      accMass (pbarP ν hh0 hn) (grpMap Q x0 θ) t g =
      (1/(2*n)) * ν.real {x | t ≤ param Q x0 (θ i) x} := by
    unfold pbarP
    rw [Finset.sum_congr rfl (fun g _ => pbar_acc hX ν hh0 hn (grpMap Q x0 θ)
      (fun g => (hQ.strictMono _ (grpMap_mem hQ x0 θ g)).monotone) t g)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    have hz : (zeroGrp n) i = true ↔ False := by simp [zeroGrp]
    simp only [hz, if_false, mul_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · simp [unitGrp, grpMap_unit hQ x0 θ i]
    · intro k _ hk
      have : unitGrp k i = false := by simp [unitGrp, Ne.symm hk]
      simp [this]
    · simp
  rw [hnum]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  field_simp

lemma nu_fibre (ν : Measure ↥X) (hat : ∀ y : ↥X, ν {y} = 0) {h : ↥X → ↥X}
    (hinj : Function.Injective h) (y : ↥X) : ν {x | h x = y} = 0 := by
  by_cases hex : ∃ x, h x = y
  · obtain ⟨x, hx⟩ := hex
    have : {x | h x = y} = {x} := by
      ext z; simp only [mem_setOf_eq, mem_singleton_iff]
      exact ⟨fun hz => hinj (hz.trans hx.symm), fun hz => hz ▸ hx⟩
    rw [this, hat]
  · push_neg at hex
    have : {x | h x = y} = ∅ := by
      ext z; simp [hex z]
    rw [this, measure_empty]

lemma nu_Ioo_pos (ν : Measure ↥X) [IsProbabilityMeasure ν] (hsupp : ∀ a b : ↥X, a < b → 0 < ν (Ioo a b))
    {a b : ↥X} (hab : a < b) : 0 < ν.real (Ioo a b) :=
  ENNReal.toReal_pos (hsupp a b hab).ne' (measure_ne_top _ _)

lemma nu_preimage_Ioo (ν : Measure ↥X) [IsProbabilityMeasure ν]
    (hsupp : ∀ a b : ↥X, a < b → 0 < ν (Ioo a b)) {h : ↥X → ↥X} (hh : StrictMono h)
    (hs : Function.Surjective h) {a b : ↥X} (hab : a < b) :
    0 < ν.real {x | a < h x ∧ h x < b} := by
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  have : {x | h a' < h x ∧ h x < h b'} = Ioo a' b' := by
    ext x; simp [hh.lt_iff_lt]
  rw [this]
  exact nu_Ioo_pos ν hsupp (hh.lt_iff_lt.1 hab)

lemma nu_strict (hX : X.OrdConnected) (ν : Measure ↥X) [IsProbabilityMeasure ν]
    (hsupp : ∀ a b : ↥X, a < b → 0 < ν (Ioo a b)) {q1 q2 : ↥X → ↥X} (h1 : StrictMono q1)
    (s1 : Function.Surjective q1) (h2 : StrictMono q2) (s2 : Function.Surjective q2)
    (hlt : ∀ x, q1 x < q2 x) (t : ↥X) :
    ν.real {x | t ≤ q1 x} < ν.real {x | t ≤ q2 x} := by
  haveI := hX
  obtain ⟨u1, hu1⟩ := s1 t
  obtain ⟨u2, hu2⟩ := s2 t
  have hu : u2 < u1 := by
    have := hlt u1
    rw [hu1, ← hu2] at this
    exact h2.lt_iff_lt.1 this
  have hdisj : Disjoint {x | t ≤ q1 x} (Ioo u2 u1) := by
    rw [Set.disjoint_left]
    intro x hx hx2
    rw [← hu1] at hx
    exact absurd (h1.le_iff_le.1 hx) (not_le.2 hx2.2)
  have hsub : {x | t ≤ q1 x} ∪ Ioo u2 u1 ⊆ {x | t ≤ q2 x} := by
    rintro x (hx | hx)
    · exact hx.trans (hlt x).le
    · show t ≤ q2 x
      rw [← hu2]; exact h2.monotone hx.1.le
  have := measureReal_mono (μ := ν) hsub
  rw [measureReal_union hdisj measurableSet_Ioo] at this
  have := nu_Ioo_pos ν hsupp hu
  linarith

lemma pbar_groupMass (ν : Measure ↥X) [IsProbabilityMeasure ν] {h0 : ↥X → ↥X} (hh0 : Measurable h0)
    (hn : 1 ≤ n) (g : Grp n) :
    groupMass (pbarP ν hh0 hn) g = (1/2 : ℝ) * (if zeroGrp n = g then 1 else 0) +
      ∑ k : Fin n, (1/(2*(n:ℝ))) * (if unitGrp k = g then 1 else 0) := by
  unfold groupMass pbarP
  rw [ProbabilityMeasure.coe_mk, pbarM_real ν hh0 (mset_grp g)]
  have e1 : ν.real ((fun x : ↥X => (h0 x, zeroGrp n)) ⁻¹' {z : ScoreGrp X n | z.2 = g}) =
      if zeroGrp n = g then 1 else 0 := by
    by_cases h : zeroGrp n = g
    · simp [h]
    · simp [h]
  have e2 : ∀ k : Fin n, ν.real ((fun x : ↥X => (x, unitGrp k)) ⁻¹' {z : ScoreGrp X n | z.2 = g}) =
      if unitGrp k = g then 1 else 0 := by
    intro k
    by_cases h : unitGrp k = g
    · simp [h]
    · simp [h]
  rw [e1]
  simp only [e2]

lemma pbar_InP (hX : X.OrdConnected) (ν : Measure ↥X) [IsProbabilityMeasure ν]
    (hat : ∀ y : ↥X, ν {y} = 0) (hsupp : ∀ a b : ↥X, a < b → 0 < ν (Ioo a b))
    {h0 : ↥X → ↥X} (hh0 : Measurable h0) (hsm : StrictMono h0) (hsj : Function.Surjective h0)
    (hn : 1 ≤ n) : InP (pbarP ν hh0 hn) := by
  haveI := hX
  intro g hg
  rw [pbar_groupMass] at hg
  constructor
  · intro y
    have hmeas : MeasurableSet {z : ScoreGrp X n | z.1 = y ∧ z.2 = g} :=
      (measurable_fst (measurableSet_singleton y)).inter (mset_grp g)
    unfold pbarP
    rw [ProbabilityMeasure.coe_mk, pbarM_real ν hh0 hmeas]
    have hz : ∀ (h : ↥X → ↥X), Function.Injective h → ∀ (P : Prop),
        ν.real {x | h x = y ∧ P} = 0 := by
      intro h hinj P
      refine (measureReal_eq_zero_iff).2 (measure_mono_null (fun x hx => ?_) (nu_fibre ν hat hinj y))
      exact hx.1
    have e1 : (fun x : ↥X => (h0 x, zeroGrp n)) ⁻¹' {z : ScoreGrp X n | z.1 = y ∧ z.2 = g} =
        {x | h0 x = y ∧ zeroGrp n = g} := rfl
    have e2 : ∀ k : Fin n, (fun x : ↥X => (x, unitGrp k)) ⁻¹' {z : ScoreGrp X n | z.1 = y ∧ z.2 = g} =
        {x | id x = y ∧ unitGrp k = g} := fun k => rfl
    rw [e1, hz h0 hsm.injective]
    simp only [e2, hz id Function.injective_id, mul_zero, Finset.sum_const_zero, add_zero]
  · intro a b hab
    have hmeas : MeasurableSet {z : ScoreGrp X n | a < z.1 ∧ z.1 < b ∧ z.2 = g} :=
      (measurable_fst measurableSet_Ioi).inter ((measurable_fst measurableSet_Iio).inter (mset_grp g))
    unfold pbarP
    rw [ProbabilityMeasure.coe_mk, pbarM_real ν hh0 hmeas]
    have e1 : (fun x : ↥X => (h0 x, zeroGrp n)) ⁻¹' {z : ScoreGrp X n | a < z.1 ∧ z.1 < b ∧ z.2 = g} =
        {x | a < h0 x ∧ h0 x < b ∧ zeroGrp n = g} := rfl
    have e2 : ∀ k : Fin n, (fun x : ↥X => (x, unitGrp k)) ⁻¹' {z : ScoreGrp X n | a < z.1 ∧ z.1 < b ∧ z.2 = g} =
        {x | a < x ∧ x < b ∧ unitGrp k = g} := fun k => rfl
    rw [e1]
    simp only [e2]
    have hnn : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (1/(2*(n:ℝ))) * ν.real {x | a < x ∧ x < b ∧ unitGrp k = g} :=
      fun k _ => mul_nonneg (by positivity) measureReal_nonneg
    by_cases h0g : zeroGrp n = g
    · have : 0 < ν.real {x | a < h0 x ∧ h0 x < b ∧ zeroGrp n = g} := by
        simp only [h0g, and_true]
        exact nu_preimage_Ioo ν hsupp hsm hsj hab
      have := Finset.sum_nonneg hnn
      positivity
    · have hex : ∃ k, unitGrp k = g := by
        by_contra hne
        push_neg at hne
        simp [h0g, hne] at hg
      obtain ⟨k, hk⟩ := hex
      have hpos : 0 < ∑ k : Fin n, (1/(2*(n:ℝ))) * ν.real {x | a < x ∧ x < b ∧ unitGrp k = g} := by
        refine Finset.sum_pos' hnn ⟨k, Finset.mem_univ _, ?_⟩
        have : {x : ↥X | a < x ∧ x < b ∧ unitGrp k = g} = Ioo a b := by
          ext x; simp [hk]
        rw [this]
        exact mul_pos (by positivity) (nu_Ioo_pos ν hsupp hab)
      have : 0 ≤ ν.real {x | a < h0 x ∧ h0 x < b ∧ zeroGrp n = g} := measureReal_nonneg
      positivity

end IsectL4

open IsectL4 IsectCore in
theorem lemma4_main (X : Set ℝ) (hX : X.OrdConnected) (hXnt : X.Nontrivial) [Nonempty ↥X] (n : ℕ)
    (hn : 2 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x0 : ↥X, ∃ pbar : Intersectionality.Generic.DistSpace X n, ∃ a b : Fin n → ↥X,
      (∀ j, a j ≤ b j) ∧ Cond5 pbar.1 Q x0 α a b := by
  intro x0
  haveI := hX
  obtain ⟨ν, hνP, hat, hsupp⟩ := IsectNu.exists_nu X hX hXnt
  haveI := hνP
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ X, ∃ v ∈ X, u < v := by
    obtain ⟨x1, hx1, x2, hx2, hne⟩ := hXnt
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x1, hx1, x2, hx2, h⟩
    · exact ⟨x2, hx2, x1, hx1, h⟩
  set A : ↥X := ⟨u, hu⟩ with hA
  set B : ↥X := ⟨v, hv⟩ with hB
  set C : ↥X := ⟨(u + v) / 2, hX.out hu hv ⟨by linarith, by linarith⟩⟩ with hC
  have hAC : A < C := by
    show (A : ℝ) < (C : ℝ); simp only [hA, hC]; linarith
  have hCB : C < B := by
    show (C : ℝ) < (B : ℝ); simp only [hB, hC]; linarith
  have hn1 : 1 ≤ n := by omega
  set h0 := param Q x0 C with hh0def
  have hsm : StrictMono h0 := hQ.strictMono _ (param_mem hQ x0 C)
  have hsj : Function.Surjective h0 := (hQ.bijective _ (param_mem hQ x0 C)).2
  have hh0m : Measurable h0 := hsm.monotone.measurable
  have hpb : InP (pbarP ν hh0m hn1) := pbar_InP hX ν hat hsupp hh0m hsm hsj hn1
  have hn' : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    exact this.ne'
  have hpm : ∀ c : ↥X, StrictMono (param Q x0 c) := fun c => hQ.strictMono _ (param_mem hQ x0 c)
  have hps : ∀ c : ↥X, Function.Surjective (param Q x0 c) :=
    fun c => (hQ.bijective _ (param_mem hQ x0 c)).2
  -- the total rate at a constant parameter vector
  have htot : ∀ (c : ↥X) (t : ↥X), totalRate (pbarP ν hh0m hn1) Q x0 (fun _ => c) t =
      (1/2) * ν.real {x | t ≤ h0 x} + (1/2) * ν.real {x | t ≤ param Q x0 c x} := by
    intro c t
    rw [pbar_total hX hQ x0 ν hh0m hn1]
    simp only [grpMap_zero hQ, grpMap_unit hQ, id, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  set tA := thr (pbarP ν hh0m hn1) Q x0 α (fun _ => A) with htA
  set tB := thr (pbarP ν hh0m hn1) Q x0 α (fun _ => B) with htB
  have hRA : ν.real {x | tA ≤ param Q x0 A x} < α := by
    have hs := thr_spec hX hQ x0 hα0 hα1 (pbarP ν hh0m hn1) hpb (fun _ => A)
    rw [htot] at hs
    have hlt := nu_strict hX ν hsupp (hpm A) (hps A) hsm hsj
      (fun x => param_strictMono_left hQ x0 x hAC) tA
    linarith
  have hRB : α < ν.real {x | tB ≤ param Q x0 B x} := by
    have hs := thr_spec hX hQ x0 hα0 hα1 (pbarP ν hh0m hn1) hpb (fun _ => B)
    rw [htot] at hs
    have hlt := nu_strict hX ν hsupp hsm hsj (hpm B) (hps B)
      (fun x => param_strictMono_left hQ x0 x hCB) tB
    linarith
  refine ⟨⟨pbarP ν hh0m hn1, hpb⟩, fun _ => A, fun _ => B, fun _ => (hAC.trans hCB).le, ?_⟩
  intro i θ hθ
  constructor
  · show catRate (pbarP ν hh0m hn1) Q x0 _ (thr (pbarP ν hh0m hn1) Q x0 α _) i < α
    rw [pbar_catRate hX hQ x0 ν hh0m hn1, Function.update_self]
    have hle : (fun _ => A) ≤ Function.update θ i A := by
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact (hθ j hj).1
    have hmono := thr_mono hX hQ x0 hα0 hα1 (pbarP ν hh0m hn1) hpb hle
    calc ν.real {x | thr (pbarP ν hh0m hn1) Q x0 α (Function.update θ i A) ≤ param Q x0 A x}
        ≤ ν.real {x | tA ≤ param Q x0 A x} :=
          measureReal_mono (fun x hx => hmono.trans hx)
      _ < α := hRA
  · show α < catRate (pbarP ν hh0m hn1) Q x0 _ (thr (pbarP ν hh0m hn1) Q x0 α _) i
    rw [pbar_catRate hX hQ x0 ν hh0m hn1, Function.update_self]
    have hle : Function.update θ i B ≤ (fun _ => B) := by
      intro j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact (hθ j hj).2
    have hmono := thr_mono hX hQ x0 hα0 hα1 (pbarP ν hh0m hn1) hpb hle
    calc α < ν.real {x | tB ≤ param Q x0 B x} := hRB
      _ ≤ ν.real {x | thr (pbarP ν hh0m hn1) Q x0 α (Function.update θ i B) ≤ param Q x0 B x} :=
          measureReal_mono (fun x hx => hmono.trans hx)

theorem solution (X : Set ℝ) (hX : X.OrdConnected) (hXnt : X.Nontrivial) [Nonempty ↥X] (n : ℕ)
    (hn : 2 ≤ n) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X))
    (hQ : Intersectionality.Generic.IsPolicyFamily Q) :
    ∀ x0 : ↥X, ∃ pbar : Intersectionality.Generic.DistSpace X n, ∃ a b : Fin n → ↥X,
      (∀ j, a j ≤ b j) ∧ Cond5 pbar.1 Q x0 α a b :=
  lemma4_main X hX hXnt n hn α hα0 hα1 Q hQ
