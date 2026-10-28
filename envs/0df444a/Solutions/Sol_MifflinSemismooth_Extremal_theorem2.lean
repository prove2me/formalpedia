-- Prove2me | solution 1 for MifflinSemismooth.Extremal.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T13:45:49.72098+00:00
-- url     : https://prove2.me/submissions/16d13a93-bfab-4aa7-856d-2abd5fbc845e

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_MifflinSemismooth_Extremal_Basic
import Definitions.Def_MifflinSemismooth_Extremal_Setting

-- Complete module: MSProof/SharedBasics.lean

open Filter Topology
open scoped RealInnerProductSpace

namespace MifflinSemismooth.Extremal.MSFresh

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/ActiveSets.lean

open Filter Topology

namespace MifflinSemismooth.Extremal.MSFresh

theorem seqCompact_image_continuousOn {T Y : Type*}
    [TopologicalSpace T] [TopologicalSpace Y] {U : Set T} {F : T → Y}
    (hU : IsSeqCompact U) (hF : ContinuousOn F U) : IsSeqCompact (F '' U) := by
  intro ys hys
  choose us hus heq using hys
  obtain ⟨u, hu, φ, hφ, hlim⟩ := hU hus
  refine ⟨F u, Set.mem_image_of_mem F hu, φ, hφ, ?_⟩
  have hw : Tendsto (us ∘ φ) atTop (𝓝[U] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall (fun k => hus (φ k))⟩
  exact ((hF u hu).tendsto.comp hw).congr (fun k => heq (φ k))

theorem active_nonempty {n : ℕ} {T : Type*}
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    {f : EuclideanSpace ℝ (Fin n) → T → ℝ} {E : EuclideanSpace ℝ (Fin n) → ℝ}
    (hd : HypD B U f E ∨ HypD' B U f E) {x} (hx : x ∈ B) :
    (activeSet U f E x).Nonempty := by
  rcases hd with hd | hd
  · obtain ⟨u, hu, he⟩ := (hd x hx).1
    exact ⟨u, hu, he.symm⟩
  · obtain ⟨u, hu, he⟩ := (hd x hx).1
    exact ⟨u, hu, he.symm⟩

theorem active_limit {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    {f : EuclideanSpace ℝ (Fin n) → T → ℝ} {E : EuclideanSpace ℝ (Fin n) → ℝ}
    (ha : HypA B U f) {xs : ℕ → EuclideanSpace ℝ (Fin n)} {us : ℕ → T}
    {x : EuclideanSpace ℝ (Fin n)} {u : T}
    (hx : x ∈ B) (hu : u ∈ U) (hxs : ∀ k, xs k ∈ B)
    (hus : ∀ k, us k ∈ activeSet U f E (xs k))
    (hxl : Tendsto xs atTop (𝓝 x)) (hul : Tendsto us atTop (𝓝 u))
    (hEl : Tendsto (fun k => E (xs k)) atTop (𝓝 (E x))) :
    u ∈ activeSet U f E x := by
  refine ⟨hu, ?_⟩
  have hw : Tendsto (fun k => (xs k, us k)) atTop (𝓝[B ×ˢ U] (x, u)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxl.prodMk_nhds hul,
      Filter.Eventually.of_forall (fun k => ⟨hxs k, (hus k).1⟩)⟩
  have hf := (ha (x, u) ⟨hx, hu⟩).tendsto.comp hw
  exact tendsto_nhds_unique hEl (hf.congr (fun k => (hus k).2.symm))

theorem active_seqCompact {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    {f : EuclideanSpace ℝ (Fin n) → T → ℝ} {E : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsSeqCompact U) (ha : HypA B U f) {x} (hx : x ∈ B) :
    IsSeqCompact (activeSet U f E x) := by
  intro us hus
  obtain ⟨u, hu, φ, hφ, hlim⟩ := hU (fun k => (hus k).1)
  refine ⟨u, ?_, φ, hφ, hlim⟩
  exact active_limit ha hx hu (fun _ => hx) (fun k => hus (φ k))
    tendsto_const_nhds hlim tendsto_const_nhds

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/ActiveExtrema.lean

open Filter Topology

namespace MifflinSemismooth.Extremal.MSFresh

theorem active_pairing_continuousOn {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    {f : EuclideanSpace ℝ (Fin n) → T → ℝ} {E : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U)) {x} (hx : x ∈ B)
    (d : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun u => inner ℝ (gradient (fun y => f y u) x) d)
      (activeSet U f E x) := by
  have hg : ContinuousOn (fun u => gradient (fun y => f y u) x)
      (activeSet U f E x) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hu => ⟨hx, hu.1⟩)
  exact hg.inner continuousOn_const

theorem active_pairing_extrema {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    {f : EuclideanSpace ℝ (Fin n) → T → ℝ} {E : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsSeqCompact U) (ha : HypA B U f)
    (hd : HypD B U f E ∨ HypD' B U f E)
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U)) {x} (hx : x ∈ B)
    (d : EuclideanSpace ℝ (Fin n)) :
    (∃ u ∈ activeSet U f E x, ∀ v ∈ activeSet U f E x,
      inner ℝ (gradient (fun y => f y v) x) d ≤
        inner ℝ (gradient (fun y => f y u) x) d) ∧
    (∃ u ∈ activeSet U f E x, ∀ v ∈ activeSet U f E x,
      inner ℝ (gradient (fun y => f y u) x) d ≤
        inner ℝ (gradient (fun y => f y v) x) d) := by
  let F : T → ℝ := fun u => inner ℝ (gradient (fun y => f y u) x) d
  have hcompact : IsCompact (F '' activeSet U f E x) :=
    (seqCompact_image_continuousOn (active_seqCompact hU ha hx)
      (active_pairing_continuousOn hc hx d)).isCompact
  have hne := (active_nonempty hd hx).image F
  obtain ⟨a, ⟨u, hu, rfl⟩, hmax⟩ := hcompact.exists_isGreatest hne
  obtain ⟨b, ⟨v, hv, rfl⟩, hmin⟩ := hcompact.exists_isLeast hne
  exact ⟨⟨u, hu, fun w hw => hmax (Set.mem_image_of_mem F hw)⟩,
    ⟨v, hv, fun w hw => hmin (Set.mem_image_of_mem F hw)⟩⟩

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/SegmentCalculus.lean

open Filter Topology
open scoped RealInnerProductSpace

namespace MifflinSemismooth.Extremal.MSFresh

variable {n : ℕ}

lemma segment_mvt (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (a b : EuclideanSpace ℝ (Fin n))
    (hd : ∀ c ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ F (a + c • (b-a))) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      F b - F a = ⟪gradient F (a + c • (b-a)), b-a⟫ := by
  let g : ℝ → ℝ := fun t => F (a + t • (b-a))
  have hder (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt g ⟪gradient F (a + t • (b-a)), b-a⟫ t := by
    have hp : HasDerivAt (fun s : ℝ => a + s • (b-a)) (b-a) t := by
      simpa using ((hasDerivAt_id t).smul_const (b-a)).const_add a
    simpa only [g, Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hd t ht).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope g
    (fun t => ⟪gradient F (a + t • (b-a)), b-a⟫) (by norm_num : (0:ℝ)<1)
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  refine ⟨c,hc,?_⟩
  simpa [g] using he.symm

lemma slice_lipschitz_ball (B : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (M : NNReal) (hr : Metric.ball x r ⊆ B)
    (hd : ∀ y ∈ B, DifferentiableAt ℝ F y)
    (hb : ∀ y ∈ B, ‖gradient F y‖ ≤ M) :
    LipschitzOnWith M F (Metric.ball x r) := by
  apply (convex_ball x r).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun y hy => hd y (hr hy))
  intro y hy
  have he := (hd y (hr hy)).hasGradientAt.hasFDerivAt.fderiv
  rw [he]
  change ‖InnerProductSpace.toDual ℝ _ (gradient F y)‖ ≤ (M : ℝ)
  rw [(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).norm_map]
  exact hb y (hr hy)

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/MovingExpansion.lean

open Filter Topology
open scoped RealInnerProductSpace

namespace MifflinSemismooth.Extremal.MSFresh

lemma moving_secant {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (hB : IsOpen B)
    (hd : ∀ u ∈ U, ∀ z ∈ B, DifferentiableAt ℝ (fun y => f y u) z)
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    {x d : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B)
    {ys : ℕ → EuclideanSpace ℝ (Fin n)} {us : ℕ → T} {u : T}
    (hu : u ∈ U) (hus : ∀ k, us k ∈ U)
    (hy : Tendsto ys atTop (𝓝 x)) (hul : Tendsto us atTop (𝓝 u))
    {t : ℕ → ℝ} (_ht : ∀ k, 0 < t k)
    (hv : Tendsto (fun k => (t k)⁻¹ • (ys k-x)) atTop (𝓝 d)) :
    Tendsto (fun k => (f (ys k) (us k)-f x (us k))/t k) atTop
      (𝓝 (⟪gradient (fun y => f y u) x,d⟫)) := by
  classical
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB x hx
  have hseg (k) (hk : ys k ∈ Metric.ball x r) (c : ℝ) (hc' : c ∈ Set.Icc (0:ℝ) 1) :
      x+c • (ys k-x) ∈ B := by
    apply hrB
    have h := (convex_ball x r) (Metric.mem_ball_self hr) hk
      (sub_nonneg.mpr hc'.2) hc'.1 (by ring : (1-c)+c=1)
    convert h using 1
    module
  have hex (k : ℕ) : ∃ c ∈ Set.Icc (0:ℝ) 1,
      ys k ∈ Metric.ball x r → f (ys k) (us k)-f x (us k) =
        ⟪gradient (fun y => f y (us k)) (x+c • (ys k-x)),ys k-x⟫ := by
    by_cases hk : ys k ∈ Metric.ball x r
    · obtain ⟨c,hc',he⟩ := segment_mvt (fun y => f y (us k)) x (ys k)
        (fun c hc' => hd (us k) (hus k) _ (hseg k hk c hc'))
      exact ⟨c,⟨hc'.1.le,hc'.2.le⟩,fun _ => he⟩
    · exact ⟨0,by simp,fun h => (hk h).elim⟩
  choose c hcc he using hex
  have hsmall : Tendsto (fun k => c k • (ys k-x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => ?_) (by simpa using (hy.sub_const x).norm)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcc k).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hcc k).2
  have hz : Tendsto (fun k => x+c k • (ys k-x)) atTop (𝓝 x) := by
    simpa using hsmall.const_add x
  have hyball : ∀ᶠ k in atTop, ys k ∈ Metric.ball x r := hy (Metric.ball_mem_nhds x hr)
  have hp : Tendsto (fun k => (x+c k • (ys k-x),us k)) atTop (𝓝[B ×ˢ U] (x,u)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz.prodMk_nhds hul,
      hyball.mono (fun k hk => ⟨hseg k hk _ (hcc k),hus k⟩)⟩
  have hg := (hc (x,u) ⟨hx,hu⟩).tendsto.comp hp
  apply (hg.inner hv).congr'
  filter_upwards [hyball] with k hk
  rw [he k hk, real_inner_smul_right]
  dsimp only [Function.comp_def]
  ring

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/SubsequenceCriterion.lean

open Filter Topology

namespace MifflinSemismooth.Extremal.MSFresh

theorem tendsto_of_subsubsequence {a : ℕ → ℝ} {L : ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (a ∘ φ ∘ ψ) atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hn
  push Not at hn
  have hf : ∃ᶠ k in atTop, ε ≤ dist (a k) L := frequently_atTop.mpr hn
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨ψ, _hψ, hlim⟩ := h φ hφ
  have he := (Metric.tendsto_atTop.mp hlim) ε hε
  obtain ⟨N, hN⟩ := he
  have hb := hbad (ψ N)
  have hg := hN N le_rfl
  exact (not_lt_of_ge hb) hg

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/ActiveRay.lean

open Filter Topology

namespace MifflinSemismooth.Extremal.MSFresh

theorem active_sequence_limit {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (hB : IsOpen B) (hU : IsSeqCompact U) (ha : HypA B U f)
    (hdiff : ∀ u ∈ U, ∀ z ∈ B, DifferentiableAt ℝ (fun y => f y u) z)
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    {x d : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B) (hE : ContinuousAt E x)
    {ys : ℕ → EuclideanSpace ℝ (Fin n)} (hys : ∀ k, ys k ∈ B)
    (hy : Tendsto ys atTop (𝓝 x)) {t : ℕ → ℝ} (ht : ∀ k, 0 < t k)
    (hv : Tendsto (fun k => (t k)⁻¹ • (ys k-x)) atTop (𝓝 d))
    {v : T} (hva : v ∈ activeSet U f E x) {L : ℝ}
    (hvL : inner ℝ (gradient (fun y => f y v) x) d = L)
    (hext : (HypD B U f E ∧ ∀ u ∈ activeSet U f E x,
        inner ℝ (gradient (fun y => f y u) x) d ≤ L) ∨
      (HypD' B U f E ∧ ∀ u ∈ activeSet U f E x,
        L ≤ inner ℝ (gradient (fun y => f y u) x) d))
    (us : ℕ → T) (hus : ∀ k, us k ∈ activeSet U f E (ys k)) :
    Tendsto (fun k => inner ℝ (gradient (fun y => f y (us k)) (ys k)) d)
      atTop (𝓝 L) := by
  apply tendsto_of_subsubsequence
  intro φ hφ
  obtain ⟨u, hu, ψ, hψ, hul⟩ := hU (fun k => (hus (φ k)).1)
  let τ := φ ∘ ψ
  have hτ : StrictMono τ := hφ.comp hψ
  have hyl := hy.comp hτ.tendsto_atTop
  have hua : u ∈ activeSet U f E x :=
    active_limit ha hx hu (fun k => hys (τ k)) (fun k => hus (τ k))
      hyl hul ((hE.tendsto.comp hy).comp hτ.tendsto_atTop)
  have hqu := moving_secant f hB hdiff hc hx hu (fun k => (hus (τ k)).1)
    hyl hul (fun k => ht (τ k)) (hv.comp hτ.tendsto_atTop)
  have hqv := moving_secant f hB hdiff hc hx hva.1 (fun _ => hva.1)
    hyl tendsto_const_nhds (fun k => ht (τ k)) (hv.comp hτ.tendsto_atTop)
  have heq : inner ℝ (gradient (fun y => f y u) x) d = L := by
    rcases hext with ⟨hd, hmax⟩ | ⟨hd, hmin⟩
    · apply le_antisymm (hmax u hua)
      rw [← hvL]
      apply le_of_tendsto_of_tendsto' hqv hqu
      intro k
      apply div_le_div_of_nonneg_right _ (ht (τ k)).le
      have h1 := (hd (ys (τ k)) (hys (τ k))).2
        (Set.mem_image_of_mem (fun v => f (ys (τ k)) v) hva.1)
      have h2 := (hd x hx).2 (Set.mem_image_of_mem (fun v => f x v) (hus (τ k)).1)
      have h3 := (hus (τ k)).2
      have h4 := hva.2
      dsimp only [Function.comp_def]
      linarith
    · apply le_antisymm _ (hmin u hua)
      rw [← hvL]
      apply le_of_tendsto_of_tendsto' hqu hqv
      intro k
      apply div_le_div_of_nonneg_right _ (ht (τ k)).le
      have h1 := (hd (ys (τ k)) (hys (τ k))).2
        (Set.mem_image_of_mem (fun v => f (ys (τ k)) v) hva.1)
      have h2 := (hd x hx).2 (Set.mem_image_of_mem (fun v => f x v) (hus (τ k)).1)
      have h3 := (hus (τ k)).2
      have h4 := hva.2
      dsimp only [Function.comp_def]
      linarith
  have hp : Tendsto (fun k => (ys (τ k), us (τ k))) atTop (𝓝[B ×ˢ U] (x, u)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hyl.prodMk_nhds hul,
      Filter.Eventually.of_forall (fun k => ⟨hys (τ k), (hus (τ k)).1⟩)⟩
  refine ⟨ψ, hψ, ?_⟩
  have hg : Tendsto (fun k => inner ℝ (gradient (fun y => f y (us (τ k))) (ys (τ k))) d)
      atTop (𝓝 (inner ℝ (gradient (fun y => f y u) x) d)) :=
    ((hc (x, u) ⟨hx, hu⟩).tendsto.comp hp).inner
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))
  simpa only [heq, τ, Function.comp_def] using hg

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/LocalLipschitz.lean

open Filter Topology
open scoped RealInnerProductSpace

namespace MifflinSemismooth.Extremal.MSFresh

variable {n : ℕ} {T : Type*}

lemma extremal_lipschitz_on (B S : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (hS : S ⊆ B) (hdE : HypD B U f E ∨ HypD' B U f E) (M : NNReal)
    (hf : ∀ u ∈ U, LipschitzOnWith M (fun x => f x u) S) : LipschitzOnWith M E S := by
  have hub (x) (hx : x ∈ S) (y) (hy : y ∈ S) : E x-E y ≤ M*dist x y := by
    rcases hdE with hmax | hmin
    · obtain ⟨u,hu,he⟩ := (hmax x (hS hx)).1
      have hle := (hmax y (hS hy)).2 (Set.mem_image_of_mem (fun u => f y u) hu)
      have hb := (hf u hu).dist_le_mul x hx y hy
      rw [Real.dist_eq] at hb
      have hsub := (abs_le.mp hb).2
      linarith
    · obtain ⟨u,hu,he⟩ := (hmin y (hS hy)).1
      have hle := (hmin x (hS hx)).2 (Set.mem_image_of_mem (fun u => f x u) hu)
      have hb := (hf u hu).dist_le_mul x hx y hy
      rw [Real.dist_eq] at hb
      have hsub := (abs_le.mp hb).2
      linarith
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hub y hy x hx
    rw [dist_comm y x] at h
    linarith
  · exact hub x hx y hy

lemma extremal_lipschitzNear (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T)
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (hB : IsOpen B) (hdE : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M)
    {x} (hx : x ∈ B) : LipschitzNear E x := by
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB x hx
  obtain ⟨M,hM⟩ := hbdd
  let K : NNReal := ⟨max M 0, le_max_right _ _⟩
  refine ⟨r,hr,K,extremal_lipschitz_on B (Metric.ball x r) U f E hrB hdE K ?_⟩
  intro u hu
  apply slice_lipschitz_ball B (fun y => f y u) x r K hrB (hdiff u hu)
  intro y hy
  exact (hM y hy u hu).trans (le_max_left _ _)

lemma continuousAt_of_lipschitzNear (E : EuclideanSpace ℝ (Fin n) → ℝ) {x}
    (h : LipschitzNear E x) : ContinuousAt E x := by
  obtain ⟨r,hr,K,hK⟩ := h
  exact hK.continuousOn.continuousAt (Metric.ball_mem_nhds x hr)

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/QuotientFilters.lean

open Filter Topology
open scoped RealInnerProductSpace

namespace MifflinSemismooth.Extremal.MSFresh

variable {n : ℕ}

lemma quotient_endpoints (x d : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ p : EuclideanSpace ℝ (Fin n) × ℝ in
      𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ),
      0 < p.2 ∧ x+p.1 ∈ Metric.ball x r ∧ x+p.1+p.2 • d ∈ Metric.ball x r := by
  have hfst : Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1)
      (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_fst
  have hsnd : Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.2)
      (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have ha : Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => x+p.1)
      (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa using hfst.const_add x
  have hb : Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => x+p.1+p.2 • d)
      (𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa using ha.add (hsnd.smul_const d)
  have hp : ∀ᶠ p : EuclideanSpace ℝ (Fin n) × ℝ in
      𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ), 0 < p.2 :=
    tendsto_snd.eventually self_mem_nhdsWithin
  exact hp.and ((ha.eventually (Metric.ball_mem_nhds x hr)).and (hb.eventually (Metric.ball_mem_nhds x hr)))

lemma quotient_bounded (E : EuclideanSpace ℝ (Fin n) → ℝ) (x d : EuclideanSpace ℝ (Fin n))
    (h : LipschitzNear E x) : ∃ C : ℝ, ∀ᶠ p : EuclideanSpace ℝ (Fin n) × ℝ in
      𝓝 (0 : EuclideanSpace ℝ (Fin n)) ×ˢ 𝓝[>] (0 : ℝ),
      |(E (x+p.1+p.2 • d)-E (x+p.1))/p.2| ≤ C := by
  obtain ⟨r,hr,K,hK⟩ := h
  refine ⟨K*‖d‖,?_⟩
  filter_upwards [quotient_endpoints x d hr] with p hp
  have hb := hK.dist_le_mul _ hp.2.2 _ hp.2.1
  rw [Real.dist_eq, dist_eq_norm] at hb
  have he : x+p.1+p.2 • d-(x+p.1) = p.2 • d := by abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hp.1] at hb
  rw [abs_div,abs_of_pos hp.1,div_le_iff₀ hp.1]
  nlinarith

lemma genDir_le_of_local_increment (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (h : LipschitzNear E x) (L : ℝ)
    (hub : ∀ ε > 0, ∃ r > 0, ∀ a b : EuclideanSpace ℝ (Fin n),
      a ∈ Metric.ball x r → b ∈ Metric.ball x r → ∀ t : ℝ, 0 < t →
      b=a+t • d → (E b-E a)/t ≤ L+ε) :
    ClarkeGradients.Shared.genDirDeriv E x d ≤ L := by
  obtain ⟨C,hC⟩ := quotient_bounded E x d h
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r,hr,hub⟩ := hub ε hε
  apply Filter.limsup_le_of_le
    (Filter.isCoboundedUnder_le_of_eventually_le _ (hC.mono (fun p hp => (abs_le.mp hp).1)))
  filter_upwards [quotient_endpoints x d hr] with p hp
  exact hub _ _ hp.2.1 hp.2.2 _ hp.1 rfl

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/NearbyActive.lean

open Filter Topology

namespace MifflinSemismooth.Extremal.MSFresh

theorem nearby_active_upper {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    {f : EuclideanSpace ℝ (Fin n) → T → ℝ} {E : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : IsSeqCompact U) (ha : HypA B U f)
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B) (hE : ContinuousAt E x)
    (d : EuclideanSpace ℝ (Fin n)) (L : ℝ)
    (hL : ∀ u ∈ activeSet U f E x, inner ℝ (gradient (fun y => f y u) x) d ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ z w u, z ∈ B → w ∈ B →
      dist z x < r → dist w x < r → u ∈ activeSet U f E z →
      inner ℝ (gradient (fun y => f y u) w) d ≤ L + ε := by
  classical
  by_contra h
  push Not at h
  choose z w u hz hw hzx hwx hu hbad using
    (fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity))
  have hzlim : Tendsto z atTop (𝓝 x) := tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun k => (hzx k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have hwlim : Tendsto w atTop (𝓝 x) := tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero (fun _ => dist_nonneg) (fun k => (hwx k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨v, hv, φ, hφ, hvl⟩ := hU (fun k => (hu k).1)
  have hactive : v ∈ activeSet U f E x :=
    active_limit ha hx hv (fun k => hz (φ k)) (fun k => hu (φ k))
      (hzlim.comp hφ.tendsto_atTop) hvl ((hE.tendsto.comp hzlim).comp hφ.tendsto_atTop)
  have hpair : Tendsto (fun k => (w (φ k), u (φ k))) atTop (𝓝[B ×ˢ U] (x, v)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(hwlim.comp hφ.tendsto_atTop).prodMk_nhds hvl,
        Filter.Eventually.of_forall (fun k => ⟨hw (φ k), (hu (φ k)).1⟩)⟩
  have hgrad : Tendsto (fun k => inner ℝ (gradient (fun y => f y (u (φ k))) (w (φ k))) d)
      atTop (𝓝 (inner ℝ (gradient (fun y => f y v) x) d)) :=
    ((hc (x, v) ⟨hx, hv⟩).tendsto.comp hpair).inner
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))
  have hge : L + ε ≤ inner ℝ (gradient (fun y => f y v) x) d :=
    ge_of_tendsto hgrad (Filter.Eventually.of_forall (fun k => (hbad (φ k)).le))
  have := hL v hactive
  linarith

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/GeneralizedSandwich.lean

open Filter Topology
open scoped RealInnerProductSpace

namespace MifflinSemismooth.Extremal.MSFresh

lemma extremal_increment_le {n : ℕ} {T : Type*}
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ z ∈ B, DifferentiableAt ℝ (fun y => f y u) z)
    (x d : EuclideanSpace ℝ (Fin n)) (r H : ℝ) (hrB : Metric.ball x r ⊆ B)
    (hG : ∀ z ∈ Metric.ball x r, ∀ u ∈ activeSet U f E z,
      ∀ w ∈ Metric.ball x r, ⟪gradient (fun y => f y u) w,d⟫ ≤ H)
    (a b : EuclideanSpace ℝ (Fin n)) (ha : a ∈ Metric.ball x r) (hb : b ∈ Metric.ball x r)
    (t : ℝ) (ht : 0 < t) (he : b=a+t • d) : (E b-E a)/t ≤ H := by
  have hex : ∃ z ∈ Metric.ball x r, ∃ u ∈ activeSet U f E z,
      E b-E a ≤ f b u-f a u := by
    rcases hd with hmax | hmin
    · obtain ⟨u,hu,huE⟩ := (hmax b (hrB hb)).1
      have hle := (hmax a (hrB ha)).2 (Set.mem_image_of_mem (fun u => f a u) hu)
      exact ⟨b,hb,u,⟨hu,huE.symm⟩,by linarith⟩
    · obtain ⟨u,hu,huE⟩ := (hmin a (hrB ha)).1
      have hle := (hmin b (hrB hb)).2 (Set.mem_image_of_mem (fun u => f b u) hu)
      exact ⟨a,ha,u,⟨hu,huE.symm⟩,by linarith⟩
  obtain ⟨z,hz,u,hu,hinc⟩ := hex
  have hseg (c : ℝ) (hc : c ∈ Set.Icc (0:ℝ) 1) : a+c • (b-a) ∈ Metric.ball x r := by
    have h := (convex_ball x r) ha hb (sub_nonneg.mpr hc.2) hc.1
      (by ring : (1-c)+c=1)
    convert h using 1
    module
  obtain ⟨c,hc,hcE⟩ := segment_mvt (fun y => f y u) a b
    (fun c hc => hdiff u hu.1 _ (hrB (hseg c hc)))
  have hgrad := hG z hz u hu _ (hseg c ⟨hc.1.le,hc.2.le⟩)
  have hsub : b-a=t • d := by rw [he]; abel
  rw [hsub,real_inner_smul_right] at hcE
  rw [hsub] at hgrad
  apply (div_le_iff₀ ht).mpr
  nlinarith

lemma genDir_upper {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (hB : IsOpen B) (hU : IsSeqCompact U) (ha : HypA B U f)
    (hd : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ z ∈ B, DifferentiableAt ℝ (fun y => f y u) z)
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B) (hLip : LipschitzNear E x)
    (d : EuclideanSpace ℝ (Fin n)) (L : ℝ)
    (hL : ∀ u ∈ activeSet U f E x, ⟪gradient (fun y => f y u) x,d⟫ ≤ L) :
    ClarkeGradients.Shared.genDirDeriv E x d ≤ L := by
  apply genDir_le_of_local_increment E x d hLip L
  intro ε hε
  obtain ⟨r,hr,hbound⟩ := nearby_active_upper hU ha hc hx
    (continuousAt_of_lipschitzNear E hLip) d L hL hε
  obtain ⟨s,hs,hsB⟩ := Metric.isOpen_iff.mp hB x hx
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  have hRB : Metric.ball x R ⊆ B :=
    fun _ hz => hsB (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)))
  refine ⟨R,hR,?_⟩
  intro a b ha' hb' t ht he
  apply extremal_increment_le f E hd hdiff x d R (L+ε) hRB ?_ a b ha' hb' t ht he
  intro z hz u hu w hw
  exact hbound z w u (hRB hz) (hRB hw)
    (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _))
    (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)) hu

lemma genGrad_pairing_sandwich {n : ℕ} {T : Type*} [TopologicalSpace T]
    {B : Set (EuclideanSpace ℝ (Fin n))} {U : Set T}
    (f : EuclideanSpace ℝ (Fin n) → T → ℝ) (E : EuclideanSpace ℝ (Fin n) → ℝ)
    (hB : IsOpen B) (hU : IsSeqCompact U) (ha : HypA B U f)
    (hd : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ z ∈ B, DifferentiableAt ℝ (fun y => f y u) z)
    (hc : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T =>
      gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B) (hLip : LipschitzNear E x)
    (d : EuclideanSpace ℝ (Fin n)) (l L : ℝ)
    (hl : ∀ u ∈ activeSet U f E x, l ≤ ⟪gradient (fun y => f y u) x,d⟫)
    (hL : ∀ u ∈ activeSet U f E x, ⟪gradient (fun y => f y u) x,d⟫ ≤ L)
    {g : EuclideanSpace ℝ (Fin n)} (hg : g ∈ genGrad E x) :
    l ≤ ⟪g,d⟫ ∧ ⟪g,d⟫ ≤ L := by
  constructor
  · have h := (hg (-d)).trans (genDir_upper f E hB hU ha hd hdiff hc hx hLip (-d) (-l)
      (fun u hu => by simpa using neg_le_neg (hl u hu)))
    simpa using neg_le_neg h
  · exact (hg d).trans (genDir_upper f E hB hU ha hd hdiff hc hx hLip d L hL)

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/NativeConclusion.lean

open Filter Topology

namespace MifflinSemismooth.Extremal.MSFresh

theorem native_theorem2 {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hdE : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × T => gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M) :
    SemismoothOn E B := by
  classical
  intro x hx
  have hLip := extremal_lipschitzNear B U f E hB hdE hdiff hbdd hx
  refine ⟨hLip, ?_⟩
  intro d t θ g ht htl hθ hg
  let ys : ℕ → EuclideanSpace ℝ (Fin n) := fun k => x + t k • d + θ k
  have hθlim : Tendsto θ atTop (𝓝 0) := by
    have hh := htl.smul hθ
    have he : (fun k => t k • ((t k)⁻¹ • θ k)) = θ := by
      funext k
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (ht k)), one_smul]
    simpa only [he, zero_smul] using hh
  have hyl : Tendsto ys atTop (𝓝 x) := by
    simpa only [zero_smul, add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add
        (htl.smul_const d)).add hθlim
  have hv : Tendsto (fun k => (t k)⁻¹ • (ys k-x)) atTop (𝓝 d) := by
    have he : (fun k => (t k)⁻¹ • (ys k-x)) = (fun k => d + (t k)⁻¹ • θ k) := by
      funext k
      have hy : ys k - x = t k • d + θ k := by dsimp [ys]; abel
      rw [hy, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt (ht k)), one_smul]
    rw [he]
    simpa only [add_zero] using hθ.const_add d
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hyl (hB.mem_nhds hx))
  have hys (k : ℕ) : ys (k+N) ∈ B := hN (k+N) (Nat.le_add_left N k)
  have hext := active_pairing_extrema hU ha hdE hcont hx d
  have hvchoose : ∃ v ∈ activeSet U f E x,
      (HypD B U f E ∧ ∀ u ∈ activeSet U f E x,
        inner ℝ (gradient (fun y => f y u) x) d ≤ inner ℝ (gradient (fun y => f y v) x) d) ∨
      (HypD' B U f E ∧ ∀ u ∈ activeSet U f E x,
        inner ℝ (gradient (fun y => f y v) x) d ≤ inner ℝ (gradient (fun y => f y u) x) d) := by
    rcases hdE with hd | hd
    · obtain ⟨v, hv, hmax⟩ := hext.1
      exact ⟨v, hv, Or.inl ⟨hd, hmax⟩⟩
    · obtain ⟨v, hv, hmin⟩ := hext.2
      exact ⟨v, hv, Or.inr ⟨hd, hmin⟩⟩
  obtain ⟨v, hva, hvext⟩ := hvchoose
  let L := inner ℝ (gradient (fun y => f y v) x) d
  have hchosen (k : ℕ) := active_pairing_extrema hU ha hdE hcont (hys k) d
  choose umax humax hmax using fun k => (hchosen k).1
  choose umin humin hmin using fun k => (hchosen k).2
  have hseq (us : ℕ → T) (hus : ∀ k, us k ∈ activeSet U f E (ys (k+N))) :
      Tendsto (fun k => inner ℝ (gradient (fun y => f y (us k)) (ys (k+N))) d)
        atTop (𝓝 L) :=
    active_sequence_limit f E hB hU ha hdiff hcont hx
      (continuousAt_of_lipschitzNear E hLip) hys
      (hyl.comp (tendsto_add_atTop_nat N)) (fun k => ht (k+N))
      (hv.comp (tendsto_add_atTop_nat N)) hva rfl hvext us hus
  have hb (k : ℕ) := genGrad_pairing_sandwich f E hB hU ha hdE hdiff hcont (hys k)
    (extremal_lipschitzNear B U f E hB hdE hdiff hbdd (hys k)) d
    (inner ℝ (gradient (fun y => f y (umin k)) (ys (k+N))) d)
    (inner ℝ (gradient (fun y => f y (umax k)) (ys (k+N))) d)
    (hmin k) (hmax k) (hg (k+N))
  have htail : Tendsto (fun k => inner ℝ (g (k+N)) d) atTop (𝓝 L) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (hseq umin humin) (hseq umax humax)
      (fun k => (hb k).1) (fun k => (hb k).2)
  have hfull : Tendsto (fun k => inner ℝ (g k) d) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat N).mp htail
  refine ⟨L, hfull.mapClusterPt, ?_⟩
  intro c hc
  obtain ⟨φ, hφ, hcl⟩ := hc.tendsto_subseq
  exact tendsto_nhds_unique hcl (hfull.comp hφ.tendsto_atTop)

end MifflinSemismooth.Extremal.MSFresh

-- Complete module: MSProof/FinalRoot.lean

namespace MifflinSemismooth.Extremal

/-- Mifflin (1976), Theorem 2, p. 8: suppose (a) and (d) or (d') hold, `f(·, u)` is
differentiable on `B` for each `u ∈ U`, and `∇ₓf(·, ·)` is continuous and bounded on `B × U`.
Then `E` is semismooth on `B`. -/
theorem theorem2 {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hdE : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × T => gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M) :
    SemismoothOn E B := by
  exact MSFresh.native_theorem2 B U f E hB hU ha hdE hdiff hcont hbdd

end MifflinSemismooth.Extremal


open MifflinSemismooth.Extremal
theorem solution {n : ℕ} {T : Type*} [TopologicalSpace T]
    (B : Set (EuclideanSpace ℝ (Fin n))) (U : Set T) (f : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (E : EuclideanSpace ℝ (Fin n) → ℝ) (hB : IsOpen B) (hU : IsSeqCompact U)
    (ha : HypA B U f) (hdE : HypD B U f E ∨ HypD' B U f E)
    (hdiff : ∀ u ∈ U, ∀ x ∈ B, DifferentiableAt ℝ (fun y => f y u) x)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × T => gradient (fun y => f y p.2) p.1) (B ×ˢ U))
    (hbdd : ∃ M : ℝ, ∀ x ∈ B, ∀ u ∈ U, ‖gradient (fun y => f y u) x‖ ≤ M) :
    SemismoothOn E B := by
  exact MifflinSemismooth.Extremal.theorem2 B U f E hB hU ha hdE hdiff hcont hbdd
