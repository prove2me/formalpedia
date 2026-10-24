-- Prove2me | solution 1 for OAI.QuadricCounterexample.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:08:17.604328+00:00
-- url     : https://prove2.me/submissions/b654c67a-fe18-4109-b39a-7ebf56b4353e

import Mathlib
import Definitions.Def_QuadricBundles
import Definitions.Def_OAIQWQC004
import Theorems.Thm_OAI_QuadricCounterexample_DiskSubharmonicOn_eq_const_of_max

section
-- module Solutions.OAIQW_QuadricCounterexample.Charts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuadricCounterexample
open Set Filter Topology Metric OnePoint
noncomputable section
open scoped Matrix.Norms.Elementwise ComplexOrder

lemma affineP1_isOpenEmbedding (i : Fin 2) : IsOpenEmbedding (affineP1 i) := by
  fin_cases i
  · exact reciprocalP1Homeomorph.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  · exact OnePoint.isOpenEmbedding_coe

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set OnePoint MvPolynomial
noncomputable section

lemma powerPullbackTwist_spec (G : AlgebraicRankTwoBundle) (m : ℕ) (hm : 0 < m) :
    IsPowerPullbackTwist G m (powerPullbackTwist G m hm) :=
  ⟨rfl,rfl,fun _ ↦ rfl,fun _ _ _ _ _ ↦ rfl⟩

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Removability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

open scoped Pointwise
noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

open Real

theorem DiskSubharmonicOn.pointwise_limit {Ω : Set ℂ} {u : ℕ → ℂ → ℝ}
    {q : ℂ → ℝ} (hu : ∀ n, DiskSubharmonicOn Ω (u n))
    (hq : UpperSemicontinuousOn q Ω)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (q x)))
    (hbound : ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → closedBall x r ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ y ∈ ball x r, ‖u n y‖ ≤ C) : DiskSubharmonicOn Ω q := by
  refine ⟨hq, ?_⟩
  intro x hx r hr hb
  obtain ⟨C, hC⟩ := hbound x hx r hr hb
  have hi (n : ℕ) : IntegrableOn (u n) (ball x r) := (hu n).2 x hx r hr hb |>.1
  have hc : IntegrableOn (fun _ : ℂ ↦ C) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hCae (n : ℕ) : ∀ᵐ y ∂volume.restrict (ball x r), ‖u n y‖ ≤ C :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hC n y hy
  have hl : ∀ᵐ y ∂volume.restrict (ball x r),
      Tendsto (fun n ↦ u n y) atTop (𝓝 (q y)) :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hlim y (hb (ball_subset_closedBall hy))
  have hqi : IntegrableOn q (ball x r) := by
    apply hc.mono' (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hi n).aestronglyMeasurable) hl)
    filter_upwards [hl, ae_all_iff.mpr hCae] with y hy hCy
    exact le_of_tendsto hy.norm (Eventually.of_forall hCy)
  have hInt := tendsto_integral_of_dominated_convergence (fun _ : ℂ ↦ C)
    (fun n ↦ (hi n).aestronglyMeasurable) hc hCae hl
  refine ⟨hqi, ?_⟩
  exact le_of_tendsto_of_tendsto ((hlim x hx).const_mul _) hInt
    (Eventually.of_forall fun n ↦ (hu n).2 x hx r hr hb |>.2)

theorem DiskSubharmonicOn.integral {α : Type u21} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {Ω : Set ℂ} {F : α → ℂ → ℝ}
    (hF : ∀ᵐ a ∂μ, DiskSubharmonicOn Ω (F a))
    (hc : UpperSemicontinuousOn (fun z ↦ ∫ a, F a z ∂μ) Ω)
    (hpoint : ∀ z ∈ Ω, Integrable (fun a ↦ F a z) μ)
    (hprod : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → closedBall z r ⊆ Ω →
      Integrable (fun p : α × ℂ ↦ F p.1 p.2) (μ.prod (volume.restrict (ball z r)))) :
    DiskSubharmonicOn Ω (fun z ↦ ∫ a, F a z ∂μ) := by
  refine ⟨hc, ?_⟩
  intro z hz r hr hb
  have hi := hprod z hz r hr hb
  refine ⟨hi.integral_prod_right, ?_⟩
  have hm : ∀ᵐ a ∂μ, (volume (ball z r)).toReal * F a z ≤ ∫ y in ball z r, F a y :=
    hF.mono fun a ha ↦ (ha.2 z hz r hr hb).2
  calc
    (volume (ball z r)).toReal * (∫ a, F a z ∂μ) =
        ∫ a, (volume (ball z r)).toReal * F a z ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ a, (∫ y in ball z r, F a y) ∂μ :=
      integral_mono_ae ((hpoint z hz).const_mul _) hi.integral_prod_left hm
    _ = ∫ y in ball z r, ∫ a, F a y ∂μ := integral_integral_swap hi

theorem DiskPshOn.pointwise_limit {E : Type u22} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ω : Set E} {u : ℕ → E → ℝ} {q : E → ℝ}
    (hu : ∀ n, DiskPshOn Ω (u n)) (hq : UpperSemicontinuousOn q Ω)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (q x)))
    (hbound : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ x ∈ K, ‖u n x‖ ≤ C) : DiskPshOn Ω q := by
  refine ⟨hq, ?_⟩
  intro D hD γ hγ hmap
  refine DiskSubharmonicOn.pointwise_limit (fun n ↦ (hu n).2 D hD γ hγ hmap)
    (hq.comp hγ.continuousOn hmap) (fun x hx ↦ hlim (γ x) (hmap hx)) ?_
  intro x hx r hr hb
  have hc : IsCompact (γ '' closedBall x r) :=
    (isCompact_closedBall x r).image_of_continuousOn (hγ.continuousOn.mono hb)
  obtain ⟨C, hC⟩ := hbound _ hc (image_subset_iff.mpr (hmap.mono_left hb))
  exact ⟨C, fun n y hy ↦ hC n (γ y) ⟨y, ball_subset_closedBall hy, rfl⟩⟩

lemma continuousOn_integral_compact_parameter
    {E : Type u23} {α : Type u24} [NormedAddCommGroup E] [LocallyCompactSpace E]
    [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω)
    {F : α → E → ℝ} (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Ω)) :
    ContinuousOn (fun x ↦ ∫ a, F a x ∂μ) Ω := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hc : Continuous (fun p : Ω × α ↦ F p.2 p.1) :=
    hF.comp_continuous (f := fun p : Ω × α ↦ (p.2, (p.1 : E)))
      (by fun_prop) (fun p ↦ ⟨mem_univ _, p.1.property⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun x : Ω ↦ fun a : α ↦ F a x) hc isCompact_univ
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hi using 1
  ext x
  simp only [Set.domRestrict_apply, setIntegral_univ]

theorem DiskPshOn.integral_compact_parameter
    {E : Type u25} {α : Type u26} [NormedAddCommGroup E] [NormedSpace ℂ E] [LocallyCompactSpace E]
    [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {Ω : Set E} (hΩ : IsOpen Ω) {F : α → E → ℝ}
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ Ω))
    (hF : ∀ a, DiskPshOn Ω (F a)) : DiskPshOn Ω (fun x ↦ ∫ a, F a x ∂μ) := by
  have hcont := continuousOn_integral_compact_parameter (μ := μ) hΩ hc
  refine ⟨hcont.upperSemicontinuousOn, ?_⟩
  intro D hD γ hγ hmap
  apply DiskSubharmonicOn.integral
    (Eventually.of_forall fun a ↦ (hF a).2 D hD γ hγ hmap)
    (hcont.upperSemicontinuousOn.comp hγ.continuousOn hmap)
  · intro z hz
    have hh : Continuous (fun a ↦ F a (γ z)) :=
      hc.comp_continuous (f := fun a : α ↦ (a, γ z))
        (by fun_prop) (fun a ↦ ⟨mem_univ _, hmap hz⟩)
    exact integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ)
  · intro z hz r hr hb
    have hcomp : ContinuousOn (fun p : α × ℂ ↦ F p.1 (γ p.2))
        (univ ×ˢ closedBall z r) := by
      apply hc.comp (continuous_fst.continuousOn.prodMk
        (hγ.continuousOn.comp continuous_snd.continuousOn (fun p hp ↦ hb hp.2)))
      exact fun p hp ↦ ⟨mem_univ _, hmap (hb hp.2)⟩
    have hi := hcomp.integrableOn_compact (μ := μ.prod volume) (isCompact_univ.prod (isCompact_closedBall z r))
    have hij := hi.mono_set (prod_mono (Subset.refl univ) ball_subset_closedBall)
    unfold IntegrableOn at hij
    rw [← Measure.prod_restrict univ (ball z r), Measure.restrict_univ] at hij
    exact hij

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.BallAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set Metric MeasureTheory Topology Filter
open scoped ENNReal

section BallAverage
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuous_ball_integral {f : E → F} (hf : Integrable f μ) (r : ℝ) :
    Continuous (fun x ↦ ∫ y in ball x r, f y ∂μ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have hx₀ : ∀ᵐ y ∂μ, y ∉ sphere x₀ r := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using μ.addHaar_sphere x₀ r
  have hbound (x y : E) : ‖(ball x r).indicator f y‖ ≤ ‖f y‖ := by
    by_cases hy : y ∈ ball x r
    · simp only [indicator_of_mem hy]
      exact le_rfl
    · simp only [indicator_of_notMem hy, norm_zero]
      exact norm_nonneg _
  have hcont : ∀ᵐ y ∂μ, ContinuousAt (fun x ↦ (ball x r).indicator f y) x₀ := by
    filter_upwards [hx₀] with y hy
    have hdist : dist y x₀ ≠ r := hy
    rcases lt_or_gt_of_ne hdist with hlt | hgt
    · have hn : ∀ᶠ x in 𝓝 x₀, dist y x < r :=
        (continuous_const.dist continuous_id).continuousAt.eventually_lt_const hlt
      apply (show ContinuousAt (fun _ : E ↦ f y) x₀ from continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hn] with x hx
      simp only [indicator_of_mem (show y ∈ ball x r from hx)]
    · have hn : ∀ᶠ x in 𝓝 x₀, r < dist y x :=
        (continuous_const.dist continuous_id).continuousAt.eventually_const_lt hgt
      apply (show ContinuousAt (fun _ : E ↦ (0 : F)) x₀ from continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hn] with x hx
      simp only [indicator_of_notMem (show y ∉ ball x r from not_lt_of_ge hx.le)]
  have hh : ContinuousAt (fun x ↦ ∫ y, (ball x r).indicator f y ∂μ) x₀ :=
    continuousAt_of_dominated
      (Eventually.of_forall fun x ↦ hf.aestronglyMeasurable.indicator measurableSet_ball)
      (Eventually.of_forall fun x ↦ Eventually.of_forall (hbound x)) hf.norm hcont
  simpa only [integral_indicator measurableSet_ball] using hh

theorem continuous_ball_average {f : E → F} (hf : Integrable f μ) (r : ℝ) :
    Continuous (fun x ↦ ⨍ y in ball x r, f y ∂μ) := by
  simp_rw [setAverage_eq, measureReal_def, μ.addHaar_ball_center]
  exact continuous_const.smul (continuous_ball_integral hf r)

end BallAverage

section Representative
variable {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] [Nontrivial E] in
lemma ball_average_nonneg {u : E → ℝ} (hu : 0 ≤ᵐ[μ] u) (x : E) (r : ℝ) :
    0 ≤ ⨍ y in ball x r, u y ∂μ := by
  rw [setAverage_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg_of_ae (ae_restrict_of_ae hu))

omit [BorelSpace E] [Nontrivial E] in
lemma ball_average_le_const {u : E → ℝ} {x : E} {r c : ℝ}
    (hr : 0 < r) (hu : IntegrableOn u (ball x r) μ)
    (hle : u ≤ᵐ[μ.restrict (ball x r)] fun _ ↦ c) :
    (⨍ y in ball x r, u y ∂μ) ≤ c := by
  have hfin : μ (ball x r) ≠ ∞ := measure_ne_top_of_subset ball_subset_closedBall
    (isCompact_closedBall x r).measure_ne_top
  have hc : IntegrableOn (fun _ : E ↦ c) (ball x r) μ := integrableOn_const hfin
  calc
    (⨍ y in ball x r, u y ∂μ) ≤ ⨍ _y in ball x r, c ∂μ := by
      simp_rw [setAverage_eq, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (integral_mono_ae hu hc hle)
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = c := setAverage_const (ne_of_gt (Metric.measure_ball_pos μ x hr)) hfin c

theorem ball_infimum_representative_limit {u : E → ℝ} (hu : Integrable u μ)
    (hpos : 0 ≤ᵐ[μ] u) {Ω : Set E} (hΩ : IsOpen Ω)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ n, ∀ᵐ x ∂μ.restrict Ω, u x ≤ ⨍ y in ball x (r n), u y ∂μ) :
    let q := fun x ↦ ⨅ n, ⨍ y in ball x (r n), u y ∂μ
    UpperSemicontinuous q ∧ (∀ x, 0 ≤ q x) ∧
      (∀ᵐ x ∂μ.restrict Ω, u x ≤ q x) ∧
      ∀ x ∈ Ω, Tendsto (fun n ↦ ⨍ y in ball x (r n), u y ∂μ) atTop (𝓝 (q x)) := by
  let A := fun n x ↦ ⨍ y in ball x (r n), u y ∂μ
  have hApos (x : E) (n : ℕ) : 0 ≤ A n x := ball_average_nonneg hpos x (r n)
  have hb (x : E) : BddBelow (range fun n ↦ A n x) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hApos x n⟩
  have hq : UpperSemicontinuous (fun x ↦ ⨅ n, A n x) :=
    upperSemicontinuous_ciInf hb (fun n ↦ (continuous_ball_average hu (r n)).upperSemicontinuous)
  have hle : ∀ᵐ x ∂μ.restrict Ω, u x ≤ ⨅ n, A n x := by
    filter_upwards [ae_all_iff.mpr hmean] with x hx
    exact le_ciInf hx
  refine ⟨hq, fun x ↦ le_ciInf (hApos x), hle, ?_⟩
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (ciInf_le (hb x) n)
  · intro b hqb
    obtain ⟨c, hqc, hcb⟩ := exists_between hqb
    have hn := inter_mem (hΩ.mem_nhds hx) (hq x c hqc)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
    have hnδ : ∀ᶠ n in atTop, r n < δ := hr0.eventually (gt_mem_nhds hδ)
    filter_upwards [hnδ] with n hn
    have hsub : ball x (r n) ⊆ Ω := fun y hy ↦ (hball (ball_subset_ball hn.le hy)).1
    have huc : u ≤ᵐ[μ.restrict (ball x (r n))] fun _ ↦ c := by
      have hh := ae_mono (Measure.restrict_mono hsub le_rfl) hle
      filter_upwards [hh, ae_restrict_mem measurableSet_ball] with y hy hyb
      exact hy.trans (hball (ball_subset_ball hn.le hyb)).2.le
    exact (ball_average_le_const (hr n) hu.integrableOn huc).trans_lt hcb

lemma ball_average_eq_closedBall_average (u : E → ℝ) (x : E) (r : ℝ) :
    (⨍ y in ball x r, u y ∂μ) = ⨍ y in closedBall x r, u y ∂μ := by
  apply setAverage_congr
  exact ae_eq_of_subset_of_measure_ge ball_subset_closedBall
    (μ.addHaar_closedBall_eq_addHaar_ball x r).le measurableSet_ball.nullMeasurableSet
    (isCompact_closedBall x r).measure_ne_top

theorem ball_infimum_representative_ae {u : E → ℝ} (hu : Integrable u μ)
    (hpos : 0 ≤ᵐ[μ] u) {Ω : Set E} (hΩ : IsOpen Ω)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ n, ∀ᵐ x ∂μ.restrict Ω, u x ≤ ⨍ y in ball x (r n), u y ∂μ) :
    (fun x ↦ ⨅ n, ⨍ y in ball x (r n), u y ∂μ) =ᵐ[μ.restrict Ω] u := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average μ hu.locallyIntegrable 1
  have hlim := (ball_infimum_representative_limit hu hpos hΩ hr hr0 hmean).2.2.2
  have hr' : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Eventually.of_forall hr⟩
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  have hd := hx (fun _ : ℕ ↦ x) r hr' (Eventually.of_forall fun n ↦ by
    simpa only [one_mul] using (mem_closedBall_self (hr n).le))
  simp_rw [← ball_average_eq_closedBall_average] at hd
  exact tendsto_nhds_unique (hlim x hxΩ) hd

end Representative
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 u32 u33 u34 u35 u36 u37 u38

noncomputable section

namespace QuadricCounterexample
open Set Metric MeasureTheory Topology Filter Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
open Matrix
open scoped ComplexOrder

theorem quadraticValue_pointwise_limit
    {n : Type u9} [Fintype n] [DecidableEq n]
    {H : ℕ → Matrix n n ℂ} {q : (n → ℂ) → ℝ}
    (hH : ∀ k, (H k).PosSemidef)
    (hq : ∀ v, Tendsto (fun k ↦ quadraticValue (H k) v) atTop (𝓝 (q v))) :
    ∃ M : Matrix n n ℂ, M.PosSemidef ∧ ∀ v, q v = quadraticValue M v := by
  let M := matrixFromQuadratic q
  have hm (i j : n) : Tendsto (fun k ↦ H k i j) atTop (𝓝 (M i j)) := by
    change Tendsto (fun k ↦ H k i j) atTop (𝓝 (matrixFromQuadratic q i j))
    have hrec (k : ℕ) : matrixFromQuadratic (quadraticValue (H k)) i j = H k i j :=
      congrFun (congrFun (matrixFromQuadratic_value (hH k).1) i) j
    simp_rw [← hrec, matrixFromQuadratic, Complex.mk_eq_add_mul_I]
    exact (((hq _).sub (hq _)).sub (hq _)).div_const 2 |>.ofReal |>.add
      ((((hq _).add (hq _)).sub (hq _)).div_const 2 |>.ofReal |>.mul_const Complex.I)
  have hmat : Tendsto H atTop (𝓝 M) :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ hm i j
  have hherm : M.IsHermitian := by
    ext i j
    exact tendsto_nhds_unique ((hm j i).star)
      ((hm i j).congr' (Filter.Eventually.of_forall fun k ↦ ((hH k).1.apply i j).symm))
  have hform (v : n → ℂ) :
      Tendsto (fun k ↦ star v ⬝ᵥ ((H k) *ᵥ v)) atTop (𝓝 (star v ⬝ᵥ (M *ᵥ v))) := by
    have hc : Continuous (fun N : Matrix n n ℂ ↦ star v ⬝ᵥ (N *ᵥ v)) := by fun_prop
    exact hc.continuousAt.tendsto.comp hmat
  refine ⟨M, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun v ↦ ?_), fun v ↦ ?_⟩
  · exact ge_of_tendsto (hform v)
      (Filter.Eventually.of_forall fun k ↦ (hH k).dotProduct_mulVec_nonneg v)
  · exact tendsto_nhds_unique (hq v) (Complex.continuous_re.continuousAt.tendsto.comp (hform v))

lemma isClosed_matrix_positive_semidefinite {n : Type u10} [Fintype n] [DecidableEq n] :
    IsClosed {M : Matrix n n ℂ | M.PosSemidef} := by
  have heq : {M : Matrix n n ℂ | M.PosSemidef} =
      {M | M.conjTranspose = M} ∩ ⋂ v : n → ℂ, {M | 0 ≤ star v ⬝ᵥ (M *ᵥ v)} := by
    ext M
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun h ↦ ⟨h.1, h.dotProduct_mulVec_nonneg⟩,
      fun h ↦ Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h.1 h.2⟩
  rw [heq]
  refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun v ↦ ?_)
  exact isClosed_le continuous_const (by fun_prop)

lemma convex_matrix_positive_semidefinite {n : Type u11} [Fintype n] [DecidableEq n] :
    Convex ℝ {M : Matrix n n ℂ | M.PosSemidef} := by
  intro M hM N hN a b ha hb _
  exact (hM.smul ha).add (hN.smul hb)

attribute [local instance] OAI.QuadricCounterexample.matrixContinuousENorm
lemma quadraticValue_average {α : Type u14} {n : Type u15} [MeasurableSpace α]
    [Fintype n] {μ : Measure α} {H : α → Matrix n n ℂ}
    (hH : Integrable H μ) (v : n → ℂ) :
    quadraticValue (⨍ x, H x ∂μ) v = ⨍ x, quadraticValue (H x) v ∂μ := by
  exact ((quadraticValueCLM v).integral_comp_comm hH.to_average).symm

lemma positive_semidefinite_average {α : Type u16} {n : Type u17} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {H : α → Matrix n n ℂ} (hH : Integrable H μ)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef) : (⨍ x, H x ∂μ).PosSemidef :=
  convex_matrix_positive_semidefinite.average_mem isClosed_matrix_positive_semidefinite hpos hH

theorem matrix_ball_infimum_representative
    {E : Type u19} {n : Type u20} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ}
    (hH : Integrable H μ) (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef)
    {Ω : Set E} (hΩ : IsOpen Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ v k, ∀ᵐ x ∂μ.restrict Ω,
      quadraticValue (H x) v ≤ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) :
    ∀ x ∈ Ω, ∃ M : Matrix n n ℂ, M.PosSemidef ∧ ∀ v,
      (⨅ k, ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) = quadraticValue M v := by
  intro x hx
  let Hbar : ℕ → Matrix n n ℂ := fun k ↦ ⨍ y in ball x (r k), H y ∂μ
  have hbar (k : ℕ) : (Hbar k).PosSemidef := by
    have : Fact (μ (ball x (r k)) < ∞) := ⟨measure_ball_lt_top⟩
    have : NeZero (μ (ball x (r k))) :=
      ⟨ne_of_gt (Metric.measure_ball_pos μ x (hr k))⟩
    exact positive_semidefinite_average hH.integrableOn (ae_restrict_of_ae hpos)
  apply quadraticValue_pointwise_limit hbar
  intro v
  have hi : Integrable (fun y ↦ quadraticValue (H y) v) μ :=
    (quadraticValueCLM v).integrable_comp hH
  have hp : 0 ≤ᵐ[μ] fun y ↦ quadraticValue (H y) v :=
    hpos.mono fun y hy ↦ quadraticValue_nonneg hy v
  have hl := (ball_infimum_representative_limit hi hp hΩ hr hr0 (hmean v)).2.2.2 x hx
  simpa only [Hbar, quadraticValue_average hH.integrableOn] using hl

lemma continuous_joint_averaged_quadratic
    {E : Type u21} {n : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] {H : E → Matrix n n ℂ} (hH : Integrable H μ) (r : ℝ) :
    Continuous (fun p : E × (n → ℂ) ↦ quadraticValue (⨍ y in ball p.1 r, H y ∂μ) p.2) := by
  have hc : Continuous (fun p : E × (n → ℂ) ↦ ⨍ y in ball p.1 r, H y ∂μ) :=
    (continuous_ball_average hH r).comp continuous_fst
  unfold quadraticValue
  fun_prop

lemma joint_upperSemicontinuous_infimum
    {E : Type u23} {n : Type u24} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] {H : E → Matrix n n ℂ} (hH : Integrable H μ)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef) (r : ℕ → ℝ) :
    UpperSemicontinuous (fun p : E × (n → ℂ) ↦
      ⨅ k, ⨍ y in ball p.1 (r k), quadraticValue (H y) p.2 ∂μ) := by
  apply upperSemicontinuous_ciInf
  · intro p
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact ball_average_nonneg (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy p.2) _ _
  · intro k
    simpa only [quadraticValue_average hH.integrableOn] using
      (continuous_joint_averaged_quadratic hH (r k)).upperSemicontinuous

lemma matrixFromQuadratic_ae_recovery {α : Type u25} {n : Type u26} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] {μ : Measure α}
    {H : α → Matrix n n ℂ} {q : α → (n → ℂ) → ℝ}
    (hH : ∀ᵐ x ∂μ, (H x).IsHermitian)
    (hq : ∀ v, (fun x ↦ q x v) =ᵐ[μ] fun x ↦ quadraticValue (H x) v) :
    (fun x ↦ matrixFromQuadratic (q x)) =ᵐ[μ] H := by
  have hd := ae_all_iff.mpr (fun i : n ↦ hq (Pi.single i 1))
  have hs := ae_all_iff.mpr (fun i : n ↦ ae_all_iff.mpr
    (fun j : n ↦ hq (Pi.single i 1 + Pi.single j 1)))
  have hi := ae_all_iff.mpr (fun i : n ↦ ae_all_iff.mpr
    (fun j : n ↦ hq (Pi.single i 1 + Complex.I • Pi.single j 1)))
  filter_upwards [hH, hd, hs, hi] with x hx hdx hsx hix
  rw [← matrixFromQuadratic_value hx]
  ext i j
  all_goals simp only [matrixFromQuadratic, hdx, hsx, hix]

theorem matrix_regularized_representative
    {E : Type u27} {n : Type u28} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
    [Fintype n] [DecidableEq n] {H : E → Matrix n n ℂ}
    (hH : Integrable H μ) (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef)
    {Ω : Set E} (hΩ : IsOpen Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ v k, ∀ᵐ x ∂μ.restrict Ω,
      quadraticValue (H x) v ≤ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) :
    ∃ M : E → Matrix n n ℂ,
      (∀ x ∈ Ω, (M x).PosSemidef) ∧ M =ᵐ[μ.restrict Ω] H ∧
      UpperSemicontinuousOn (fun p : E × (n → ℂ) ↦ quadraticValue (M p.1) p.2)
        (Ω ×ˢ univ) ∧
      ∀ x ∈ Ω, ∀ v, Tendsto
        (fun k ↦ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ)
        atTop (𝓝 (quadraticValue (M x) v)) := by
  let q := fun x v ↦ ⨅ k, ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ
  let M := fun x ↦ matrixFromQuadratic (q x)
  have hxM (x : E) (hx : x ∈ Ω) : (M x).PosSemidef ∧ ∀ v, q x v = quadraticValue (M x) v := by
    obtain ⟨N, hN, hqN⟩ := matrix_ball_infimum_representative hH hpos hΩ hr hr0 hmean x hx
    have he : M x = N := by
      change matrixFromQuadratic (q x) = N
      rw [show q x = quadraticValue N from funext hqN, matrixFromQuadratic_value hN.1]
    simpa only [he] using And.intro hN hqN
  have hqae (v : n → ℂ) : (fun x ↦ q x v) =ᵐ[μ.restrict Ω]
      fun x ↦ quadraticValue (H x) v :=
    ball_infimum_representative_ae ((quadraticValueCLM v).integrable_comp hH)
      (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy v) hΩ hr hr0 (hmean v)
  refine ⟨M, fun x hx ↦ (hxM x hx).1,
    matrixFromQuadratic_ae_recovery (ae_restrict_of_ae (hpos.mono fun _ h ↦ h.1)) hqae, ?_, ?_⟩
  · intro p hp
    apply UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (((joint_upperSemicontinuous_infimum hH hpos r).upperSemicontinuousOn
        (Ω ×ˢ (univ : Set (n → ℂ)))) p hp) hp
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hxM z.1 hz.1).2 z.2
  · intro x hx v
    have hl := (ball_infimum_representative_limit ((quadraticValueCLM v).integrable_comp hH)
      (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy v) hΩ hr hr0 (hmean v)).2.2.2 x hx
    change Tendsto (fun k ↦ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ)
      atTop (𝓝 (quadraticValue (M x) v))
    rw [← (hxM x hx).2 v]
    exact hl

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

lemma integral_ball_translate
    {E : Type u29} {F : Type u30} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] (f : E → F) (x : E) (r : ℝ) :
    (∫ a in ball (0 : E) r, f (x + a) ∂μ) = ∫ y in ball x r, f y ∂μ := by
  have he : (fun a : E ↦ x + a) ⁻¹' ball x r = ball 0 r := by
    ext a
    simp only [mem_preimage, mem_ball, dist_self_add_left, dist_zero_right]
  have hh := ((MeasurePreserving.id μ).add_left μ x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding f (ball x r)
  simpa only [id_eq, he] using hh

theorem DiskPshOn.base_ball_average
    {E : Type u31} {V : Type u32} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [LocallyCompactSpace V]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {Ω U : Set E} (hU : IsOpen U) {q : E × V → ℝ}
    (hq : DiskPshOn (Ω ×ˢ univ) q) (hc : ContinuousOn q (Ω ×ˢ univ))
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ a ∈ closedBall (0 : E) r, ∀ x ∈ U, x + a ∈ Ω) :
    DiskPshOn (U ×ˢ univ) (fun p ↦ ⨍ y in ball p.1 r, q (y,p.2) ∂μ) := by
  let K := closedBall (0 : E) r
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) r)
  let : Fact (μ (ball (0 : E) r) < ∞) := ⟨measure_ball_lt_top⟩
  have hm0 : μ (ball (0 : E) r) ≠ 0 := ne_of_gt (Metric.measure_ball_pos μ 0 hr)
  let ν : Measure E := (μ (ball (0 : E) r))⁻¹ • μ.restrict (ball 0 r)
  let : IsFiniteMeasure ν := Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hm0)
  let η : Measure K := Measure.comap Subtype.val ν
  let F := fun a : K ↦ fun p : E × V ↦ q (p.1 + a, p.2)
  have hFc : ContinuousOn (Function.uncurry F) (univ ×ˢ (U ×ˢ univ)) := by
    exact hc.comp (by fun_prop) (fun p hp ↦ ⟨hb p.1 p.1.property p.2.1 hp.2.1, mem_univ _⟩)
  have hFp (a : K) : DiskPshOn (U ×ˢ univ) (F a) := by
    exact hq.comp (by fun_prop) (fun p hp ↦ ⟨hb a a.property p.1 hp.1, mem_univ _⟩)
  have hi := DiskPshOn.integral_compact_parameter (μ := η) (hU.prod isOpen_univ) hFc hFp
  have he (p : E × V) : (∫ a, F a p ∂η) = ⨍ y in ball p.1 r, q (y,p.2) ∂μ := by
    change (∫ a : K, q (p.1 + a, p.2) ∂(Measure.comap Subtype.val ν)) = _
    rw [integral_subtype_comap (show MeasurableSet K from measurableSet_closedBall) (fun a : E ↦ q (p.1 + a, p.2))]
    change (∫ a in K, q (p.1 + a, p.2) ∂((μ (ball (0 : E) r))⁻¹ •
      μ.restrict (ball 0 r))) = _
    rw [Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict measurableSet_closedBall]
    rw [show K ∩ ball (0 : E) r = ball 0 r from inter_eq_right.mpr ball_subset_closedBall]
    rw [integral_ball_translate (fun y : E ↦ q (y,p.2)) p.1 r, setAverage_eq, measureReal_def, μ.addHaar_ball_center]
    simp only [ENNReal.toReal_inv, μ.addHaar_ball_center]
  simpa only [he] using hi

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

lemma DiskPshOn.pointwise_limit_of_continuous_bound {E : Type u33} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ω : Set E} {u : ℕ → E → ℝ} {q B : E → ℝ}
    (hu : ∀ n, DiskPshOn Ω (u n)) (hq : UpperSemicontinuousOn q Ω)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (q x)))
    (hB : Continuous B) (hbound : ∀ n, ∀ x ∈ Ω, ‖u n x‖ ≤ B x) :
    DiskPshOn Ω q := by
  apply DiskPshOn.pointwise_limit hu hq hlim
  intro K hK hKΩ
  obtain ⟨C, hC⟩ := hK.bddAbove_image hB.continuousOn
  exact ⟨C, fun n x hx ↦ (hbound n x (hKΩ hx)).trans (hC (mem_image_of_mem B hx))⟩

open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] OAI.QuadricCounterexample.instContinuousENormMatrixComplexOfFintype_solutions
theorem averaged_matrix_limit_psh
    {E : Type u35} {n : Type u36} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    [Fintype n] [DecidableEq n]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {H : E → Matrix n n ℂ} {Hm : ℕ → E → Matrix n n ℂ}
    {Ω U : Set E} (hU : IsOpen U)
    (hH : Integrable H μ) (hHm : ∀ m, Integrable (Hm m) μ)
    (hpos : ∀ m, ∀ᵐ x ∂μ, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {C r : ℝ} (hr : 0 < r)
    (hb : ∀ a ∈ closedBall (0 : E) r, ∀ x ∈ U, x + a ∈ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2)
    (hl : ∀ x ∈ U, ∀ v, Tendsto
      (fun m ↦ ⨍ y in ball x r, quadraticValue (Hm m y) v ∂μ)
      atTop (𝓝 (⨍ y in ball x r, quadraticValue (H y) v ∂μ))) :
    DiskPshOn (U ×ˢ univ)
      (fun p : E × (n → ℂ) ↦ ⨍ y in ball p.1 r, quadraticValue (H y) p.2 ∂μ) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hcq := continuous_joint_averaged_quadratic hH r
  have huc : UpperSemicontinuousOn
      (fun p : E × (n → ℂ) ↦ ⨍ y in ball p.1 r, quadraticValue (H y) p.2 ∂μ)
      (U ×ˢ univ) := by
    simpa only [quadraticValue_average hH.integrableOn] using hcq.upperSemicontinuous.upperSemicontinuousOn (U ×ˢ univ)
  apply DiskPshOn.pointwise_limit_of_continuous_bound
    (fun m ↦ (hp m).base_ball_average hU (hc m) hr hb) huc
    (fun p hp ↦ hl p.1 hp.1 p.2) (B := fun p : E × (n → ℂ) ↦ C * ‖p.2‖ ^ 2)
    (by fun_prop)
  intro m p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (ball_average_nonneg
    ((hpos m).mono fun _ hy ↦ quadraticValue_nonneg hy p.2) _ _)]
  have hi : Integrable (fun y : E ↦ quadraticValue (Hm m y) p.2) μ :=
    (quadraticValueCLM p.2).integrable_comp (hHm m)
  apply ball_average_le_const (μ := μ) (x := p.1) hr hi.integrableOn
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  apply hbound m y _ p.2
  have ha : y - p.1 ∈ closedBall (0 : E) r := by
    simpa only [mem_closedBall, dist_zero_right, ← dist_eq_norm] using (mem_ball.mp hy).le
  simpa only [add_sub_cancel] using hb (y-p.1) ha p.1 hp.1

theorem joint_matrix_regularized_representative
    {E : Type u37} {n : Type u38} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    [Fintype n] [DecidableEq n]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    {H : E → Matrix n n ℂ} {Hm : ℕ → E → Matrix n n ℂ}
    {Ω U : Set E} (hU : IsOpen U)
    (hH : Integrable H μ) (hHm : ∀ m, Integrable (Hm m) μ)
    (hpos : ∀ᵐ x ∂μ, (H x).PosSemidef)
    (hposm : ∀ m, ∀ᵐ x ∂μ, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : E × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {C : ℝ} {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hb : ∀ k, ∀ a ∈ closedBall (0 : E) (r k), ∀ x ∈ U, x + a ∈ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2)
    (hl : ∀ k, ∀ x ∈ U, ∀ v, Tendsto
      (fun m ↦ ⨍ y in ball x (r k), quadraticValue (Hm m y) v ∂μ)
      atTop (𝓝 (⨍ y in ball x (r k), quadraticValue (H y) v ∂μ)))
    (hmean : ∀ v k, ∀ᵐ x ∂μ.restrict U,
      quadraticValue (H x) v ≤ ⨍ y in ball x (r k), quadraticValue (H y) v ∂μ) :
    ∃ M : E → Matrix n n ℂ,
      (∀ x ∈ U, (M x).PosSemidef) ∧ M =ᵐ[μ.restrict U] H ∧
      DiskPshOn (U ×ˢ univ) (fun p : E × (n → ℂ) ↦ quadraticValue (M p.1) p.2) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  obtain ⟨M, hM, hMae, hMusc, hMl⟩ :=
    matrix_regularized_representative hH hpos hU hr hr0 hmean
  refine ⟨M, hM, hMae, ?_⟩
  apply DiskPshOn.pointwise_limit_of_continuous_bound
    (fun k ↦ averaged_matrix_limit_psh hU hH hHm hposm hc hp (hr k) (hb k) hbound (hl k))
    hMusc (fun p hp ↦ hMl p.1 hp.1 p.2)
    (B := fun p : E × (n → ℂ) ↦ C * ‖p.2‖ ^ 2) (by fun_prop)
  intro k p hpU
  rw [Real.norm_eq_abs, abs_of_nonneg (ball_average_nonneg
    (hpos.mono fun _ hy ↦ quadraticValue_nonneg hy p.2) _ _)]
  apply le_of_tendsto (hl k p.1 hpU.1 p.2)
  apply Eventually.of_forall
  intro m
  have hi : Integrable (fun y : E ↦ quadraticValue (Hm m y) p.2) μ :=
    (quadraticValueCLM p.2).integrable_comp (hHm m)
  apply ball_average_le_const (μ := μ) (x := p.1) (hr k) hi.integrableOn
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  apply hbound m y _ p.2
  have ha : y - p.1 ∈ closedBall (0 : E) (r k) := by
    simpa only [mem_closedBall, dist_zero_right, ← dist_eq_norm] using (mem_ball.mp hy).le
  simpa only [add_sub_cancel] using hb k (y-p.1) ha p.1 hpU.1

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31

noncomputable section

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory
open scoped ENNReal

lemma tendsto_dual_of_tendsto_inner
    {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {f : ℕ → E} {w : E}
    (h : ∀ v : E, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v)))
    (d : StrongDual ℂ E) : Tendsto (fun k ↦ d (f k)) atTop (𝓝 (d w)) := by
  let v := (InnerProductSpace.toDual ℂ E).symm d
  have h' := (h v).star
  have he (z : E) : star (inner ℂ z v) = d z := by
    change (starRingEnd ℂ) (inner ℂ z v) = d z
    rw [inner_conj_symm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [he] using h'

lemma tendsto_real_dual_of_tendsto_inner
    {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {f : ℕ → E} {w : E}
    (h : ∀ v : E, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v)))
    (d : StrongDual ℝ E) : Tendsto (fun k ↦ d (f k)) atTop (𝓝 (d w)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_dual_of_tendsto_inner h (StrongDual.extendRCLike d))
  have he (y : E) : ((StrongDual.extendRCLike d) y : ℂ).re = d y :=
    StrongDual.re_extendRCLike_apply (𝕜 := ℂ) d y
  simpa only [Function.comp_def, he] using ht

lemma mem_closed_convex_of_weak_limit
    {E : Type u3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {C : Set E} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    {f : ℕ → E} {w : E} (hf : ∀ k, f k ∈ C)
    (hlim : ∀ v : E, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    w ∈ C := by
  by_contra hw
  obtain ⟨d, r, hr, hw⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconvex hclosed hw
  have hl := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_dual_of_tendsto_inner hlim d)
  have he : ∀ᶠ k in atTop, (d (f k)).re ≤ r :=
    Eventually.of_forall fun k ↦ (hr (f k) (hf k)).le
  exact hw.not_ge (le_of_tendsto hl he)

lemma isClosed_ae_linear_constraint {α : Type u4} {E : Type u5} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (Ω : Set α)
    (ℓ : E →L[ℝ] ℝ) (A : α → Lp E p μ →L[ℝ] ℝ) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ.restrict Ω, ℓ (f x) ≤ A x f} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, hφmono, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr hf
  filter_upwards [hall, ae_restrict_of_ae hφ] with x hx hlim
  have hleft := ℓ.continuous.continuousAt.tendsto.comp hlim
  have hright := (A x).continuous.continuousAt.tendsto.comp
    (hfg.comp hφmono.tendsto_atTop)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n ↦ hx (φ n))

lemma convex_ae_linear_constraint {α : Type u6} {E : Type u7} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (Ω : Set α)
    (ℓ : E →L[ℝ] ℝ) (A : α → Lp E p μ →L[ℝ] ℝ) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ.restrict Ω, ℓ (f x) ≤ A x f} := by
  intro f hf g hg a b ha hb _
  filter_upwards [hf, hg, ae_restrict_of_ae (Lp.coeFn_add (a • f) (b • g)),
    ae_restrict_of_ae (Lp.coeFn_smul a f),
    ae_restrict_of_ae (Lp.coeFn_smul b g)] with x hx hy hadd hsmul₁ hsmul₂
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂]
  simp only [Pi.smul_apply, map_add, map_smul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

theorem ae_linear_constraint_of_weak_limit {α : Type u8} {E : Type u9} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (Ω : Set α) (ℓ : E →L[ℝ] ℝ)
    (A : α → Lp E 2 μ →L[ℝ] ℝ)
    {f : ℕ → Lp E 2 μ} {w : Lp E 2 μ}
    (hf : ∀ k, ∀ᵐ x ∂μ.restrict Ω, ℓ (f k x) ≤ A x (f k))
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ᵐ x ∂μ.restrict Ω, ℓ (w x) ≤ A x w :=
  mem_closed_convex_of_weak_limit (isClosed_ae_linear_constraint Ω ℓ A)
    (convex_ae_linear_constraint Ω ℓ A) hf hw

lemma setAverageL2Functional_apply {α : Type u12} {E : Type u13} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (ℓ : E →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp E 2 μ) :
    setAverageL2Functional ℓ hs hμs f = ⨍ x in s, ℓ (f x) ∂μ := by
  let z := (InnerProductSpace.toDual ℂ E).symm (StrongDual.extendRCLike ℓ)
  have hz (y : E) : inner ℂ z y = StrongDual.extendRCLike ℓ y :=
    InnerProductSpace.toDual_symm_apply
  change (μ s).toReal⁻¹ * (inner ℂ (indicatorConstLp 2 hs hμs z) f).re = _
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ f hs z hμs]
  simp_rw [hz]
  have hg : (∫ x in s, (StrongDual.extendRCLike (𝕜 := ℂ) ℓ) (f x) ∂μ).re =
      ∫ x in s, ((StrongDual.extendRCLike (𝕜 := ℂ) ℓ) (f x)).re ∂μ :=
    (integral_re ((StrongDual.extendRCLike (𝕜 := ℂ) ℓ).integrable_comp
      (integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs))).symm
  rw [hg]
  have he (y : E) : ((StrongDual.extendRCLike ℓ) y : ℂ).re = ℓ y :=
    StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ℓ y
  simp only [he, setAverage_eq, smul_eq_mul, measureReal_def]

lemma tendsto_setAverage_of_tendsto_inner {α : Type u14} {E : Type u15} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (ℓ : E →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : ℕ → Lp E 2 μ} {w : Lp E 2 μ}
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    Tendsto (fun k ↦ ⨍ x in s, ℓ (f k x) ∂μ) atTop (𝓝 (⨍ x in s, ℓ (w x) ∂μ)) := by
  simpa only [setAverageL2Functional_apply] using
    tendsto_real_dual_of_tendsto_inner hw (setAverageL2Functional ℓ hs hμs)

theorem ae_submean_of_weak_limit {α : Type u16} {E : Type u17} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (Ω : Set α) (ℓ : E →L[ℝ] ℝ)
    (S : α → Set α) (hS : ∀ x, MeasurableSet (S x)) (hμS : ∀ x, μ (S x) ≠ ∞)
    {f : ℕ → Lp E 2 μ} {w : Lp E 2 μ}
    (hf : ∀ k, ∀ᵐ x ∂μ.restrict Ω, ℓ (f k x) ≤ ⨍ y in S x, ℓ (f k y) ∂μ)
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ᵐ x ∂μ.restrict Ω, ℓ (w x) ≤ ⨍ y in S x, ℓ (w y) ∂μ := by
  have hc := ae_linear_constraint_of_weak_limit Ω ℓ
    (fun x ↦ setAverageL2Functional ℓ (hS x) (hμS x))
    (fun k ↦ by simpa only [setAverageL2Functional_apply] using hf k) hw
  simpa only [setAverageL2Functional_apply] using hc

end QuadricCounterexample

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

lemma isClosed_ae_mem_Lp {α : Type u18} {E : Type u19} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Set E} (hC : IsClosed C) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, f n x ∈ C := ae_all_iff.mpr hf
  filter_upwards [hall, hφ] with x hx hlim
  exact hC.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ hx (φ n))

lemma convex_ae_mem_Lp {α : Type u20} {E : Type u21} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hx hy hadd hsmul₁ hsmul₂
  change (a • f + b • g) x ∈ C
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂]
  exact hC hx hy ha hb hab

lemma continuous_coefficientsToMatrix {n : Type u23} [Fintype n] :
    Continuous (coefficientsToMatrix (n := n)) :=
  LinearMap.continuous_of_finiteDimensional _

lemma coefficientsQuadraticCLM_apply {n : Type u25} [Fintype n]
    (v : n → ℂ) (c : EuclideanSpace ℂ (n × n)) :
    coefficientsQuadraticCLM v c = quadraticValue (coefficientsToMatrix c) v := rfl

lemma weak_coefficients_positive {α : Type u26} {n : Type u27} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] {μ : Measure α}
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 μ}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 μ}
    (hf : ∀ m, ∀ᵐ x ∂μ, (coefficientsToMatrix (f m x)).PosSemidef)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ᵐ x ∂μ, (coefficientsToMatrix (w x)).PosSemidef := by
  have hclosed : IsClosed {c : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix c).PosSemidef} :=
    isClosed_matrix_positive_semidefinite.preimage continuous_coefficientsToMatrix
  have hconvex : Convex ℝ {c : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix c).PosSemidef} :=
    convex_matrix_positive_semidefinite.linear_preimage (coefficientsToMatrix.restrictScalars ℝ)
  exact mem_closed_convex_of_weak_limit (isClosed_ae_mem_Lp hclosed)
    (convex_ae_mem_Lp hconvex) hf hw

attribute [local instance] OAI.QuadricCounterexample.instContinuousENormMatrixComplexOfFintype_solutions_1
lemma weak_quadratic_averages {n : Type u29} [Fintype n]
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ}
    (hf : ∀ m, (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v)))
    (x : ℂ × ℂ) (r : ℝ) (v : n → ℂ) :
    Tendsto (fun m ↦ ⨍ y in ball x r, quadraticValue (Hm m y) v) atTop
      (𝓝 (⨍ y in ball x r, quadraticValue (coefficientsToMatrix (w y)) v)) := by
  have hlim := tendsto_setAverage_of_tendsto_inner (coefficientsQuadraticCLM v)
    (measurableSet_ball (x := x) (ε := r)) measure_ball_lt_top.ne hw
  have he (m : ℕ) : (⨍ y in ball x r, coefficientsQuadraticCLM v (f m y)) =
      ⨍ y in ball x r, quadraticValue (Hm m y) v := by
    apply average_congr
    exact (ae_restrict_of_ae (hf m)).mono fun y hy ↦ by
      exact congrArg (fun M ↦ quadraticValue M v) hy
  simp_rw [he] at hlim
  exact hlim

lemma weak_quadratic_submean {n : Type u30} [Fintype n]
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ}
    {Ω U : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hf : ∀ m, (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v)))
    (hHm : ∀ m, Integrable (Hm m))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {r : ℝ} (hr : 0 < r) (hb : ∀ x ∈ U, closedBall x r ⊆ Ω) (v : n → ℂ) :
    ∀ᵐ x ∂volume.restrict U,
      quadraticValue (coefficientsToMatrix (w x)) v ≤
        ⨍ y in ball x r, quadraticValue (coefficientsToMatrix (w y)) v := by
  have hall : ∀ m, ∀ᵐ x ∂volume.restrict U, coefficientsQuadraticCLM v (f m x) ≤
      ⨍ y in ball x r, coefficientsQuadraticCLM v (f m y) := by
    intro m
    have he (x : ℂ × ℂ) : (⨍ y in ball x r, coefficientsQuadraticCLM v (f m y)) =
        ⨍ y in ball x r, quadraticValue (Hm m y) v := by
      apply average_congr
      exact (ae_restrict_of_ae (hf m)).mono fun y hy ↦ by
        exact congrArg (fun M ↦ quadraticValue M v) hy
    have hbase : DiskPshOn Ω (fun x ↦ quadraticValue (Hm m x) v) :=
      (hp m).comp (f := fun x ↦ (x,v)) (by fun_prop) (fun _ hx ↦ ⟨hx, mem_univ _⟩)
    have hi : Integrable (fun x ↦ quadraticValue (Hm m x) v) :=
      (quadraticValueCLM v).integrable_comp (hHm m)
    filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae (hf m)] with x hx hfx
    rw [coefficientsQuadraticCLM_apply, hfx, he]
    exact hbase.base_average_submean hΩ (hb x hx (mem_closedBall_self hr.le)) hr
      (hb x hx) hi.integrableOn
  have hs := ae_submean_of_weak_limit U (coefficientsQuadraticCLM v)
    (fun x ↦ ball x r) (fun _ ↦ measurableSet_ball) (fun _ ↦ measure_ball_lt_top.ne) hall hw
  simpa only [coefficientsQuadraticCLM_apply] using hs

local instance instIsAddHaarMeasureProdComplexVolume_solutions : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

theorem weak_quadratic_psh_representative {n : Type u31} [Fintype n] [DecidableEq n]
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ}
    {Ω U : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hf : ∀ m, (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v)))
    (hwL1 : Integrable (fun x ↦ w x)) (hHm : ∀ m, Integrable (Hm m))
    (hposm : ∀ m, ∀ᵐ x ∂volume, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {C : ℝ} {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hb : ∀ k, ∀ x ∈ U, closedBall x (r k) ⊆ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2) :
    ∃ M : (ℂ × ℂ) → Matrix n n ℂ,
      (∀ x ∈ U, (M x).PosSemidef) ∧
      M =ᵐ[volume.restrict U] (fun x ↦ coefficientsToMatrix (w x)) ∧
      DiskPshOn (U ×ˢ univ)
        (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (M p.1) p.2) := by
  have hH : Integrable (fun x ↦ coefficientsToMatrix (w x)) :=
    coefficientsToMatrix.toContinuousLinearMap.integrable_comp hwL1
  have hpos : ∀ᵐ x ∂volume, (coefficientsToMatrix (w x)).PosSemidef := by
    apply weak_coefficients_positive _ hw
    intro m
    filter_upwards [hf m, hposm m] with x hx hp
    rwa [hx]
  apply joint_matrix_regularized_representative hU hH hHm hpos hposm hc hp hr hr0
    _ hbound _ _
  · intro k a ha x hx
    apply hb k x hx
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using ha
  · intro k x _ v
    exact weak_quadratic_averages hf hw x (r k) v
  · intro v k
    exact weak_quadratic_submean hΩ hU hf hw hHm hp (hr k) (hb k) v

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

lemma isClosed_bounded_positive_coefficients {n : Type u2} [Fintype n] [DecidableEq n]
    (R : ℝ) : IsClosed {v : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R} := by
  exact (isClosed_matrix_positive_semidefinite.preimage continuous_coefficientsToMatrix).inter
    (isClosed_le continuous_norm continuous_const)

lemma convex_bounded_positive_coefficients {n : Type u3} [Fintype n] [DecidableEq n]
    (R : ℝ) : Convex ℝ {v : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R} := by
  have hc : Convex ℝ {v : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix v).PosSemidef} :=
    convex_matrix_positive_semidefinite.linear_preimage
      (coefficientsToMatrix.restrictScalars ℝ)
  refine hc.inter ?_
  intro x hx y hy a b ha hb hab
  change ‖a • x + b • y‖ ≤ R
  calc
    ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
    _ = a * ‖x‖ + b * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul, hab, one_mul]

lemma isClosed_ae_variable_mem_Lp {α : Type u5} {E : Type u6} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : α → Set E} (hC : ∀ x, IsClosed (C x)) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C x} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, f n x ∈ C x := ae_all_iff.mpr hf
  filter_upwards [hall, hφ] with x hx hlim
  exact (hC x).mem_of_tendsto hlim (Eventually.of_forall fun n ↦ hx (φ n))

lemma convex_ae_variable_mem_Lp {α : Type u7} {E : Type u8} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : α → Set E} (hC : ∀ x, Convex ℝ (C x)) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C x} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hx hy hadd hsmul₁ hsmul₂
  change (a • f + b • g) x ∈ C x
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂]
  exact hC x hx hy ha hb hab

lemma L2_integrable_of_finite_support {α : Type u9} {E : Type u10} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp E 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : Integrable (fun x ↦ f x) μ := by
  have hi : Integrable (s.indicator (fun x ↦ f x)) μ :=
    (integrable_indicator_iff hs).mpr (integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs)
  apply hi.congr
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs]
  · simp only [indicator_of_notMem hxs, hx hxs]

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

local instance instContinuousENormMatrixComplexOfFintype_solutions_2_r6716fe_1 {n : Type u13} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))
lemma matrix_coefficients_memLp {α : Type u16} {n : Type u17} [MeasurableSpace α]
    [Fintype n] {μ : Measure α} {H : α → Matrix n n ℂ} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hH : AEStronglyMeasurable H μ)
    {R : ℝ} (_hR : 0 ≤ R)
    (hb : ∀ᵐ x ∂μ, ‖matrixToCoefficients (H x)‖ ≤ R ∧ (x ∉ s → H x = 0)) :
    MemLp (fun x ↦ matrixToCoefficients (H x)) 2 μ := by
  apply (memLp_indicator_const 2 hs R (Or.inr hμs)).mono'
    ((LinearMap.continuous_of_finiteDimensional matrixToCoefficients).comp_aestronglyMeasurable hH)
  filter_upwards [hb] with x hx
  by_cases hxs : x ∈ s
  · simpa only [indicator_of_mem hxs] using hx.1
  · simp only [indicator_of_notMem hxs, hx.2 hxs, map_zero, norm_zero, le_refl]

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
local instance instIsAddHaarMeasureProdComplexVolume_solutions_2 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

lemma DiskPshOn.moving_base_mass {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) {x y : ℂ × ℂ} {r a : ℝ}
    (hr : 0 < r) (hxy : dist y x < r) (hb : closedBall x (3*r) ⊆ Ω)
    (hpos : ∀ z ∈ ball x (2*r), 0 ≤ q z)
    (hi : IntegrableOn q (ball x (2*r))) (ha : a ≤ q y) :
    (volume (ball (0 : ℂ × ℂ) r)).toReal * a ≤ ∫ z in ball x (2*r), q z := by
  have hsub : ball y r ⊆ ball x (2*r) :=
    ball_subset_ball' (by linarith)
  have hcb : closedBall y r ⊆ Ω := by
    apply Subset.trans _ hb
    exact closedBall_subset_closedBall' (by linarith)
  have hy : y ∈ Ω := hcb (mem_closedBall_self hr.le)
  have hs := hq.base_submean hΩ hy hr hcb (hi.mono_set hsub)
  calc
    (volume (ball (0 : ℂ × ℂ) r)).toReal * a = (volume (ball y r)).toReal * a := by
      rw [Measure.addHaar_ball_center _ y, Measure.addHaar_ball_center _ (0 : ℂ × ℂ)]
    _ ≤ (volume (ball y r)).toReal * q y :=
      mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
    _ ≤ ∫ z in ball y r, q z := hs
    _ ≤ ∫ z in ball x (2*r), q z :=
      setIntegral_mono_set hi ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ hpos z hz) (Eventually.of_forall hsub)

lemma nonzero_of_average_limit {α : Type u19} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {q : α → ℝ} {s : Set α} (hs : MeasurableSet s) {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto (fun m ↦ ⨍ x in s, f m x ∂μ) atTop (𝓝 (⨍ x in s, q x ∂μ)))
    (hmass : ∀ᶠ m in atTop, a ≤ ⨍ x in s, f m x ∂μ) :
    ∃ x ∈ s, q x ≠ 0 := by
  have h := ge_of_tendsto hlim hmass
  by_contra hn
  push Not at hn
  have hz : (⨍ x in s, q x ∂μ) = 0 := by
    rw [setAverage_eq]
    have hi : (∫ x in s, q x ∂μ) = 0 := integral_eq_zero_of_ae
      ((ae_restrict_mem hs).mono fun x hx ↦ hn x hx)
    rw [hi, smul_zero]
  rw [hz] at h
  exact (not_le_of_gt ha) h

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
theorem bounded_hilbert_countable_weak_subsequence
    {ι : Type u20} [Countable ι] {E : ι → Type u27}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, TopologicalSpace.SeparableSpace (E i)]
    {u : ℕ → ∀ i, E i} {R : ι → ℝ} (hu : ∀ k i, ‖u k i‖ ≤ R i) :
    ∃ (w : ∀ i, E i) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, ‖w i‖ ≤ R i) ∧
      ∀ i (v : E i), Tendsto (fun k ↦ inner ℂ (u (φ k) i) v) atTop
        (𝓝 (inner ℂ (w i) v)) := by
  let K (i : ι) : Set (WeakDual ℂ (E i)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (E i)) (R i)
  have hc (i : ι) : IsCompact (K i) := WeakDual.isCompact_closedBall (0 : StrongDual ℂ (E i)) (R i)
  let (i : ι) : CompactSpace (K i) := isCompact_iff_compactSpace.mp (hc i)
  let (i : ι) : TopologicalSpace.MetrizableSpace (K i) :=
    WeakDual.metrizable_of_isCompact ℂ (E i) (K i) (hc i)
  let d (k : ℕ) (i : ι) : K i :=
    ⟨StrongDual.toWeakDual ((InnerProductSpace.toDual ℂ (E i)) (u k i)), by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hu k i⟩
  obtain ⟨w', _, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := ∀ i, K i)).isSeqCompact.subseq_of_frequently_in
      (Filter.Frequently.of_forall (fun k ↦ mem_univ (d k)))
  let w (i : ι) : E i := (InnerProductSpace.toDual ℂ (E i)).symm
    (WeakDual.toStrongDual (w' i))
  refine ⟨w, φ, hφ, ?_, ?_⟩
  · intro i
    change ‖(InnerProductSpace.toDual ℂ (E i)).symm (WeakDual.toStrongDual (w' i))‖ ≤ R i
    simpa only [LinearIsometryEquiv.norm_map, K, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] using (w' i).property
  · intro i v
    have hi := ((continuous_apply i).continuousAt.tendsto.comp hlim)
    have hv := (WeakDual.eval_continuous (𝕜 := ℂ) v).continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp hi)
    simpa [d, w, Function.comp_def] using hv

theorem countable_supported_positive_weak_subsequence
    {ι : Type u21} {α : Type u22} {n : Type u23} [Countable ι] [MeasurableSpace α] [Fintype n] [DecidableEq n]
    {μ : Measure α} [IsSeparable μ]
    {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (hμs : ∀ i, μ (s i) ≠ ∞)
    {u : ℕ → ι → Lp (EuclideanSpace ℂ (n × n)) 2 μ} {R : ι → ℝ}
    (hR : ∀ i, 0 ≤ R i)
    (hu : ∀ k i, ∀ᵐ x ∂μ, (coefficientsToMatrix (u k i x)).PosSemidef ∧
      ‖u k i x‖ ≤ R i ∧ (x ∉ s i → u k i x = 0)) :
    ∃ (w : ι → Lp (EuclideanSpace ℂ (n × n)) 2 μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i, (∀ᵐ x ∂μ, (coefficientsToMatrix (w i x)).PosSemidef ∧
        ‖w i x‖ ≤ R i ∧ (x ∉ s i → w i x = 0)) ∧
        Integrable (fun x ↦ w i x) μ ∧ ∀ v,
          Tendsto (fun k ↦ inner ℂ (u (φ k) i) v) atTop (𝓝 (inner ℂ (w i) v)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let g (i : ι) : Lp ℝ 2 μ := indicatorConstLp 2 (hs i) (hμs i) (R i)
  have hn (k : ℕ) (i : ι) : ‖u k i‖ ≤ ‖g i‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu k i, (indicatorConstLp_coeFn (p := 2) (hs := hs i)
      (hμs := hμs i) (c := R i))] with x hx hg
    change ‖u k i x‖ ≤ ‖(indicatorConstLp 2 (hs i) (hμs i) (R i)) x‖
    rw [hg]
    by_cases hxs : x ∈ s i
    · simpa only [indicator_of_mem hxs, Real.norm_eq_abs, abs_of_nonneg (hR i)] using hx.2.1
    · simp only [indicator_of_notMem hxs, hx.2.2 hxs, norm_zero, le_refl]
  obtain ⟨w,φ,hφ,_,hlim⟩ := bounded_hilbert_countable_weak_subsequence hn
  refine ⟨w,φ,hφ,?_⟩
  intro i
  let C : α → Set (EuclideanSpace ℂ (n × n)) := fun x ↦
    {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R i ∧ (x ∉ s i → v = 0)}
  have hclosed (x : α) : IsClosed (C x) := by
    have he : C x = {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R i} ∩
        {v | x ∉ s i → v = 0} := by ext v; simp only [C, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [he]
    apply (isClosed_bounded_positive_coefficients (R i)).inter
    by_cases hx : x ∈ s i
    · simpa only [hx, not_true_eq_false, IsEmpty.forall_iff, ofPred_true] using
        (isClosed_univ : IsClosed (univ : Set (EuclideanSpace ℂ (n × n))))
    · simpa only [hx, not_false_eq_true, forall_true_left, ofPred_eq_eq_singleton] using
        (isClosed_singleton : IsClosed ({0} : Set (EuclideanSpace ℂ (n × n))))
  have hconvex (x : α) : Convex ℝ (C x) := by
    have he : C x = {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R i} ∩
        {v | x ∉ s i → v = 0} := by ext v; simp only [C, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [he]
    apply (convex_bounded_positive_coefficients (R i)).inter
    by_cases hx : x ∈ s i
    · simpa only [hx, not_true_eq_false, IsEmpty.forall_iff, ofPred_true] using
        (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℂ (n × n))))
    · simpa only [hx, not_false_eq_true, forall_true_left, ofPred_eq_eq_singleton] using
        (convex_singleton (0 : EuclideanSpace ℂ (n × n)) : Convex ℝ ({0} : Set (EuclideanSpace ℂ (n × n))))
  have hw := mem_closed_convex_of_weak_limit
    (isClosed_ae_variable_mem_Lp hclosed) (convex_ae_variable_mem_Lp hconvex)
    (fun k ↦ hu (φ k) i) (hlim i)
  change (∀ᵐ x ∂μ, (coefficientsToMatrix (w i x)).PosSemidef ∧
    ‖w i x‖ ≤ R i ∧ (x ∉ s i → w i x = 0)) at hw
  exact ⟨hw,L2_integrable_of_finite_support (hs i) (hμs i) (w i)
    (hw.mono fun _ h ↦ h.2.2), hlim i⟩

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

local instance instIsAddHaarMeasureProdComplexVolume_solutions_3_r6716fe_1 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
attribute [local instance] OAI.QuadricCounterexample.instContinuousENormMatrixComplexOfFintype_solutions_3
theorem countable_local_quadratic_compactness_with_weak
    {ι : Type u25} {n : Type u26} [Countable ι] [Fintype n] [DecidableEq n]
    {Hm : ℕ → ι → (ℂ × ℂ) → Matrix n n ℂ}
    {Ω U s : ι → Set (ℂ × ℂ)}
    (hΩ : ∀ i, IsOpen (Ω i)) (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, MeasurableSet (s i)) (hμs : ∀ i, volume (s i) ≠ ∞)
    (hmeas : ∀ m i, AEStronglyMeasurable (Hm m i))
    (hposm : ∀ m i, ∀ᵐ x ∂volume, (Hm m i x).PosSemidef)
    (hc : ∀ m i, ContinuousOn
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m i p.1) p.2) (Ω i ×ˢ univ))
    (hp : ∀ m i, DiskPshOn (Ω i ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m i p.1) p.2))
    {R C : ι → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hcoef : ∀ m i, ∀ᵐ x ∂volume, ‖matrixToCoefficients (Hm m i x)‖ ≤ R i ∧
      (x ∉ s i → Hm m i x = 0))
    {r : ι → ℕ → ℝ} (hr : ∀ i k, 0 < r i k)
    (hr0 : ∀ i, Tendsto (r i) atTop (𝓝 0))
    (hb : ∀ i k, ∀ x ∈ U i, closedBall x (r i k) ⊆ Ω i)
    (hbound : ∀ m i, ∀ x ∈ Ω i, ∀ v,
      quadraticValue (Hm m i x) v ≤ C i * ‖v‖ ^ 2) :
    ∃ (M : ι → (ℂ × ℂ) → Matrix n n ℂ)
      (f : ℕ → ι → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ)))
      (w : ι → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ)))
      (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ m i, (fun x ↦ coefficientsToMatrix (f m i x)) =ᵐ[volume] Hm m i) ∧
      (∀ m i, ∀ᵐ x ∂volume, ‖f m i x‖ ≤ R i ∧ (x ∉ s i → f m i x = 0)) ∧
      ∀ i, (M i =ᵐ[volume.restrict (U i)] fun x ↦ coefficientsToMatrix (w i x)) ∧
        (∀ v, Tendsto (fun m ↦ inner ℂ (f (φ m) i) v) atTop (𝓝 (inner ℂ (w i) v))) ∧
        (∀ x ∈ U i, (M i x).PosSemidef) ∧
        DiskPshOn (U i ×ˢ univ)
          (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (M i p.1) p.2) ∧
        ∀ x ρ v, ball x ρ ⊆ U i →
          Tendsto (fun m ↦ ⨍ y in ball x ρ, quadraticValue (Hm (φ m) i y) v) atTop
            (𝓝 (⨍ y in ball x ρ, quadraticValue (M i y) v)) := by
  have hLp (m : ℕ) (i : ι) := matrix_coefficients_memLp
    (hs i) (hμs i) (hmeas m i) (hR i) (hcoef m i)
  let f (m : ℕ) (i : ι) := (hLp m i).toLp (fun x ↦ matrixToCoefficients (Hm m i x))
  have hf (m : ℕ) (i : ι) :
      (fun x ↦ coefficientsToMatrix (f m i x)) =ᵐ[volume] Hm m i := by
    filter_upwards [(hLp m i).coeFn_toLp] with x hx
    exact congrArg coefficientsToMatrix hx
  have hfb (m : ℕ) (i : ι) : ∀ᵐ x ∂volume,
      (coefficientsToMatrix (f m i x)).PosSemidef ∧ ‖f m i x‖ ≤ R i ∧
      (x ∉ s i → f m i x = 0) := by
    filter_upwards [(hLp m i).coeFn_toLp, hposm m i, hcoef m i] with x hx hp hb
    rw [hx]
    exact ⟨hp, hb.1, fun hxs ↦ by rw [hb.2 hxs, map_zero]⟩
  obtain ⟨w,φ,hφ,hw⟩ := countable_supported_positive_weak_subsequence hs hμs hR hfb
  have hHm (m : ℕ) (i : ι) : Integrable (Hm m i) := by
    have hf1 := L2_integrable_of_finite_support (hs i) (hμs i) (f m i)
      ((hfb m i).mono fun _ h ↦ h.2.2)
    exact (coefficientsToMatrix.toContinuousLinearMap.integrable_comp hf1).congr (hf m i)
  have hex (i : ι) := weak_quadratic_psh_representative (hΩ i) (hU i)
    (fun m ↦ hf (φ m) i) (hw i).2.2 (hw i).2.1 (fun m ↦ hHm (φ m) i)
    (fun m ↦ hposm (φ m) i) (fun m ↦ hc (φ m) i) (fun m ↦ hp (φ m) i)
    (hr i) (hr0 i) (hb i) (fun m ↦ hbound (φ m) i)
  choose M hM hae hpsh using hex
  refine ⟨M,f,w,φ,hφ,hf,fun m i ↦ (hfb m i).mono (fun _ h ↦ h.2),
    fun i ↦ ⟨hae i,(hw i).2.2,hM i,hpsh i,?_⟩⟩
  intro x ρ v hball
  have hh := weak_quadratic_averages (fun m ↦ hf (φ m) i) (hw i).2.2 x ρ v
  convert hh using 1
  congr 1
  apply average_congr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (hae i)] with y hy
  exact congrArg (fun H ↦ quadraticValue H v) hy

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TraceMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace TwistedPshForm
variable {D : EqualizerData} {m : ℕ}

lemma quadratic_bound_of_unit_ball {H : TwoMatrix} {C : ℝ}
    (h : ∀ v : FiberCoordinates, ‖v‖≤1 → quadraticValue H v≤C) (v : FiberCoordinates) :
    quadraticValue H v ≤ C*‖v‖^2 := by
  by_cases hv : v=0
  · subst v; simp [quadraticValue]
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hn' : (‖v‖ : ℂ)≠0 := by exact_mod_cast hn
  let w := (‖v‖ : ℂ)⁻¹ •v
  have hw : ‖w‖≤1 := by
    dsimp [w]
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hn]
  have he : (‖v‖:ℂ) • w=v := by
    dsimp [w]
    ext k
    change (‖v‖:ℂ) * ((‖v‖:ℂ)⁻¹ * v k)=v k
    rw [← mul_assoc,mul_inv_cancel₀ hn',one_mul]
  calc
    quadraticValue H v = quadraticValue H ((‖v‖:ℂ) • w) := congrArg _ he.symm
    _ = ‖v‖^2*quadraticValue H w := by
      rw [quadraticValue_scalar,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖v‖^2*C := mul_le_mul_of_nonneg_left (h w hw) (sq_nonneg _)
    _ = C*‖v‖^2 := mul_comm _ _

lemma exists_normalized (P : TwistedPshForm D m) :
    ∃ Q : TwistedPshForm D m,
      (∀ i z, ‖z‖≤1 → ∀ v, Q.value i (z,v)≤‖v‖^2) ∧
      ∃ i z v, ‖z‖≤1 ∧ ‖v‖≤1 ∧ Q.value i (z,v)=1 := by
  let K : Set (StandardChart × (BaseCoordinates × FiberCoordinates)) :=
    univ ×ˢ (closedBall 0 1 ×ˢ closedBall 0 1)
  have hK : IsCompact K := isCompact_univ.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hKn : K.Nonempty := ⟨((0,0),(0,0)),by simp [K]⟩
  have hf : Continuous (fun p : StandardChart × (BaseCoordinates × FiberCoordinates) ↦ P.value p.1 p.2) :=
    continuous_prod_of_discrete_left.mpr P.value_continuous
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn hKn hf.continuousOn
  let C := P.value p.1 p.2
  let e : FiberCoordinates := Pi.single 0 1
  have he : e≠0 := by intro he; have ht := congrFun he 0; simp [e] at ht
  have hen : ‖e‖≤1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    (fun k ↦ by by_cases hk : k=0 <;> simp [e,hk])
  have h0 : 0<P.value (0,0) (0,e) :=
    (Complex.lt_def.mp ((P.positive (0,0) 0).dotProduct_mulVec_pos he)).1
  have hC : 0<C := h0.trans_le (hmax (show ((0,0),(0,e))∈K by
    exact ⟨mem_univ _,by simp,by simpa only [mem_closedBall,dist_zero_right] using hen⟩))
  have hC' : C≠0 := ne_of_gt hC
  refine ⟨P.rescale C⁻¹ (inv_pos.mpr hC),?_,p.1,p.2.1,p.2.2,?_,?_,?_⟩
  · intro i z hz v
    change quadraticValue ((P.rescale C⁻¹ (inv_pos.mpr hC)).matrix i z) v≤‖v‖^2
    suffices hh : ∀ w : FiberCoordinates, ‖w‖≤1 →
        quadraticValue ((P.rescale C⁻¹ (inv_pos.mpr hC)).matrix i z) w≤1 by
      simpa only [one_mul] using quadratic_bound_of_unit_ball hh v
    intro w hw
    change (P.rescale C⁻¹ (inv_pos.mpr hC)).value i (z,w)≤1
    rw [value_rescale]
    have ht : P.value i (z,w)≤C := hmax (show (i,(z,w))∈K by
      exact ⟨mem_univ _,by simpa using hz,by simpa using hw⟩)
    exact (inv_mul_le_iff₀ hC).mpr (by simpa using ht)
  · simpa only [K,mem_prod,mem_univ,mem_closedBall,dist_zero_right,true_and] using hp.2.1
  · simpa only [K,mem_prod,mem_univ,mem_closedBall,dist_zero_right,true_and] using hp.2.2
  · rw [value_rescale]; exact inv_mul_cancel₀ hC'
end TwistedPshForm

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise
noncomputable section

lemma norm_matrix_of_quadratic_bound {H : TwoMatrix} (hH : H.PosSemidef) {C : ℝ}
    (hC : 0≤C) (hb : ∀ v : FiberCoordinates, quadraticValue H v≤C*‖v‖^2) : ‖H‖≤4*C := by
  have hnon (v : FiberCoordinates) : 0≤quadraticValue H v := quadraticValue_nonneg hH v
  have he (i : Fin 2) : ‖(Pi.single i 1 : FiberCoordinates)‖=1 := by rw [Pi.norm_single,norm_one]
  have hsingle (i : Fin 2) : quadraticValue H (Pi.single i 1)≤C := by simpa only [he,one_pow,mul_one] using hb (Pi.single i 1)
  have hsmall (v : FiberCoordinates) (hv : ‖v‖≤2) : quadraticValue H v≤4*C := by
    have hn := sq_le_sq₀ (norm_nonneg v) (by norm_num : (0:ℝ)≤2) |>.mpr hv
    have hh := mul_le_mul_of_nonneg_left hn hC
    exact (hb v).trans (by nlinarith)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hsum := hsmall (Pi.single i 1+Pi.single j 1) (by
    calc ‖(Pi.single i 1 : FiberCoordinates)+Pi.single j 1‖ ≤ ‖(Pi.single i 1 : FiberCoordinates)‖+‖(Pi.single j 1 : FiberCoordinates)‖ := norm_add_le _ _
         _ = 2 := by rw [he,he]; norm_num)
  have hisum := hsmall (Pi.single i 1+Complex.I •Pi.single j 1) (by
    calc ‖(Pi.single i 1 : FiberCoordinates)+Complex.I •Pi.single j 1‖ ≤ ‖(Pi.single i 1 : FiberCoordinates)‖+‖Complex.I •(Pi.single j 1 : FiberCoordinates)‖ := norm_add_le _ _
         _ = 2 := by rw [norm_smul,Complex.norm_I,he,he]; norm_num)
  have hid := congrFun (congrFun (matrixFromQuadratic_value hH.isHermitian) i) j
  have hre : |(H i j).re|≤2*C := by
    rw [← hid]
    change |(quadraticValue H (Pi.single i 1+Pi.single j 1)-quadraticValue H (Pi.single i 1)-quadraticValue H (Pi.single j 1))/2|≤2*C
    apply abs_le.mpr
    constructor <;> nlinarith [hnon (Pi.single i 1+Pi.single j 1),hnon (Pi.single i 1),hnon (Pi.single j 1),hsingle i,hsingle j]
  have him : |(H i j).im|≤2*C := by
    rw [← hid]
    change |(quadraticValue H (Pi.single i 1)+quadraticValue H (Pi.single j 1)-quadraticValue H (Pi.single i 1+Complex.I •Pi.single j 1))/2|≤2*C
    apply abs_le.mpr
    constructor <;> nlinarith [hnon (Pi.single i 1+Complex.I •Pi.single j 1),hnon (Pi.single i 1),hnon (Pi.single j 1),hsingle i,hsingle j]
  exact (Complex.norm_le_abs_re_add_abs_im (H i j)).trans (by linarith)

lemma norm_coefficients_of_quadratic_bound {H : TwoMatrix} (hH : H.PosSemidef) {C : ℝ}
    (hC : 0≤C) (hb : ∀ v : FiberCoordinates, quadraticValue H v≤C*‖v‖^2) :
    ‖matrixToCoefficients H‖≤8*C := by
  have hM := norm_matrix_of_quadratic_bound hH hC hb
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤8*C)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    ∑ ij : Fin 2 × Fin 2, ‖matrixToCoefficients H ij‖^2 ≤ ∑ _ij : Fin 2 × Fin 2, (4*C)^2 := by
      apply Finset.sum_le_sum
      intro ij _
      change ‖H ij.1 ij.2‖^2≤(4*C)^2
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact (norm_le_pi_norm (H ij.1) ij.2).trans ((norm_le_pi_norm H ij.1).trans hM)
    _ = (8*C)^2 := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]; norm_num; ring

end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.TraceExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section
local instance instPseudoMetrizableSpaceTwoMatrix : TopologicalSpace.PseudoMetrizableSpace TwoMatrix :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

lemma traceBound_spec (D : EqualizerData) (a : TraceIndex) (m : ℕ) (hm : 0 < m)
    (P : TwistedPshForm D m) (hP : ∀ i z, ‖z‖≤1 → ∀ v, P.value i (z,v)≤‖v‖^2)
    (z : BaseCoordinates) (hz : z∈traceSupport a) (v : FiberCoordinates) :
    P.value a.1 (z,v)≤traceBound D a*‖v‖^2 :=
  (TwistedPshForm.local_bound D a.1 ((a.2:ℝ)+4)).choose_spec.2 m hm P hP z
    (by simpa only [traceSupport,mem_closedBall,dist_zero_right] using hz) v

lemma exists_extractedTrace {D : EqualizerData} {ex : ℕ → ℕ} (hex : ∀ k, 0 < ex k)
    (P : ∀ k, TwistedPshForm D (ex k))
    (hP : ∀ k i z, ‖z‖≤1 → ∀ v, (P k).value i (z,v)≤‖v‖^2) :
    Nonempty (ExtractedTrace ex P) := by
  let H (k : ℕ) (a : TraceIndex) := cutoffTrace (P k) a
  have heq (k : ℕ) (a : TraceIndex) : EqOn
      (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (H k a p.1) p.2)
      ((P k).value a.1) (traceDomain a ×ˢ univ) := by
    intro p hp
    change quadraticValue (H k a p.1) p.2 = quadraticValue ((P k).matrix a.1 p.1) p.2
    rw [show H k a p.1=(P k).matrix a.1 p.1 from cutoffTrace_eq _ _ (traceDomain_subset_support a hp.1)]
  have hmeas (k : ℕ) (a : TraceIndex) : AEStronglyMeasurable (H k a) :=
    ((P k).continuous a.1).aestronglyMeasurable.indicator measurableSet_closedBall
  have hpos (k : ℕ) (a : TraceIndex) : ∀ᵐ x ∂volume, (H k a x).PosSemidef := by
    apply Eventually.of_forall; intro x
    by_cases hx : x∈traceSupport a
    · rw [show H k a x=(P k).matrix a.1 x from cutoffTrace_eq _ _ hx]
      exact ((P k).positive a.1 x).posSemidef
    · simp only [H,cutoffTrace,indicator_of_notMem hx]
      exact Matrix.PosSemidef.zero
  have hcont (k : ℕ) (a : TraceIndex) : ContinuousOn
      (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (H k a p.1) p.2)
      (traceDomain a ×ˢ univ) := ((P k).value_continuous a.1).continuousOn.congr (heq k a)
  have hpsh (k : ℕ) (a : TraceIndex) : DiskPshOn (traceDomain a ×ˢ univ)
      (fun p : BaseCoordinates × FiberCoordinates ↦ quadraticValue (H k a p.1) p.2) :=
    (((P k).psh a.1).mono (subset_univ _)).congr (heq k a).symm
  have hb (k : ℕ) (a : TraceIndex) : ∀ᵐ x ∂volume,
      ‖matrixToCoefficients (H k a x)‖≤8*traceBound D a ∧ (x∉traceSupport a → H k a x=0) := by
    apply Eventually.of_forall; intro x
    by_cases hx : x∈traceSupport a
    · rw [show H k a x=(P k).matrix a.1 x from cutoffTrace_eq _ _ hx]
      exact ⟨norm_coefficients_of_quadratic_bound ((P k).positive a.1 x).posSemidef
        (traceBound_nonneg D a) (traceBound_spec D a (ex k) (hex k) (P k) (hP k) x hx),
        fun hn ↦ (hn hx).elim⟩
    · simp only [H,cutoffTrace,indicator_of_notMem hx,map_zero,norm_zero]
      exact ⟨mul_nonneg (by norm_num) (traceBound_nonneg D a),fun _ ↦ trivial⟩
  let r (_ : TraceIndex) (k : ℕ) : ℝ := 1/(k+1)
  have hr (a : TraceIndex) (k : ℕ) : 0 < r a k := by dsimp [r]; positivity
  have hr0 (a : TraceIndex) : Tendsto (r a) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hballs (a : TraceIndex) (k : ℕ) : ∀ x∈traceInterior a, closedBall x (r a k) ⊆ traceDomain a := by
    intro x hx
    apply closedBall_subset_ball'
    have hxr : dist x 0 < (a.2:ℝ)+2 := hx
    have hrle : r a k≤1 := by
      dsimp [r]
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_left (Nat.cast_nonneg k)
    linarith
  have hbound (k : ℕ) (a : TraceIndex) : ∀ x∈traceDomain a, ∀ v,
      quadraticValue (H k a x) v≤traceBound D a*‖v‖^2 := by
    intro x hx v
    rw [show H k a x=(P k).matrix a.1 x from cutoffTrace_eq _ _ (traceDomain_subset_support a hx)]
    exact traceBound_spec D a (ex k) (hex k) (P k) (hP k) x (traceDomain_subset_support a hx) v
  obtain ⟨M,f,w,φ,hφ,hf,hfb,hlim⟩ := countable_local_quadratic_compactness_with_weak
    (fun _ ↦ isOpen_ball) (fun _ ↦ isOpen_ball) (fun _ ↦ measurableSet_closedBall)
    (fun _ ↦ measure_closedBall_lt_top.ne) hmeas hpos hcont hpsh
    (fun a ↦ mul_nonneg (by norm_num) (traceBound_nonneg D a)) hb hr hr0 hballs hbound
  exact ⟨{
    matrix := M, f := f, w := w, subsequence := φ, strictMono := hφ
    coefficients := hf, bound := hfb, representative := fun a ↦ (hlim a).1
    weak := fun a ↦ (hlim a).2.1, positive := fun a ↦ (hlim a).2.2.1
    psh := fun a ↦ (hlim a).2.2.2.1, averages := fun a ↦ (hlim a).2.2.2.2 }⟩
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.MatrixDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section

namespace QuadricCounterexample
open Matrix

lemma source_A_trace : source_A.trace = 1 := by
  simp [source_A, trace_fin_two, source_a_add_inv]

lemma source_B_trace : source_B.trace = 1 := by
  simp [source_B, trace_fin_two]

lemma matrix_sq_of_det_trace_one
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hd : M.det = 1) (ht : M.trace = 1) :
    M ^ 2 = M - 1 := by
  have h := M.aeval_self_charpoly
  rw [Matrix.charpoly_fin_two, ht, hd] at h
  simp only [map_add, map_sub, map_pow, Polynomial.aeval_X,
    map_one, one_mul] at h
  apply eq_sub_iff_add_eq.mpr
  apply sub_eq_zero.mp
  simpa only [sub_add_eq_add_sub] using h

lemma matrix_cube_of_det_trace_one
    {M : Matrix (Fin 2) (Fin 2) ℂ} (hd : M.det = 1) (ht : M.trace = 1) :
    M ^ 3 = -1 := by
  have hs := matrix_sq_of_det_trace_one hd ht
  calc
    M ^ 3 = M * M ^ 2 := by noncomm_ring
    _ = M * (M - 1) := by rw [hs]
    _ = M ^ 2 - M := by noncomm_ring
    _ = -1 := by rw [hs]; abel

lemma source_A_cube : source_A ^ 3 = -1 :=
  matrix_cube_of_det_trace_one source_A_det source_A_trace
lemma source_B_cube : source_B ^ 3 = -1 :=
  matrix_cube_of_det_trace_one source_B_det source_B_trace

lemma source_A_inv : source_A⁻¹ = !![source_a⁻¹, 0; 0, source_a] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [source_A, Matrix.mul_apply, source_a_ne_zero]

lemma source_relative_trace : (source_A⁻¹ * source_B).trace = -(Real.sqrt 2 : ℂ) := by
  have htrace : (source_A⁻¹ * source_B).trace =
      source_a⁻¹ * source_s + source_a * (1 - source_s) := by
    simp [source_A_inv, source_B, trace_fin_two]
  rw [htrace]
  rw [source_a_inv_eq, source_a_eq]
  unfold source_s
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma source_product_trace : (source_A * source_B).trace = 1 + (Real.sqrt 2 : ℂ) := by
  have hinv : source_A + source_A⁻¹ = 1 := by
    rw [source_A_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [source_A, source_a_add_inv, add_comm]
  have htrace := congrArg Matrix.trace (congrArg (fun M ↦ M * source_B) hinv)
  rw [add_mul, trace_add, one_mul, source_relative_trace, source_B_trace] at htrace
  linear_combination htrace

end QuadricCounterexample

namespace QuadricCounterexample
open Matrix

lemma hyperbolicBasis_diagonalizes {M : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ}
    (ht : 2 < t) (htr : M.trace = (t : ℂ)) (hdet : M.det = 1) :
    M * hyperbolicBasis M t = hyperbolicBasis M t *
      Matrix.diagonal ![(expandingRoot t : ℂ), (contractingRoot t : ℂ)] := by
  obtain ⟨_, _, _, hs, hp⟩ := hyperbolic_roots ht
  have hsC : (expandingRoot t : ℂ) + (contractingRoot t : ℂ) = (t : ℂ) := by
    exact_mod_cast hs
  have hpC : (expandingRoot t : ℂ) * (contractingRoot t : ℂ) = 1 := by
    exact_mod_cast hp
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicBasis, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (expandingRoot t : ℂ) * (htr - hsC) -
      hdet + hpC
  · linear_combination (contractingRoot t : ℂ) * (htr - hsC) -
      hdet + hpC
  · ring
  · ring

end QuadricCounterexample

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory

lemma fixed_of_period_three_in_pair {X : Type u3} {f : X → X} {p q x : X}
    (hcube : f (f (f x)) = x) (hx : x = p ∨ x = q)
    (h1 : f x = p ∨ f x = q) (h2 : f (f x) = p ∨ f (f x) = q) : f x = x := by
  have hcollision : x = f x ∨ x = f (f x) ∨ f x = f (f x) := by
    rcases hx with hx | hx <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      simp_all
  rcases hcollision with h | h | h
  · exact h.symm
  · simpa only [hcube] using congrArg f h
  · calc
      f x = f (f x) := h
      _ = f (f (f x)) := congrArg f h
      _ = x := hcube

end QuadricCounterexample

namespace QuadricCounterexample
open Matrix OnePoint Filter Topology MeasureTheory

lemma projective_cube_identity {g : GL (Fin 2) ℂ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) ^ 3 = -1) :
    ∀ x : OnePoint ℂ, g • (g • (g • x)) = x := by
  intro x
  have hv : ((g ^ 3 : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
    simpa using hg
  calc
    g • (g • (g • x)) = (g^3) • x := by simp [pow_succ, mul_smul]
    _ = x := by
      cases x using OnePoint.rec with
      | infty => simp [OnePoint.smul_infty_eq_ite, hv]
      | coe z => simp [OnePoint.smul_some_eq_ite, hv]

lemma source_no_common_fixed_point (x : OnePoint ℂ) :
    ¬ (source_A_gl • x = x ∧ source_B_gl • x = x) := by
  rintro ⟨hA, hB⟩
  cases x using OnePoint.rec with
  | infty =>
    have hc := OnePoint.smul_infty_eq_self_iff.mp hB
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
    simp [source_B_gl, source_B, hn] at hc
  | coe z =>
    have hpoly := Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hA
    have hdiff : source_a - source_a⁻¹ ≠ 0 := by
      rw [source_a_inv_eq, source_a_eq]
      intro h
      have hi := congrArg Complex.im h
      simp at hi
    have haz : (source_a⁻¹ - source_a) * z = 0 := by
      simpa [Matrix.GeneralLinearGroup.fixpointPolynomial, source_A_gl, source_A] using hpoly
    have hz : z = 0 := (mul_eq_zero.mp haz).resolve_left (sub_ne_zero.mpr
      (Ne.symm (sub_ne_zero.mp hdiff)))
    subst z
    have hb := Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mpr hB
    simp [Matrix.GeneralLinearGroup.fixpointPolynomial, source_B_gl, source_B] at hb

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.HomogeneousClassification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric

lemma invariant_mul_zpow {u : ℂ → ℝ} {a : ℂ} (ha : a ≠ 0)
    (hu : ∀ z : ℂ, z ≠ 0 → u (a * z) = u z) (n : ℤ) (z : ℂ) (hz : z ≠ 0) :
    u (a ^ n * z) = u z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add₀ ha, zpow_one, mul_comm (a ^ (k : ℤ)) a, mul_assoc,
      hu _ (mul_ne_zero (zpow_ne_zero _ ha) hz), ih]
  | pred k ih =>
    have hh := hu (a ^ (-(k : ℤ) - 1) * z) (mul_ne_zero (zpow_ne_zero _ ha) hz)
    have he : a * (a ^ (-(k : ℤ) - 1) * z) = a ^ (-(k : ℤ)) * z := by
      calc
        a * (a ^ (-(k : ℤ) - 1) * z) =
            (a ^ (1 : ℤ) * a ^ (-(k : ℤ) - 1)) * z := by rw [zpow_one, mul_assoc]
        _ = a ^ (1 + (-(k : ℤ) - 1)) * z := by rw [zpow_add₀ ha]
        _ = a ^ (-(k : ℤ)) * z := by congr 2; omega
    rw [he, ih] at hh
    exact hh.symm

lemma exists_rescale_mem_annulus {a : ℝ} (ha : 1 < a) {z : ℂ} (hz : z ≠ 0) :
    ∃ n : ℤ, 1 ≤ ‖(a : ℂ) ^ n * z‖ ∧ ‖(a : ℂ) ^ n * z‖ ≤ a := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (norm_pos_iff.mpr hz) ha
  refine ⟨-k, ?_, ?_⟩
  all_goals rw [norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha0, zpow_neg, inv_mul_eq_div]
  · exact (le_div_iff₀ (zpow_pos ha0 k)).mpr (by simpa using hk1)
  · apply (div_le_iff₀ (zpow_pos ha0 k)).mpr
    exact hk2.le.trans_eq (by rw [zpow_add₀ ha0.ne', zpow_one, mul_comm])

lemma complex_punctured_preconnected : IsPreconnected ({0}ᶜ : Set ℂ) := by
  apply (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) ?_ 0).isPreconnected
  rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
  norm_num

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric

open MeasureTheory

theorem LocalDiskSubmeanOn.eq_const_of_dilation {u : ℂ → ℝ} {a : ℝ}
    (ha : 1 < a) (hu : LocalDiskSubmeanOn ({0}ᶜ : Set ℂ) u)
    (hinv : ∀ z : ℂ, z ≠ 0 → u ((a : ℂ) * z) = u z) :
    ∃ c : ℝ, ∀ z : ℂ, z ≠ 0 → u z = c := by
  let K : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ a}
  have hkclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hkcompact : IsCompact K := (isCompact_closedBall (0 : ℂ) a).of_isClosed_subset
    hkclosed (fun z hz ↦ by simpa [mem_closedBall, dist_zero_right] using hz.2)
  have hk0 : K ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    simp only [K, he, norm_zero, Set.mem_ofPred_eq] at hz
    linarith [hz.1]
  have hkne : K.Nonempty := ⟨1, by simpa [K] using ha.le⟩
  obtain ⟨x, hx, hmax⟩ := (hu.1.mono hk0).exists_isMaxOn hkne hkcompact
  have hnonzero : (a : ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_one ha).ne'
  have hmaxall : ∀ z ∈ ({0}ᶜ : Set ℂ), u z ≤ u x := by
    intro z hz
    have hz0 : z ≠ 0 := hz
    obtain ⟨k, hk⟩ := exists_rescale_mem_annulus ha hz0
    have hk' : (a : ℂ)^k * z ∈ K := hk
    rw [← invariant_mul_zpow hnonzero hinv k z hz0]
    exact hmax hk'
  exact ⟨u x, fun z hz ↦ hu.eq_const_of_max complex_punctured_preconnected (hk0 hx) hmaxall z hz⟩

end QuadricCounterexample

namespace QuadricCounterexample
open Set Matrix

lemma HomogeneousLocalPshMetric24.normalized_subharmonic {ψ : (Fin 2 → ℂ) → ℝ}
    (hψ : HomogeneousLocalPshMetric24 ψ) :
    LocalDiskSubmeanOn ({0}ᶜ : Set ℂ) (fun z ↦ ψ ![z,1] / ‖z‖ ^ 24) := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ ↦ ![z,1]) ({0}ᶜ : Set ℂ) := by
    apply analyticOnNhd_pi_iff.mpr
    intro i
    fin_cases i
    · exact analyticOnNhd_id
    · exact analyticOnNhd_const
  have ht : AnalyticOnNhd ℂ (fun z : ℂ ↦ z ^ (-12 : ℤ)) ({0}ᶜ : Set ℂ) :=
    analyticOnNhd_id.zpow (fun z hz ↦ hz)
  have hn : ∀ z ∈ ({0}ᶜ : Set ℂ), (![z,1] : Fin 2 → ℂ) ≠ 0 := by
    intro z _ he
    have hh := congrFun he 1
    norm_num at hh
  have hh := hψ.disk _ isOpen_compl_singleton _ _ hf ht hn
  convert hh using 1
  funext z
  simp only [_root_.zpow_neg]
  norm_num
  ring

theorem HomogeneousLocalPshMetric24.hyperbolic_classification
    {ψ : (Fin 2 → ℂ) → ℝ} (hψ : HomogeneousLocalPshMetric24 ψ)
    {a : ℝ} (ha : 1 < a)
    (hinv : ∀ v, ψ ![(a : ℂ) * v 0, (a : ℂ)⁻¹ * v 1] = ψ v) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v, ψ v = c * (‖v 0‖ * ‖v 1‖) ^ 24 := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  have hpa : 1 < a ^ 48 := one_lt_pow₀ ha (by norm_num)
  have he1 : ψ ![1,0] = 0 := by
    have hs : ψ ![(a : ℂ),0] = a ^ 48 * ψ ![1,0] := by
      have hv : (a : ℂ) • (![1,0] : Fin 2 → ℂ) = ![(a : ℂ),0] := by
        ext i
        fin_cases i <;> simp
      rw [← hv, hψ.homogeneity, hanorm]
    have hi := hinv ![1,0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      mul_zero] at hi
    rw [hs] at hi
    nlinarith
  have he2 : ψ ![0,1] = 0 := by
    have hs : ψ ![0,(a : ℂ)] = a ^ 48 * ψ ![0,1] := by
      have hv : (a : ℂ) • (![0,1] : Fin 2 → ℂ) = ![0,(a : ℂ)] := by
        ext i
        fin_cases i <;> simp
      rw [← hv, hψ.homogeneity, hanorm]
    have hi := hinv ![0,(a : ℂ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      inv_mul_cancel₀ haC] at hi
    rw [hs] at hi
    nlinarith
  have hscale (z : ℂ) : ψ ![(a : ℂ)^2*z,1] = a^48 * ψ ![z,1] := by
    have hv : (a : ℂ) • ![(a : ℂ)*z,(a : ℂ)⁻¹*1] = ![(a : ℂ)^2*z,1] := by
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, pow_two, mul_assoc, haC]
    rw [← hv, hψ.homogeneity, hanorm]
    exact congrArg (fun r : ℝ ↦ a ^ 48 * r) (hinv ![z,1])
  have hu : ∀ z : ℂ, z ≠ 0 →
      ψ ![((a^2 : ℝ) : ℂ)*z,1] / ‖((a^2 : ℝ) : ℂ)*z‖^24 =
        ψ ![z,1] / ‖z‖^24 := by
    intro z hz
    rw [Complex.ofReal_pow, hscale, norm_mul, norm_pow, hanorm, mul_pow, ← pow_mul]
    norm_num
    field_simp
  obtain ⟨c, hc⟩ := hψ.normalized_subharmonic.eq_const_of_dilation
    (show 1 < a^2 by nlinarith) hu
  have hc0 : 0 ≤ c := by
    rw [← hc 1 one_ne_zero]
    exact div_nonneg (hψ.nonneg _) (pow_nonneg (norm_nonneg _) _)
  refine ⟨c, hc0, ?_⟩
  intro v
  by_cases hv1 : v 1 = 0
  · have he : v = v 0 • ![1,0] := by
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv1]
    rw [he, hψ.homogeneity, he1]
    simp
  by_cases hv0 : v 0 = 0
  · have he : v = v 1 • ![0,1] := by
      ext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv0]
    rw [he, hψ.homogeneity, he2]
    simp
  have he : v = v 1 • ![v 0 / v 1,1] := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv1, mul_div_cancel₀]
  have hh := (div_eq_iff (pow_ne_zero 24 (norm_ne_zero_iff.mpr (div_ne_zero hv0 hv1)))).mp
    (hc (v 0 / v 1) (div_ne_zero hv0 hv1))
  calc
    ψ v = ‖v 1‖^48 * ψ ![v 0/v 1,1] := by calc
      ψ v = ψ (v 1 • ![v 0/v 1,1]) := congrArg ψ he
      _ = _ := hψ.homogeneity _ _
    _ = c * (‖v 0‖ * ‖v 1‖)^24 := by
      rw [hh, norm_div, div_pow, mul_pow]
      field_simp

lemma HomogeneousLocalPshMetric24.pullback {ψ : (Fin 2 → ℂ) → ℝ}
    (hψ : HomogeneousLocalPshMetric24 ψ) (g : GL (Fin 2) ℂ) :
    HomogeneousLocalPshMetric24 (fun v ↦ ψ (g • v)) := by
  let L : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
    (Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap
  have hL (v : Fin 2 → ℂ) : L v = g • v := rfl
  have hn (v : Fin 2 → ℂ) (hv : v ≠ 0) : g • v ≠ 0 := by
    intro he
    have hh := congrArg (fun w : Fin 2 → ℂ ↦ g⁻¹ • w) he
    rw [inv_smul_smul, smul_zero] at hh
    exact hv hh
  refine ⟨fun v ↦ hψ.nonneg _, ?_, ?_, ?_⟩
  · intro c v
    rw [smul_comm g c v, hψ.homogeneity]
  · exact hψ.upperSemicontinuous.comp L.continuous.continuousOn (fun v hv ↦ hn v hv)
  · intro U hU f t hf ht hfn
    exact hψ.disk U hU (fun z ↦ g • f z) t
      (((L.analyticOnNhd univ).comp hf (mapsTo_univ _ _))) ht
      (fun z hz ↦ hn _ (hfn z hz))

end QuadricCounterexample

namespace QuadricCounterexample
open Matrix OnePoint

lemma metric_zero_pair_preserved {φ : (Fin 2 → ℂ) → ℝ}
    (hz : ∀ v, φ v = 0 ↔ v 0 = 0 ∨ v 1 = 0)
    (g : GL (Fin 2) ℂ) (hinv : ∀ v, φ (g • v) = φ v) :
    ∀ x : OnePoint ℂ, x = ∞ ∨ x = (0 : ℂ) →
      g • x = ∞ ∨ g • x = (0 : ℂ) := by
  intro x hx
  rcases hx with rfl | rfl
  · have hzero : φ (g • (![1,0] : Fin 2 → ℂ)) = 0 := by
      rw [hinv]
      exact (hz _).mpr (Or.inr rfl)
    have hh := (hz _).mp hzero
    simp only [Matrix.GeneralLinearGroup.fin_two_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, add_zero] at hh
    by_cases h10 : g 1 0 = 0
    · exact Or.inl (by simp [OnePoint.smul_infty_eq_ite, h10])
    · have h00 := hh.resolve_right h10
      exact Or.inr (by simp [OnePoint.smul_infty_eq_ite, h10, h00])
  · have hzero : φ (g • (![0,1] : Fin 2 → ℂ)) = 0 := by
      rw [hinv]
      exact (hz _).mpr (Or.inl rfl)
    have hh := (hz _).mp hzero
    simp only [Matrix.GeneralLinearGroup.fin_two_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, zero_add] at hh
    by_cases h11 : g 1 1 = 0
    · exact Or.inl (by simp [OnePoint.smul_some_eq_ite, h11])
    · have h01 := hh.resolve_right h11
      exact Or.inr (by simp [OnePoint.smul_some_eq_ite, h11, h01])

lemma conjugate_pair_contradiction {φ : (Fin 2 → ℂ) → ℝ}
    (hz : ∀ v, φ v = 0 ↔ v 0 = 0 ∨ v 1 = 0)
    (P g h : GL (Fin 2) ℂ)
    (hgi : ∀ v, φ ((P⁻¹ * g * P) • v) = φ v)
    (hhi : ∀ v, φ ((P⁻¹ * h * P) • v) = φ v)
    (hg3 : ∀ x : OnePoint ℂ, g • (g • (g • x)) = x)
    (hh3 : ∀ x : OnePoint ℂ, h • (h • (h • x)) = x)
    (hnofix : ∀ x : OnePoint ℂ, ¬ (g • x = x ∧ h • x = x)) : False := by
  let g' := P⁻¹ * g * P
  let h' := P⁻¹ * h * P
  have hgp := metric_zero_pair_preserved hz g' hgi
  have hhp := metric_zero_pair_preserved hz h' hhi
  have hgcube (x : OnePoint ℂ) : g' • (g' • (g' • x)) = x := by
    simp only [g', mul_smul, smul_inv_smul]
    rw [hg3, inv_smul_smul]
  have hhcube (x : OnePoint ℂ) : h' • (h' • (h' • x)) = x := by
    simp only [h', mul_smul, smul_inv_smul]
    rw [hh3, inv_smul_smul]
  have hgp0 := hgp ∞ (Or.inl rfl)
  have hhp0 := hhp ∞ (Or.inl rfl)
  have hgf : g' • (∞ : OnePoint ℂ) = ∞ :=
    fixed_of_period_three_in_pair (hgcube ∞) (Or.inl rfl) hgp0 (hgp _ hgp0)
  have hhf : h' • (∞ : OnePoint ℂ) = ∞ :=
    fixed_of_period_three_in_pair (hhcube ∞) (Or.inl rfl) hhp0 (hhp _ hhp0)
  apply hnofix (P • (∞ : OnePoint ℂ))
  constructor
  · have he := congrArg (fun x : OnePoint ℂ ↦ P • x) hgf
    simpa only [g', mul_smul, smul_inv_smul] using he
  · have he := congrArg (fun x : OnePoint ℂ ↦ P • x) hhf
    simpa only [h', mul_smul, smul_inv_smul] using he

lemma local_homogeneous_metric_zero_of_diagonal_product
    {ψ : (Fin 2 → ℂ) → ℝ} (hψ : HomogeneousLocalPshMetric24 ψ)
    (P g h : GL (Fin 2) ℂ) {a : ℝ} (ha : 1 < a)
    (hdiag : ∀ v, P • ![(a : ℂ)*v 0,(a : ℂ)⁻¹*v 1] = g • (h • (P • v)))
    (hgi : ∀ v, ψ (g • v) = ψ v) (hhi : ∀ v, ψ (h • v) = ψ v)
    (hg3 : ∀ x : OnePoint ℂ, g • (g • (g • x)) = x)
    (hh3 : ∀ x : OnePoint ℂ, h • (h • (h • x)) = x)
    (hnofix : ∀ x : OnePoint ℂ, ¬ (g • x = x ∧ h • x = x)) :
    ∀ v, ψ v = 0 := by
  let φ : (Fin 2 → ℂ) → ℝ := fun v ↦ ψ (P • v)
  have hφ := hψ.pullback P
  obtain ⟨c, _, hc⟩ := hφ.hyperbolic_classification ha (fun v ↦ by
    rw [hdiag, hgi, hhi])
  by_cases hcZ : c = 0
  · intro v
    have he := hc (P⁻¹ • v)
    simpa only [smul_inv_smul, hcZ, zero_mul] using he
  have hz : ∀ v, φ v = 0 ↔ v 0 = 0 ∨ v 1 = 0 := by
    intro v
    change ψ (P • v) = 0 ↔ _
    rw [hc]
    simp [hcZ, mul_eq_zero]
  apply (conjugate_pair_contradiction hz P g h ?_ ?_ hg3 hh3 hnofix).elim
  · intro v
    simp only [φ, mul_smul, smul_inv_smul, hgi]
  · intro v
    simp only [φ, mul_smul, smul_inv_smul, hhi]

lemma source_expanding_gt_one : 1 < expandingRoot (1 + Real.sqrt 2) := by
  apply (hyperbolic_roots ?_).1
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

lemma source_eigenbasis_diagonalizes_inv :
    (source_A * source_B) * (source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) =
      (source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) *
        diagonal ![(expandingRoot (1 + Real.sqrt 2) : ℂ),
          (expandingRoot (1 + Real.sqrt 2) : ℂ)⁻¹] := by
  have ht : 2 < 1 + Real.sqrt 2 := by
    have hn := Real.sqrt_nonneg (2 : ℝ)
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hcontract : (contractingRoot (1 + Real.sqrt 2) : ℂ) =
      (expandingRoot (1 + Real.sqrt 2) : ℂ)⁻¹ := by
    have hh : (expandingRoot (1 + Real.sqrt 2) : ℂ) *
        (contractingRoot (1 + Real.sqrt 2) : ℂ) = 1 := by
      exact_mod_cast (hyperbolic_roots ht).2.2.2.2
    exact eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  have hd := hyperbolicBasis_diagonalizes ht
    (show (source_A * source_B).trace = ((1 + Real.sqrt 2 : ℝ) : ℂ) by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using source_product_trace)
    (show (source_A * source_B).det = 1 by
      rw [Matrix.det_mul, source_A_det, source_B_det, one_mul])
  rw [hcontract] at hd
  exact hd

lemma source_eigenbasis_diagonal_action (v : Fin 2 → ℂ) :
    source_eigenbasis • ![(expandingRoot (1 + Real.sqrt 2) : ℂ)*v 0,
      (expandingRoot (1 + Real.sqrt 2) : ℂ)⁻¹*v 1] =
      source_A_gl • (source_B_gl • (source_eigenbasis • v)) := by
  let a : ℂ := expandingRoot (1 + Real.sqrt 2)
  have hv : ![a*v 0,a⁻¹*v 1] = diagonal ![a,a⁻¹] *ᵥ v := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]
  change (source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ![a*v 0,a⁻¹*v 1] =
    source_A *ᵥ (source_B *ᵥ ((source_eigenbasis : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v))
  rw [hv, mulVec_mulVec, ← source_eigenbasis_diagonalizes_inv,
    ← mulVec_mulVec, ← mulVec_mulVec]

theorem source_invariant_local_homogeneous_metric_zero
    {ψ : (Fin 2 → ℂ) → ℝ} (hψ : HomogeneousLocalPshMetric24 ψ)
    (hA : ∀ v, ψ (source_A_gl • v) = ψ v)
    (hB : ∀ v, ψ (source_B_gl • v) = ψ v) : ∀ v, ψ v = 0 :=
  local_homogeneous_metric_zero_of_diagonal_product hψ source_eigenbasis source_A_gl
    source_B_gl source_expanding_gt_one source_eigenbasis_diagonal_action hA hB
    (projective_cube_identity source_A_cube) (projective_cube_identity source_B_cube)
    source_no_common_fixed_point

end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.DualForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology Metric
noncomputable section

lemma projective_usc_of_affine_usc {u : ProjectiveLine → ℝ}
    (hu : ∀ i : Fin 2, UpperSemicontinuous (fun z ↦ u (affineP1 i z))) :
    UpperSemicontinuous u := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro t
  have he : u ⁻¹' Set.Iio t = ⋃ i : Fin 2, affineP1 i '' ((u ∘ affineP1 i) ⁻¹' Set.Iio t) := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Iio,Set.mem_iUnion,Set.mem_image]
    constructor
    · intro hx
      obtain ⟨i,z,rfl⟩ := affineP1_cover x
      exact ⟨i,z,hx,rfl⟩
    · rintro ⟨i,z,hz,rfl⟩
      exact hz
  rw [he]
  exact isOpen_iUnion fun i ↦ (affineP1_isOpenEmbedding i).isOpenMap _
    ((hu i).isOpen_preimage _)

theorem projective_subharmonic_const {u : ProjectiveLine → ℝ}
    (hu : ∀ i : Fin 2, DiskSubharmonicOn Set.univ (fun z ↦ u (affineP1 i z))) :
    ∀ x y, u x = u y := by
  have husc : UpperSemicontinuous u := projective_usc_of_affine_usc
    (fun i ↦ upperSemicontinuousOn_univ_iff.mp (hu i).1)
  obtain ⟨p,_,hp⟩ := UpperSemicontinuousOn.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set ProjectiveLine).Nonempty)
    isCompact_univ (husc.upperSemicontinuousOn Set.univ)
  obtain ⟨i,z,hz⟩ := affineP1_cover p
  have hmax (q : ProjectiveLine) : u q ≤ u p := hp (Set.mem_univ q)
  have hi := (hu i).eq_const_of_max isOpen_univ isPreconnected_univ (Set.mem_univ z)
    (fun y _ ↦ by rw [hz]; exact hmax (affineP1 i y))
  have hone : u (1 : ℂ) = u p := by simpa only [affineP1_one,hz] using hi 1 (Set.mem_univ 1)
  have hall (j : Fin 2) (w : ℂ) : u (affineP1 j w) = u p := by
    have hj := (hu j).eq_const_of_max isOpen_univ isPreconnected_univ (Set.mem_univ (1 : ℂ))
      (fun y _ ↦ by rw [affineP1_one,hone]; exact hmax (affineP1 j y))
    simpa only [affineP1_one,hone] using hj w (Set.mem_univ w)
  intro x y
  obtain ⟨i,z,rfl⟩ := affineP1_cover x
  obtain ⟨j,w,rfl⟩ := affineP1_cover y
  exact (hall i z).trans (hall j w).symm

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
open scoped ComplexOrder

lemma coordinateOverlap_of_affine_eq {i j : StandardChart} {z w : BaseCoordinates}
    (h : affineQuadric i z=affineQuadric j w) : z ∈ coordinateOverlap i j := by
  rw [← affineQuadric_mem_range,h]
  exact ⟨w,rfl⟩

lemma coordinateChange_of_affine_eq {i j : StandardChart} {z w : BaseCoordinates}
    (h : affineQuadric i z=affineQuadric j w) : coordinateChange i j z=w := by
  rw [← coordinateChange_coord,h,coordQuadric_affine]

lemma exists_projective_gluing (f : Fin 2 → ℂ → ℝ)
    (h : ∀ i j z w, affineP1 i z=affineP1 j w → f i z=f j w) :
    ∃ u : ProjectiveLine → ℝ, ∀ i z, u (affineP1 i z)=f i z := by
  choose i z hz using affineP1_cover
  refine ⟨fun x ↦ f (i x) (z x),fun j w ↦ ?_⟩
  exact h _ _ _ _ (hz (affineP1 j w))

namespace EqualizerData.PshDualForm
variable {D : EqualizerData} (Q : D.PshDualForm)

lemma firstNorm_same_ruling (i j k : Fin 2) (z y w c : ℂ)
    (h : affineP1 j y=affineP1 k w) :
    Q.firstNorm (i,j) ((z,y),c)=Q.firstNorm (i,k) ((z,w),c) := by
  have he : affineQuadric (i,j) (z,y)=affineQuadric (i,k) (z,w) := Prod.ext rfl h
  rw [Q.firstNorm_change (i,j) (i,k) (coordinateOverlap_of_affine_eq he),
    coordinateChange_of_affine_eq he]
  simp [EqualizerData.topFactor,firstFactor,scalarFactor]

lemma secondNorm_same_ruling (i j k : Fin 2) (z y w c : ℂ)
    (h : affineP1 j y=affineP1 k w) :
    Q.secondNorm (j,i) ((y,z),c)=Q.secondNorm (k,i) ((w,z),c) := by
  have he : affineQuadric (j,i) (y,z)=affineQuadric (k,i) (w,z) := Prod.ext h rfl
  rw [Q.secondNorm_change (j,i) (k,i) (coordinateOverlap_of_affine_eq he),
    coordinateChange_of_affine_eq he]
  simp [EqualizerData.quotientFactor,secondFactor,scalarFactor]

lemma firstNorm_ruling_const (i j k : Fin 2) (z y w c : ℂ) :
    Q.firstNorm (i,j) ((z,y),c)=Q.firstNorm (i,k) ((z,w),c) := by
  obtain ⟨u,hu⟩ := exists_projective_gluing (fun j y ↦ Q.firstNorm (i,j) ((z,y),c))
    (fun j k y w h ↦ Q.firstNorm_same_ruling i j k z y w c h)
  have hp : ∀ j : Fin 2, DiskSubharmonicOn Set.univ (fun y ↦ u (affineP1 j y)) := by
    intro j
    simpa only [hu,Function.comp_def] using
      (Q.firstNorm_psh (i,j)).2 Set.univ isOpen_univ (fun y : ℂ ↦ ((z,y),c))
        (by fun_prop) (mapsTo_univ _ _)
  simpa only [hu] using projective_subharmonic_const hp (affineP1 j y) (affineP1 k w)

lemma secondNorm_ruling_const (i j k : Fin 2) (z y w c : ℂ) :
    Q.secondNorm (j,i) ((y,z),c)=Q.secondNorm (k,i) ((w,z),c) := by
  obtain ⟨u,hu⟩ := exists_projective_gluing (fun j y ↦ Q.secondNorm (j,i) ((y,z),c))
    (fun j k y w h ↦ Q.secondNorm_same_ruling i j k z y w c h)
  have hp : ∀ j : Fin 2, DiskSubharmonicOn Set.univ (fun y ↦ u (affineP1 j y)) := by
    intro j
    simpa only [hu,Function.comp_def] using
      (Q.secondNorm_psh (j,i)).2 Set.univ isOpen_univ (fun y : ℂ ↦ ((y,z),c))
        (by fun_prop) (mapsTo_univ _ _)
  simpa only [hu] using projective_subharmonic_const hp (affineP1 j y) (affineP1 k w)

end EqualizerData.PshDualForm

lemma homogeneousCoordinate_smul (i : Fin 2) {v : FiberCoordinates} (hv : v i≠0)
    {c : ℂ} (hc : c≠0) : homogeneousCoordinate i (c • v)=homogeneousCoordinate i v := by
  simp only [homogeneousCoordinate,Pi.smul_apply,smul_eq_mul]
  field_simp

lemma homogeneousRepresentative (i : Fin 2) {v : FiberCoordinates} (hv : v i≠0) :
    v=v i • affineRepresentative i (homogeneousCoordinate i v) := by
  fin_cases i <;> dsimp at hv <;> ext k <;> fin_cases k <;>
    simp [affineRepresentative,homogeneousCoordinate,otherIndex,Pi.smul_apply,smul_eq_mul] <;>
    field_simp

lemma homogeneousCoordinate_overlap (i j : Fin 2) {v : FiberCoordinates}
    (_hi : v i≠0) (hj : v j≠0) : i=j ∨ homogeneousCoordinate i v≠0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [homogeneousCoordinate,otherIndex]

lemma homogeneousCoordinate_change (i j : Fin 2) {v : FiberCoordinates}
    (_hi : v i≠0) (_hj : v j≠0) :
    scalarCoordinateChange i j (homogeneousCoordinate i v)=homogeneousCoordinate j v := by
  fin_cases i <;> fin_cases j <;>
    simp [scalarCoordinateChange,homogeneousCoordinate,otherIndex]

lemma homogeneousCoordinate_factor (i j : Fin 2) {v : FiberCoordinates}
    (hi : v i≠0) (_hj : v j≠0) :
    scalarFactor i j (homogeneousCoordinate i v)*v i=v j := by
  fin_cases i <;> fin_cases j <;> dsimp at hi <;>
    simp [scalarFactor,homogeneousCoordinate,otherIndex] <;> field_simp

namespace PshLine24
variable (L : PshLine24)

lemma zero (i : Fin 2) (z : ℂ) : L.value i (z,0)=0 := by
  simpa using L.scalar i z 0 0

lemma coordinate_independent (i j : Fin 2) {v : FiberCoordinates}
    (hi : v i≠0) (hj : v j≠0) :
    L.value i (homogeneousCoordinate i v,(v i)^24)=
      L.value j (homogeneousCoordinate j v,(v j)^24) := by
  rw [L.change _ _ _ (homogeneousCoordinate_overlap i j hi hj),
    homogeneousCoordinate_change i j hi hj,← mul_pow,homogeneousCoordinate_factor i j hi hj]

lemma homogeneousNorm_chart (i : Fin 2) {v : FiberCoordinates} (hi : v i≠0) :
    L.homogeneousNorm v=L.value i (homogeneousCoordinate i v,(v i)^24) := by
  fin_cases i
  · change v 0≠0 at hi
    simp [homogeneousNorm,hi]
  · by_cases h : v 0=0
    · simp [homogeneousNorm,h]
    · simp only [homogeneousNorm,h,↓reduceIte]
      exact L.coordinate_independent 0 1 h hi

@[simp] lemma homogeneousNorm_zero : L.homogeneousNorm 0=0 := by
  simp [homogeneousNorm,L.zero]

lemma homogeneousNorm_nonneg (v : FiberCoordinates) : 0 ≤ L.homogeneousNorm v := by
  unfold homogeneousNorm
  split_ifs <;> exact L.nonneg _ _ _

lemma homogeneousNorm_scalar (c : ℂ) (v : FiberCoordinates) :
    L.homogeneousNorm (c • v)=‖c‖^48*L.homogeneousNorm v := by
  by_cases hc : c=0
  · subst c; simp
  by_cases hv : v=0
  · subst v; simp
  obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp hv
  have hci : (c • v) i≠0 := mul_ne_zero hc hi
  rw [L.homogeneousNorm_chart i hci,L.homogeneousNorm_chart i hi,
    homogeneousCoordinate_smul i hi hc]
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,L.scalar,norm_pow,← pow_mul]

lemma value_weighted_chart (i : Fin 2) {v : FiberCoordinates} (hi : v i≠0) (t : ℂ) :
    L.value i (homogeneousCoordinate i v,t*(v i)^24)=‖t‖^2*L.homogeneousNorm v := by
  rw [L.scalar,L.homogeneousNorm_chart i hi]

lemma weightedChart_differentiableAt {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → FiberCoordinates} {t : E → ℂ} {x : E} (i : Fin 2)
    (hf : DifferentiableAt ℂ f x) (ht : DifferentiableAt ℂ t x) (hi : f x i≠0) :
    DifferentiableAt ℂ (fun y ↦ (homogeneousCoordinate i (f y),t y*(f y i)^24)) x := by
  change DifferentiableAt ℂ (fun y ↦ (f y (otherIndex i)/f y i,t y*(f y i)^24)) x
  have hfi (j : Fin 2) : DifferentiableAt ℂ (fun y ↦ f y j) x := (differentiableAt_pi.mp hf) j
  simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply,Pi.pow_apply] using
    ((hfi (otherIndex i)).mul ((hfi i).inv hi)).prodMk (ht.mul ((hfi i).pow 24))

lemma weightedNorm_usc {E : Type u2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {f : E → FiberCoordinates} {t : E → ℂ}
    (hf : ∀ x ∈ U, DifferentiableAt ℂ f x) (ht : ∀ x ∈ U, DifferentiableAt ℂ t x)
    (hn : ∀ x ∈ U, f x≠0) :
    UpperSemicontinuousOn (fun x ↦ ‖t x‖^2*L.homogeneousNorm (f x)) U := by
  intro x hx
  obtain ⟨i,hi⟩ : ∃ i, f x i≠0 := by
    simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp (hn x hx)
  have hc := (weightedChart_differentiableAt i (hf x hx) (ht x hx) hi).continuousAt
  have hu : UpperSemicontinuousAt (fun y ↦ L.value i
      (homogeneousCoordinate i (f y),t y*(f y i)^24)) x :=
    UpperSemicontinuousAt.comp (upperSemicontinuousOn_univ_iff.mp (L.psh i).1 _) hc
  apply (hu.upperSemicontinuousWithinAt U).congr_of_eventuallyEq hx
  have he : ∀ᶠ y in 𝓝 x, f y i≠0 := ((continuous_apply i).continuousAt.comp (hf x hx).continuousAt).eventually_ne hi
  filter_upwards [nhdsWithin_le_nhds he] with y hy
  exact L.value_weighted_chart i hy (t y)

lemma homogeneousNorm_usc : UpperSemicontinuousOn L.homogeneousNorm ({0}ᶜ : Set FiberCoordinates) := by
  have h := L.weightedNorm_usc (E := FiberCoordinates) (U := ({0}ᶜ : Set FiberCoordinates))
    (f := id) (t := fun _ ↦ (1 : ℂ)) (fun _ _ ↦ differentiableAt_id)
    (fun _ _ ↦ differentiableAt_const _) (fun _ hv ↦ hv)
  simpa only [id_eq,norm_one,one_pow,one_mul] using h

lemma homogeneousNorm_disk (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → FiberCoordinates) (t : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (ht : AnalyticOnNhd ℂ t U)
    (hn : ∀ z ∈ U, f z≠0) :
    LocalDiskSubmeanOn U (fun z ↦ ‖t z‖^2*L.homogeneousNorm (f z)) := by
  refine ⟨L.weightedNorm_usc (fun z hz ↦ (hf z hz).differentiableAt)
    (fun z hz ↦ (ht z hz).differentiableAt) hn,?_⟩
  intro x hx
  obtain ⟨i,hi⟩ : ∃ i, f x i≠0 := by
    simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp (hn x hx)
  have he : ∀ᶠ y in 𝓝 x, f y i≠0 := ((continuous_apply i).continuousAt.comp (hf x hx).continuousAt).eventually_ne hi
  obtain ⟨R,hR,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hU.mem_nhds hx) he)
  have hB : closedBall x (R/2) ⊆ ball x R :=
    closedBall_subset_ball (by linarith)
  have hd : DifferentiableOn ℂ
      (fun z ↦ (homogeneousCoordinate i (f z),t z*(f z i)^24)) (ball x R) := by
    intro z hz
    exact (weightedChart_differentiableAt i
      (hf z (hball (ball_subset_closedBall hz)).1).differentiableAt
      (ht z (hball (ball_subset_closedBall hz)).1).differentiableAt
      (hball (ball_subset_closedBall hz)).2).differentiableWithinAt
  have hs := (L.psh i).2 (ball x R) isOpen_ball _ hd (mapsTo_univ _ _)
  obtain ⟨hint,hmean⟩ := hs.2 x (mem_ball_self hR) (R/2) (by linarith) hB
  have hAE : (fun z ↦ L.value i (homogeneousCoordinate i (f z),t z*(f z i)^24))
      =ᵐ[MeasureTheory.volume.restrict (ball x (R/2))]
      (fun z ↦ ‖t z‖^2*L.homogeneousNorm (f z)) :=
    (MeasureTheory.ae_restrict_mem measurableSet_ball).mono (fun z hz ↦
      L.value_weighted_chart i (hball (ball_subset_closedBall (hB (ball_subset_closedBall hz)))).2 (t z))
  refine ⟨R/2,by linarith,fun z hz ↦ (hball (ball_subset_closedBall (hB hz))).1,
    hint.congr hAE,?_⟩
  change (MeasureTheory.volume (ball x (R/2))).toReal *
    L.value i (homogeneousCoordinate i (f x),t x*(f x i)^24) ≤
      ∫ z in ball x (R/2), L.value i (homogeneousCoordinate i (f z),t z*(f z i)^24) at hmean
  rwa [MeasureTheory.integral_congr_ae hAE,L.value_weighted_chart i hi] at hmean

lemma homogeneousMetric : HomogeneousLocalPshMetric24 L.homogeneousNorm :=
  ⟨L.homogeneousNorm_nonneg,L.homogeneousNorm_scalar,L.homogeneousNorm_usc,L.homogeneousNorm_disk⟩

end PshLine24

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix
noncomputable section
namespace EqualizerData.PshDualForm
variable {D : EqualizerData} (Q : D.PshDualForm)

lemma firstLine_value (i j : Fin 2) (z w c : ℂ) :
    Q.firstLine.value i (z,c)=Q.firstNorm (i,j) ((z,w),c) :=
  Q.firstNorm_ruling_const i 0 j z 0 w c

lemma secondLine_value (i j : Fin 2) (z w c : ℂ) :
    Q.secondLine.value j (w,c)=Q.secondNorm (i,j) ((z,w),c) :=
  Q.secondNorm_ruling_const j 0 i w 0 z c

end EqualizerData.PshDualForm

lemma matrixBranchDenominator_homogeneous (M : TwoMatrix) (i j : Fin 2)
    {v : FiberCoordinates} (hi : v i≠0) :
    matrixBranchDenominator M (i,j)
      (homogeneousCoordinate i v,homogeneousCoordinate j (M*ᵥv))*v i=(M*ᵥv) j := by
  have h := congrFun (congrArg (M.mulVec) (homogeneousRepresentative i hi)) j
  simpa only [mulVec_smul,Pi.smul_apply,smul_eq_mul,matrixBranchDenominator,
    mulVec,dotProduct,Fin.sum_univ_two,mul_comm,mul_left_comm,mul_assoc,mul_add] using h.symm

lemma matrixGraphValue_homogeneous (M : TwoMatrix) (i j : Fin 2)
    {v : FiberCoordinates} (hi : v i≠0) (hj : (M*ᵥv) j≠0) :
    matrixGraphValue M (i,j)
      (homogeneousCoordinate i v,homogeneousCoordinate j (M*ᵥv))=0 := by
  apply (matrixGraphValue_zero_iff _ _ _).mpr
  have h' := homogeneousRepresentative j hj
  have hd := matrixBranchDenominator_homogeneous M i j hi
  apply (smul_right_injective _ hi)
  dsimp only
  rw [← mulVec_smul,← homogeneousRepresentative i hi,smul_smul,mul_comm,hd,← h']

namespace EqualizerData.PshDualForm
variable {T : GraphScalars} (Q : T.equalizerData.PshDualForm)

lemma graph_identifies_homogeneous (k : Fin 3) {v : FiberCoordinates}
    (hv : v≠0) (hw : T.matrices k*ᵥv≠0) :
    Q.firstLine.homogeneousNorm v=Q.secondLine.homogeneousNorm (T.matrices k*ᵥv) := by
  obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp hv
  obtain ⟨j,hj⟩ : ∃ j, (T.matrices k*ᵥv) j≠0 := by
    simpa only [not_forall,Pi.zero_apply] using funext_iff.not.mp hw
  let z : BaseCoordinates := (homogeneousCoordinate i v,homogeneousCoordinate j (T.matrices k*ᵥv))
  have hg : matrixGraphValue (T.matrices k) (i,j) z=0 := matrixGraphValue_homogeneous _ _ _ hi hj
  have hd : baseEval (T.divisorPolynomial (i,j)) z=0 := by
    simp only [GraphScalars.divisorPolynomial,baseEval_mul,baseEval_matrixGraphPolynomial]
    fin_cases k
    · exact mul_eq_zero_of_left (mul_eq_zero_of_left hg _) _
    · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ hg) _
    · exact mul_eq_zero_of_right _ hg
  have hb := T.chartLift_branch k (i,j) z hg
  have hn := matrixBranchDenominator_homogeneous (T.matrices k) i j hi
  have hcoef : baseEval (T.chartLift (i,j)) z*((T.matrices k*ᵥv) j)^24=(v i)^24 := by
    rw [← hn,mul_pow,← mul_assoc,hb,one_mul]
  rw [Q.firstLine.homogeneousNorm_chart i hi,Q.secondLine.homogeneousNorm_chart j hj,
    Q.firstLine_value i j _ z.2,Q.secondLine_value i j z.1]
  change Q.value (i,j) (z,![v i^24,0])=
    Q.value (i,j) (z,![baseEval (T.chartLift (i,j)) z*((T.matrices k*ᵥv) j)^24,
      baseEval (T.divisorPolynomial (i,j)) z*((T.matrices k*ᵥv) j)^24])
  rw [hcoef,hd,zero_mul]

end EqualizerData.PshDualForm
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section

namespace EqualizerData.PshDualForm
variable (Q : sourceGraphScalars.equalizerData.PshDualForm)

lemma source_lines_identical (v : FiberCoordinates) :
    Q.firstLine.homogeneousNorm v=Q.secondLine.homogeneousNorm v := by
  by_cases hv : v=0
  · simp [hv]
  simpa using Q.graph_identifies_homogeneous 0 hv (by simpa using hv)

lemma source_first_homogeneous_zero : ∀ v, Q.firstLine.homogeneousNorm v=0 := by
  apply source_invariant_local_homogeneous_metric_zero Q.firstLine.homogeneousMetric
  · intro v
    by_cases hv : v=0
    · simp [hv]
    have hw : sourceGraphScalars.matrices 1*ᵥv≠0 :=
      (smul_ne_zero_iff_ne source_A_gl).mpr hv
    change Q.firstLine.homogeneousNorm (source_A*ᵥv)=Q.firstLine.homogeneousNorm v
    rw [Q.source_lines_identical]
    exact (Q.graph_identifies_homogeneous 1 hv hw).symm
  · intro v
    by_cases hv : v=0
    · simp [hv]
    have hw : sourceGraphScalars.matrices 2*ᵥv≠0 :=
      (smul_ne_zero_iff_ne source_B_gl).mpr hv
    change Q.firstLine.homogeneousNorm (source_B*ᵥv)=Q.firstLine.homogeneousNorm v
    rw [Q.source_lines_identical]
    exact (Q.graph_identifies_homogeneous 2 hv hw).symm

lemma source_second_homogeneous_zero (v : FiberCoordinates) :
    Q.secondLine.homogeneousNorm v=0 := by
  rw [← Q.source_lines_identical,Q.source_first_homogeneous_zero]

end EqualizerData.PshDualForm

lemma PshLine24.value_zero_of_homogeneous_zero (L : PshLine24)
    (h : ∀ v, L.homogeneousNorm v=0) (i : Fin 2) (z c : ℂ) : L.value i (z,c)=0 := by
  have hv : affineRepresentative i z i≠0 := by simp
  have hval := h (affineRepresentative i z)
  rw [L.homogeneousNorm_chart i hv] at hval
  simp only [homogeneousCoordinate_affineRepresentative,affineRepresentative_index,one_pow] at hval
  have hs := L.scalar i z c 1
  simpa only [mul_one,hval,mul_zero] using hs

namespace EqualizerData.PshDualForm
variable (Q : sourceGraphScalars.equalizerData.PshDualForm)

lemma source_firstNorm_zero (i : StandardChart) (z : BaseCoordinates) (c : ℂ) :
    Q.firstNorm i (z,c)=0 := by
  rw [← Q.firstLine_value i.1 i.2 z.1 z.2 c]
  exact Q.firstLine.value_zero_of_homogeneous_zero Q.source_first_homogeneous_zero _ _ _

lemma source_secondNorm_zero (i : StandardChart) (z : BaseCoordinates) (c : ℂ) :
    Q.secondNorm i (z,c)=0 := by
  rw [← Q.secondLine_value i.1 i.2 z.1 z.2 c]
  exact Q.secondLine.value_zero_of_homogeneous_zero Q.source_second_homogeneous_zero _ _ _

lemma source_value_zero_off_divisor (i : StandardChart) (z : BaseCoordinates)
    (hd : baseEval (sourceGraphScalars.divisorPolynomial i) z≠0) (v : FiberCoordinates) :
    Q.value i (z,v)=0 := by
  obtain ⟨H,hH,h⟩ := Q.quadratic i z
  have hker (u : FiberCoordinates) (hu : Q.value i (z,u)=0) : H*ᵥu=0 := by
    apply (hH.dotProduct_mulVec_zero_iff u).mp
    rw [h] at hu
    exact Complex.ext hu (hH.dotProduct_mulVec_nonneg u).2.symm
  let d := baseEval (sourceGraphScalars.divisorPolynomial i) z
  let a := baseEval (sourceGraphScalars.chartLift i) z
  have hk1 : H*ᵥ![1,0]=0 := hker _ (Q.source_firstNorm_zero i z 1)
  have hk2 : H*ᵥ![a,d]=0 := hker _ (by
      simpa [secondNorm,GraphScalars.equalizerData,a,d]
        using Q.source_secondNorm_zero i z 1)
  have hv : v=(v 0-a*v 1/d) • ![1,0]+(v 1/d) • ![a,d] := by
    ext k
    fin_cases k
    · simp [smul_eq_mul,Pi.add_apply]
      field_simp [d,hd]
      ring
    · simp [smul_eq_mul,Pi.add_apply]
      field_simp [d,hd]
  have hvH : H*ᵥv=0 := by
    rw [hv,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hk1,hk2,smul_zero,smul_zero,add_zero]
  rw [h,hvH,dotProduct_zero,Complex.zero_re]

end EqualizerData.PshDualForm

lemma DiskPshOn.eq_zero_of_off_polynomial {q : BaseCoordinates → ℝ}
    (hq : DiskPshOn Set.univ q) (hn : ∀ z, 0 ≤ q z)
    {p : BasePolynomial} (hp : p≠0) (hz : ∀ z, baseEval p z≠0 → q z=0) : ∀ z, q z=0 := by
  obtain ⟨w,hw⟩ := (dense_polynomial_nonzero hp).nonempty
  intro z
  let γ : ℂ → BaseCoordinates := fun t ↦ z+t • (w-z)
  have hγ : AnalyticOnNhd ℂ γ Set.univ := by
    intro t _
    dsimp [γ]
    fun_prop
  have hr : AnalyticOnNhd ℂ (baseEval p ∘ γ) Set.univ :=
    (analytic_baseEval p).comp hγ (mapsTo_univ _ _)
  have he : ¬ Set.EqOn (baseEval p ∘ γ) 0 Set.univ := by
    intro he
    have h := he (x := (1 : ℂ)) (mem_univ _)
    have hγ1 : γ 1=w := by simp [γ]
    exact hw (by simpa only [Function.comp_apply,hγ1,Pi.zero_apply] using h)
  have hne := (hr.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left he
  have hae : ∀ᵐ t ∂volume, (baseEval p ∘ γ) t≠0 := by
    have h := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℂ)) MeasurableSet.univ hne
    change ∀ᵐ t ∂volume.restrict (univ : Set ℂ), (baseEval p ∘ γ) t≠0 at h
    simpa only [Measure.restrict_univ] using h
  have hqae : (q ∘ γ)=ᵐ[volume] (fun _ ↦ 0) := hae.mono fun t ht ↦ hz (γ t) ht
  have hs := hq.2 Set.univ isOpen_univ γ hγ.differentiableOn (mapsTo_univ _ _)
  have hm := (hs.2 0 (mem_univ _) 1 (by norm_num) (subset_univ _)).2
  rw [integral_congr_ae (ae_restrict_of_ae hqae),integral_zero] at hm
  have hvol : 0 < (volume (ball (0 : ℂ) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume (0 : ℂ) (by norm_num : (0 : ℝ) < 1)))
      (measure_ne_top_of_subset ball_subset_closedBall (isCompact_closedBall (0 : ℂ) 1).measure_ne_top)
  have hγ0 : γ 0=z := by simp [γ]
  simp only [Function.comp_apply,hγ0] at hm
  exact le_antisymm (by nlinarith [hn z]) (hn z)

namespace EqualizerData.PshDualForm
variable (Q : sourceGraphScalars.equalizerData.PshDualForm)

theorem source_value_zero (i : StandardChart) (z : BaseCoordinates) (v : FiberCoordinates) :
    Q.value i (z,v)=0 := by
  have hp : DiskPshOn Set.univ (fun w ↦ Q.value i (w,v)) :=
    (Q.psh i).comp (by fun_prop) (mapsTo_univ _ _)
  exact hp.eq_zero_of_off_polynomial (fun w ↦ Q.nonneg i w v)
    (sourceGraphScalars.divisorPolynomial_nonzero i)
    (fun w hw ↦ Q.source_value_zero_off_divisor i w hw v) z

end EqualizerData.PshDualForm
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Noncollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Matrix Complex Filter Topology BigOperators Set Metric MeasureTheory
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
lemma norm_matrix_pair_le {n : Type u1} [Fintype n]
    (H : Matrix n n ℂ) (v w : n → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, ‖H i j‖ ≤ C) :
    ‖star v ⬝ᵥ H *ᵥ w‖ ≤ (Fintype.card n : ℝ)^2 * C * ‖v‖ * ‖w‖ := by
  change ‖∑ i, star (v i) * ∑ j, H i j * w j‖ ≤ _
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, ‖star (v i) * (H i j * w j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : n, ∑ _j : n, ‖v‖ * (C * ‖w‖) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul, norm_star, norm_mul]
      exact mul_le_mul (norm_le_pi_norm v i)
        (mul_le_mul (hb i j) (norm_le_pi_norm w j) (norm_nonneg _) hC)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by simp [pow_two]; ring

lemma quadraticValue_sub_bound {n : Type u2} [Fintype n]
    (H : Matrix n n ℂ) (v w : n → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, ‖H i j‖ ≤ C) :
    |quadraticValue H v - quadraticValue H w| ≤
      (Fintype.card n : ℝ)^2 * C * ‖v-w‖ * (‖v‖+‖w‖) := by
  have he : star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w =
      star (v-w) ⬝ᵥ H *ᵥ v + star w ⬝ᵥ H *ᵥ (v-w) := by
    simp only [star_sub, sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
    ring
  calc
    _ = |(star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w).re| := by
      simp [quadraticValue]
    _ ≤ ‖star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w‖ := Complex.abs_re_le_norm _
    _ ≤ ‖star (v-w) ⬝ᵥ H *ᵥ v‖ + ‖star w ⬝ᵥ H *ᵥ (v-w)‖ := by
      rw [he]; exact norm_add_le _ _
    _ ≤ (Fintype.card n : ℝ)^2 * C * ‖v-w‖ * ‖v‖ +
        (Fintype.card n : ℝ)^2 * C * ‖w‖ * ‖v-w‖ :=
      add_le_add (norm_matrix_pair_le H _ _ hC hb) (norm_matrix_pair_le H _ _ hC hb)
    _ = _ := by ring

theorem quadraticValue_moving_vector {n : Type u3} [Fintype n]
    (H : ℕ → Matrix n n ℂ) {v : ℕ → n → ℂ} {w : n → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ k i j, ‖H k i j‖ ≤ C)
    (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k ↦ quadraticValue (H k) (v k) - quadraticValue (H k) w)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun k ↦ (Fintype.card n : ℝ)^2 * C * ‖v k-w‖ * (‖v k‖+‖w‖))
      atTop (𝓝 0) := by
    have hs : Tendsto (fun k ↦ ‖v k-w‖) atTop (𝓝 ‖w-w‖) :=
      (hv.sub tendsto_const_nhds).norm
    have hh : Tendsto (fun k ↦ (Fintype.card n : ℝ)^2 * C * ‖v k-w‖ * (‖v k‖+‖w‖))
        atTop (𝓝 ((Fintype.card n : ℝ)^2 * C * ‖w-w‖ * (‖w‖+‖w‖))) :=
      (tendsto_const_nhds.mul hs).mul (hv.norm.add tendsto_const_nhds)
    simpa using hh
  apply squeeze_zero_norm
    (fun k ↦ by simpa only [Real.norm_eq_abs] using
      quadraticValue_sub_bound (H k) (v k) w hC (hb k)) ht

lemma nonnegative_usc_integrableOn_ball {Ω : Set (ℂ × ℂ)} {q : ℂ × ℂ → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (hpos : ∀ x ∈ Ω, 0 ≤ q x)
    {x : ℂ × ℂ} {r : ℝ} (hb : closedBall x r ⊆ Ω) :
    IntegrableOn q (ball x r) := by
  obtain ⟨C,hC⟩ := (hq.mono hb).bddAbove_of_isCompact (isCompact_closedBall x r)
  have hmeas : AEStronglyMeasurable q (volume.restrict (ball x r)) :=
    (aemeasurable_restrict_of_measurable_subtype measurableSet_ball
      (upperSemicontinuousOn_iff_restrict.mpr
        (hq.mono (ball_subset_closedBall.trans hb))).measurable).aestronglyMeasurable
  exact (integrableOn_const (C := C)
      (measure_ne_top_of_subset ball_subset_closedBall
        (isCompact_closedBall x r).measure_ne_top)).mono' hmeas
    ((ae_restrict_mem measurableSet_ball).mono fun y hy ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos y (hb (ball_subset_closedBall hy)))]
      exact hC (mem_image_of_mem _ (ball_subset_closedBall hy)))

local instance instIsAddHaarMeasureProdComplexVolume_solutions_6_r6716fe_1 : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)
theorem moving_points_force_nonzero_limit
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {u : ℕ → (ℂ × ℂ) → ℝ} {q : (ℂ × ℂ) → ℝ}
    (hu : ∀ k, DiskPshOn Ω (u k)) (hpos : ∀ k x, x ∈ Ω → 0 ≤ u k x)
    {xm : ℕ → ℂ × ℂ} {x : ℂ × ℂ} {r : ℝ} (hr : 0 < r)
    (hb : closedBall x (3*r) ⊆ Ω)
    (hx : Tendsto xm atTop (𝓝 x))
    (hn : Tendsto (fun k ↦ u k (xm k)) atTop (𝓝 1))
    (hl : Tendsto (fun k ↦ ⨍ y in ball x (2*r), u k y) atTop
      (𝓝 (⨍ y in ball x (2*r), q y))) :
    ∃ y ∈ ball x (2*r), q y ≠ 0 := by
  have hb2 : closedBall x (2*r) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hb
  have hv (c : ℂ × ℂ) {s : ℝ} (hs : 0 < s) : 0 < (volume (ball c s)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume c hs))
      (measure_ne_top_of_subset ball_subset_closedBall (isCompact_closedBall c s).measure_ne_top)
  have hV := hv x (show 0 < 2*r by positivity)
  have hW := hv (0 : ℂ × ℂ) hr
  let a : ℝ := (volume (ball x (2*r))).toReal⁻¹ *
    ((volume (ball (0 : ℂ × ℂ) r)).toReal * (1/2))
  apply nonzero_of_average_limit measurableSet_ball (a := a)
    (mul_pos (inv_pos.mpr hV) (mul_pos hW (by norm_num))) hl
  have hxe : ∀ᶠ k in atTop, dist (xm k) x < r :=
    hx.eventually (ball_mem_nhds x hr)
  have hne : ∀ᶠ k in atTop, (1/2 : ℝ) ≤ u k (xm k) :=
    ((tendsto_order.mp hn).1 (1/2) (by norm_num)).mono fun _ h ↦ h.le
  filter_upwards [hxe,hne] with k hk hn'
  have hi := nonnegative_usc_integrableOn_ball (hu k).1 (hpos k) hb2
  have hm := (hu k).moving_base_mass hΩ hr hk hb
    (fun y hy ↦ hpos k y (hb2 (ball_subset_closedBall hy))) hi hn'
  simpa [a, setAverage_eq, smul_eq_mul, measureReal_def] using
    mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hV.le)

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

lemma averages_globalValue (i : StandardChart) (n : ℕ) (x : BaseCoordinates) (r : ℝ)
    (v : FiberCoordinates) (hb : ball x r ⊆ traceInterior (i,n)) :
    Tendsto (fun k ↦ ⨍ y in ball x r, (P (X.subsequence k)).value i (y,v)) atTop
      (𝓝 (⨍ y in ball x r, X.globalValue i (y,v))) := by
  have he (k : ℕ) : (⨍ y in ball x r, quadraticValue (cutoffTrace (P (X.subsequence k)) (i,n) y) v)=
      ⨍ y in ball x r, (P (X.subsequence k)).value i (y,v) := by
    apply setAverage_congr_fun measurableSet_ball
    apply Eventually.of_forall
    intro y hy
    rw [cutoffTrace_eq _ _ (traceDomain_subset_support (i,n) (traceInterior_subset_domain (i,n) (hb hy)))]
    rfl
  have hq : (⨍ y in ball x r, quadraticValue (X.matrix (i,n) y) v)=
      ⨍ y in ball x r, X.globalValue i (y,v) := by
    apply setAverage_congr_fun measurableSet_ball
    apply Eventually.of_forall
    intro y hy
    exact (X.globalValue_eq_value i n (p := (y,v)) (hb hy)).symm
  simpa only [he,hq] using X.averages (i,n) x r v hb

lemma globalValue_nonzero_of_sequence
    (i : StandardChart) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (z : ℕ → BaseCoordinates) (v : ℕ → FiberCoordinates)
    (x : BaseCoordinates) (w : FiberCoordinates)
    (hxlim : Tendsto z atTop (𝓝 x)) (hvlim : Tendsto v atTop (𝓝 w))
    (hxn : dist x 0 ≤ 1)
    (hbnd : ∀ k t, (P (X.subsequence (φ k))).value i (z k,t) ≤ ‖t‖^2)
    (hnorm : Tendsto (fun k ↦ (P (X.subsequence (φ k))).value i (z k,v k)) atTop (𝓝 1)) :
    ∃ y, X.globalValue i (y,w) ≠ 0 := by
  let seq (k : ℕ) := X.subsequence (φ k)
  have hcoeff (k : ℕ) (b c : Fin 2) : ‖(P (seq k)).matrix i (z k) b c‖ ≤ 4 := by
    have hm : ‖(P (seq k)).matrix i (z k)‖ ≤ 4 * 1 :=
      norm_matrix_of_quadratic_bound ((P (seq k)).positive i _).posSemidef
        (C := 1) (by norm_num)
        (fun t ↦ by simpa only [one_mul, TwistedPshForm.value] using hbnd k t)
    calc
      _ ≤ ‖(P (seq k)).matrix i (z k) b‖ := norm_le_pi_norm _ c
      _ ≤ ‖(P (seq k)).matrix i (z k)‖ := norm_le_pi_norm _ b
      _ ≤ 4 := by simpa only [mul_one] using hm
  have hdiff := quadraticValue_moving_vector (fun k ↦ (P (seq k)).matrix i (z k))
    (by norm_num : (0:ℝ)≤4) hcoeff hvlim
  have hfixed : Tendsto (fun k ↦ (P (seq k)).value i (z k,w)) atTop (𝓝 1) := by
    have h := hnorm.sub hdiff
    simpa only [TwistedPshForm.value,seq,sub_sub_cancel,sub_zero] using h
  have hball : closedBall x (3*(1/4:ℝ)) ⊆ traceInterior (i,0) := by
    apply closedBall_subset_ball'
    simp only [Nat.cast_zero, zero_add]
    linarith
  have hb : ball x (2*(1/4:ℝ)) ⊆ traceInterior (i,0) :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by norm_num)).trans hball)
  have hav := (X.averages_globalValue i 0 x (2*(1/4:ℝ)) w hb).comp hφ.tendsto_atTop
  have hp (k : ℕ) : DiskPshOn (traceInterior (i,0))
      (fun y : BaseCoordinates ↦ (P (seq k)).value i (y,w)) :=
    ((P (seq k)).psh i).comp (f := fun y : BaseCoordinates ↦ (y,w))
      (by fun_prop) (mapsTo_univ _ _)
  obtain ⟨y,_,hy⟩ := moving_points_force_nonzero_limit (Ω := traceInterior (i,0)) isOpen_ball hp
    (fun k y _ ↦ (P (seq k)).value_nonneg i y w)
    (by norm_num : (0:ℝ)<1/4) hball hxlim hfixed hav
  exact ⟨y,hy⟩

theorem globalValue_nonzero
    (hP : ∀ k i z, ‖z‖≤1 → ∀ v, (P k).value i (z,v)≤‖v‖^2)
    (hN : ∀ k, ∃ i z v, ‖z‖≤1 ∧ ‖v‖≤1 ∧ (P k).value i (z,v)=1) :
    ∃ i z v, X.globalValue i (z,v)≠0 := by
  choose chart z v hz hv hn using hN
  let S := StandardChart × (BaseCoordinates × FiberCoordinates)
  let p (k : ℕ) : S := (chart (X.subsequence k),(z (X.subsequence k),v (X.subsequence k)))
  let K : Set S := univ ×ˢ (closedBall 0 1 ×ˢ closedBall 0 1)
  have hK : IsCompact K := isCompact_univ.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hp (k : ℕ) : p k∈K := by
    exact ⟨mem_univ _,by simpa only [mem_closedBall,dist_zero_right] using hz (X.subsequence k),
      by simpa only [mem_closedBall,dist_zero_right] using hv (X.subsequence k)⟩
  obtain ⟨a,ha,φ,hφ,hlim⟩ := hK.isSeqCompact.subseq_of_frequently_in (x := p) (Frequently.of_forall hp)
  let i : StandardChart := a.1
  let x : BaseCoordinates := a.2.1
  let w : FiberCoordinates := a.2.2
  let seq (k : ℕ) := X.subsequence (φ k)
  have hxlim : Tendsto (fun k ↦ z (seq k)) atTop (𝓝 x) :=
    ((continuous_fst.comp continuous_snd).tendsto a).comp hlim
  have hvlim : Tendsto (fun k ↦ v (seq k)) atTop (𝓝 w) :=
    ((continuous_snd.comp continuous_snd).tendsto a).comp hlim
  have hilim : ∀ᶠ k in atTop, chart (seq k)=i := by
    have hi : Tendsto (fun k ↦ chart (seq k)) atTop (𝓝 i) :=
      (continuous_fst.tendsto a).comp hlim
    exact hi.eventually ((isOpen_discrete {i}).mem_nhds (mem_singleton i))
  have hnorm : Tendsto (fun k ↦ (P (seq k)).value i (z (seq k),v (seq k))) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hilim] with k hk
    rw [← hk,hn]
  obtain ⟨y,hy⟩ := X.globalValue_nonzero_of_sequence i φ hφ
    (fun k ↦ z (seq k)) (fun k ↦ v (seq k)) x w hxlim hvlim ha.2.1
    (fun k t ↦ hP (seq k) i _ (hz (seq k)) t) hnorm
  exact ⟨i,y,w,hy⟩
end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

theorem no_unbounded_positive_metrics (ex : ℕ → ℕ) (hex : ∀ k, 0 < ex k)
    (hlim : Tendsto ex atTop atTop)
    (hmetric : ∀ k, ∃ h : SmoothHermitianMetric
      (powerPullbackTwist sourceGraphScalars.equalizerData.bundle (ex k) (hex k)),
      h.StrictlyGriffithsPositive) : False := by
  choose h hp using hmetric
  have hn (k : ℕ) := ((h k).tracedForm (hex k) (hp k)).exists_normalized
  choose P hP hN using hn
  obtain ⟨X⟩ := exists_extractedTrace hex P hP
  obtain ⟨i,z,v,hv⟩ := X.globalValue_nonzero hP hN
  exact hv ((X.pshDualForm hlim).source_value_zero i z v)

theorem source_eventually_no_positive_metric :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m (hm : 0 < m), m₀ ≤ m →
      ¬ ∃ h : SmoothHermitianMetric
        (powerPullbackTwist sourceGraphScalars.equalizerData.bundle m hm),
        h.StrictlyGriffithsPositive := by
  by_contra hh
  push Not at hh
  have hseq (k : ℕ) := hh (k+1) (by omega)
  choose ex hex hbound hm using hseq
  have hlim : Tendsto ex atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ ↦ k)
    · intro k; exact (Nat.le_succ k).trans (hbound k)
    · exact tendsto_id
  exact no_unbounded_positive_metrics ex hex hlim hm
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.PolynomialGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix
open scoped BigOperators
noncomputable section

namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u2} [Fintype ι] (B : PolynomialGeneration n ι)
lemma recover_matrix (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) :
    (B.recover i z).mulVec ((B.matrix i z).transpose.mulVec w)=w := B.leftInverse i z w
lemma matrix_injective (i : StandardChart) (z : BaseCoordinates) :
    Function.Injective ((B.matrix i z).transpose.mulVec) := by
  intro w w' h
  have he := congrArg (B.recover i z).mulVec h
  simpa only [B.recover_matrix] using he
lemma matrix_nonzero (i : StandardChart) (z : BaseCoordinates) {w : Fin (n+1) → ℂ} (hw : w≠0) :
    (B.matrix i z).transpose.mulVec w≠0 := by
  intro hh
  apply hw
  apply B.matrix_injective i z
  simpa only [mulVec_zero] using hh
end PolynomialGeneration
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.ProjectiveEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample.BinaryForms
open MvPolynomial Matrix
open scoped BigOperators
noncomputable section

lemma veronese_nonzero (n : ℕ) {v : Fin 2 → ℂ} (hv : v≠0) : veronese n v≠0 := by
  intro h
  have h0 := congrFun h (0 : Fin (n+1))
  have h1 := congrFun h (Fin.last n)
  simp only [veronese_zero,veronese_last,Pi.zero_apply] at h0 h1
  apply hv
  ext k
  fin_cases k
  · exact eq_zero_of_pow_eq_zero h1
  · exact eq_zero_of_pow_eq_zero h0

lemma veronese_ratio (n : ℕ) (hn : 0<n) (v : Fin 2 → ℂ) (h : v 1≠0) :
    veronese n v (veroneseOne n hn)/veronese n v 0=v 0/v 1 := by
  simp only [veronese,veroneseOne,Fin.val_zero,pow_zero,one_mul,Nat.sub_zero,pow_one]
  rw [show v 1^n=v 1^(n-1)*v 1 by rw [← pow_succ]; congr 1; omega]
  field_simp

lemma veronese_relations (n : ℕ) (hn : 0<n) (c : ℂ) (v : Fin 2 → ℂ) :
    VeroneseRelations n hn (c • veronese n v) := by
  constructor
  · intro k
    change (c*veronese n v k)^n=(c*veronese n v (Fin.last n))^k.val*(c*veronese n v 0)^(n-k.val)
    rw [veronese_zero,veronese_last]
    simp only [veronese,mul_pow]
    have hk : k.val+(n-k.val)=n := by omega
    calc
      _ = (c^k.val*c^(n-k.val))*((v 0^n)^k.val*(v 1^n)^(n-k.val)) := by
        rw [← pow_add,hk]
        simp only [← pow_mul,Nat.mul_comm]
      _ = _ := by ring
  · intro k
    change (c*veronese n v k.succ)*(c*veronese n v 0)=
      (c*veronese n v k.castSucc)*(c*veronese n v (veroneseOne n hn))
    rw [veronese_zero]
    simp only [veronese,veroneseOne,Fin.val_succ,Fin.val_castSucc,pow_one]
    have hk := k.isLt
    have ha : v 1^(n-k.val)=v 1^(n-(k.val+1))*v 1 := by
      rw [← pow_succ]; congr 1; omega
    have hb : v 1^n=v 1^(n-1)*v 1 := by
      rw [← pow_succ]; congr 1; omega
    rw [ha,hb,pow_succ]
    ring
lemma VeroneseRelations.reconstruct (n : ℕ) (hn : 0<n) (w : Fin (n+1) → ℂ)
    (hw : w≠0) (h : VeroneseRelations n hn w) :
    ∃ c : ℂ,c≠0 ∧ ∃ v : Fin 2 → ℂ,v≠0 ∧ w=c • veronese n v := by
  by_cases h0 : w 0=0
  · have hi (k : Fin (n+1)) (hk : k.val<n) : w k=0 := by
      have he := h.1 k
      rw [h0,zero_pow (by omega : n-k.val≠0),mul_zero] at he
      exact eq_zero_of_pow_eq_zero he
    have hn0 : w (Fin.last n)≠0 := by
      intro hz
      apply hw
      ext k
      by_cases hk : k.val=n
      · have he : k=Fin.last n := Fin.ext hk
        simpa only [he,Pi.zero_apply] using hz
      · exact hi k (by omega)
    refine ⟨w (Fin.last n),hn0,![1,0],by simp,?_⟩
    ext k
    by_cases hk : k.val=n
    · have he : k=Fin.last n := Fin.ext hk
      subst k
      simp [veronese]
    · have hkn : n-k.val≠0 := by omega
      simp [veronese,hi k (by omega),zero_pow hkn]
  · have hc (k : Fin (n+1)) : w k=w 0*(w (veroneseOne n hn)/w 0)^k.val := by
      induction k using Fin.inductionOn with
      | zero => simp
      | succ k ih =>
        have he := h.2 k
        rw [ih] at he
        apply mul_right_cancel₀ h0
        calc
          w k.succ*w 0 = w 0*(w (veroneseOne n hn)/w 0)^k.val*w (veroneseOne n hn) := he
          _ = (w 0*(w (veroneseOne n hn)/w 0)^k.succ.val)*w 0 := by
            simp only [Fin.val_succ,pow_succ]
            field_simp
    refine ⟨w 0,h0,![w (veroneseOne n hn)/w 0,1],by simp,?_⟩
    ext k
    simpa [veronese] using hc k

lemma veronese_endpoint (n : ℕ) (v : Fin 2 → ℂ) (b : Fin 2) :
    veronese n v (veroneseEndpoint n b)=v b^n := by
  fin_cases b <;> simp [veroneseEndpoint]
lemma veronese_adjacent_ratio (n : ℕ) (hn : 0<n) (v : Fin 2 → ℂ) (b : Fin 2)
    (hb : v b≠0) :
    veronese n v (veroneseAdjacent n hn b)/veronese n v (veroneseEndpoint n b)=v (1-b)/v b := by
  fin_cases b
  · change veronese n v (veroneseAdjacent n hn 0)/veronese n v (veroneseEndpoint n 0)=v 1/v 0
    simp only [veroneseAdjacent,veroneseEndpoint,ite_true,veronese_last]
    simp only [veronese]
    rw [show n-(n-1)=1 by omega,pow_one]
    rw [show v 0^n=v 0^(n-1)*v 0 by rw [← pow_succ]; congr 1; omega]
    change v 0≠0 at hb
    field_simp [hb]
  · change veronese n v (veroneseAdjacent n hn 1)/veronese n v (veroneseEndpoint n 1)=v 0/v 1
    simpa only [veroneseAdjacent,veroneseEndpoint,show (1 : Fin 2)≠0 by decide,
      ite_false] using veronese_ratio n hn v hb
lemma binary_proportional_of_ratio (v w : Fin 2 → ℂ) (b : Fin 2) (hv : v b≠0) (hw : w b≠0)
    (h : v (1-b)/v b=w (1-b)/w b) : ∃ c : ℂ,c≠0 ∧ v=c • w := by
  refine ⟨v b/w b,div_ne_zero hv hw,?_⟩
  ext k
  by_cases hk : k=b
  · subst k; simp [Pi.smul_apply,smul_eq_mul,hw]
  · have he : k=1-b := by fin_cases k <;> fin_cases b <;> simp_all
    subst k
    have hh := (div_eq_div_iff hv hw).mp h
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = (w (1-b)*v b)/w b := (eq_div_iff hw).mpr hh
      _ = _ := by ring
lemma veronese_projective_injective (n : ℕ) (hn : 0<n) (v w : Fin 2 → ℂ)
    (hw : w≠0) (c : ℂ) (hc : c≠0) (h : veronese n v=c • veronese n w) :
    ∃ d : ℂ,d≠0 ∧ v=d • w := by
  obtain ⟨b,hb⟩ : ∃ b,w b≠0 := by
    by_contra hh
    apply hw
    ext b
    by_contra hbb
    exact hh ⟨b,hbb⟩
  have he := congrFun h (veroneseEndpoint n b)
  simp only [Pi.smul_apply,smul_eq_mul,veronese_endpoint] at he
  have hv : v b≠0 := by
    intro hz
    rw [hz,zero_pow (by omega)] at he
    exact (mul_ne_zero hc (pow_ne_zero _ hb)) he.symm
  apply binary_proportional_of_ratio v w b hv hb
  rw [← veronese_adjacent_ratio n hn v b hv,← veronese_adjacent_ratio n hn w b hb]
  rw [h]
  simp only [Pi.smul_apply,smul_eq_mul,mul_div_mul_left _ _ hc]

end
end QuadricCounterexample.BinaryForms

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section

lemma segreFactor_ne_zero_iff (a i : StandardChart) (z : BaseCoordinates) :
    segreFactor a i z≠0 ↔ z∈coordinateOverlap i a := by
  rw [coordinateOverlap_iff]
  simp only [segreFactor,eval_lineGenerator,lineFactor,firstFactor,secondFactor,scalarFactor,pow_one]
  rw [mul_ne_zero_iff]
  constructor
  · rintro ⟨h₁,h₂⟩
    constructor
    · by_cases h : i.1=a.1
      · exact Or.inl h
      · exact Or.inr (by simpa only [ite_eq_right h] using h₁)
    · by_cases h : i.2=a.2
      · exact Or.inl h
      · exact Or.inr (by simpa only [ite_eq_right h] using h₂)
  · rintro ⟨h₁,h₂⟩
    constructor
    · rcases h₁ with h₁|h₁
      · simp [h₁]
      · split_ifs <;> simp_all
    · rcases h₂ with h₂|h₂
      · simp [h₂]
      · split_ifs <;> simp_all

namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u1} [Fintype ι] (B : PolynomialGeneration n ι)
lemma stencil_smul (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (c : ℂ) :
    B.stencil i z (c • w)=c • B.stencil i z w := by
  ext j
  simp only [stencil,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
  ring
lemma stencil_nonzero (i : StandardChart) (z : BaseCoordinates) {w : Fin (n+1) → ℂ} (hw : w≠0) :
    B.stencil i z w≠0 := by
  intro hh
  apply B.matrix_nonzero i z hw
  ext q
  simpa only [stencil_self,Pi.zero_apply] using congrFun hh (index (i,q))
lemma value_nonzero (i : StandardChart) (z : BaseCoordinates) {v : FiberCoordinates} (hv : v≠0) :
    B.value i z v≠0 := B.stencil_nonzero i z (veronese_nonzero n hv)

lemma normalize_smul (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) (c : ℂ) (hc : c≠0) :
    normalize j (c • y)=normalize j y := by
  ext k
  simp only [normalize,Pi.smul_apply,smul_eq_mul,mul_div_mul_left _ _ hc]
lemma normalize_pivot (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) (hy : y j≠0) :
    normalize j y j=1 := div_self hy

lemma patchCoordinates_stencil (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι)
    (hq : B.stencil i z w (index (i,q))≠0) :
    patchCoordinates i q (normalize (index (i,q)) (B.stencil i z w))=z := by
  have hq' : ((B.matrix i z).transpose.mulVec w) q≠0 := by simpa only [stencil_self] using hq
  simp only [patchCoordinates,normalize,stencil_index,segreFactor_self,one_mul,
    segreFactor_flipFirst,segreFactor_flipSecond,mul_div_cancel_right₀ _ hq']
lemma patchRecovery_stencil (i : StandardChart) (z : BaseCoordinates) (w : Fin (n+1) → ℂ) (q : ι)
    (hq : B.stencil i z w (index (i,q))≠0) :
    B.patchRecovery i q (normalize (index (i,q)) (B.stencil i z w))=
      (B.stencil i z w (index (i,q)))⁻¹ • w := by
  unfold patchRecovery
  rw [B.patchCoordinates_stencil i z w q hq]
  have hb : block i (normalize (index (i,q)) (B.stencil i z w))=
      (B.stencil i z w (index (i,q)))⁻¹ • (B.matrix i z).transpose.mulVec w := by
    ext r
    simp only [block,normalize,stencil_self,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [hb,Matrix.mulVec_smul,B.recover_matrix]
end PolynomialGeneration
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial
open scoped BigOperators
noncomputable section

lemma exists_homogenizeAt {N : ℕ} (j : Fin N) (p : MvPolynomial (Fin N) ℂ) :
    ∃ d : ℕ,∃ h : MvPolynomial (Fin N) ℂ,h.IsHomogeneous d ∧
      ∀ y : Fin N → ℂ,y j≠0 → MvPolynomial.eval y h=(y j)^d*MvPolynomial.eval (fun k ↦ y k/y j) p := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0,C c,isHomogeneous_C _ _,fun _ _ ↦ by simp⟩
  | add p q hp hq =>
    obtain ⟨d,h,hh,he⟩ := hp
    obtain ⟨e,k,hk,ke⟩ := hq
    refine ⟨d+e,X j^e*h+X j^d*k,?_,?_⟩
    · apply IsHomogeneous.add
      · simpa only [add_comm] using (isHomogeneous_X_pow j e).mul hh
      · exact (isHomogeneous_X_pow j d).mul hk
    · intro y hy
      rw [map_add,map_add,map_mul,map_mul,map_pow,map_pow,eval_X,he y hy,ke y hy,pow_add]
      ring
  | mul_X p k hp =>
    obtain ⟨d,h,hh,he⟩ := hp
    refine ⟨d+1,h*X k,hh.mul (isHomogeneous_X ℂ k),?_⟩
    intro y hy
    rw [map_mul,map_mul,eval_X,eval_X,he y hy,pow_succ]
    field_simp

lemma projectiveCone_of_patch_equations {N : ℕ} (C : Set (Fin N → ℂ)) (hzero : 0∈C)
    (E : Fin N → Set (MvPolynomial (Fin N) ℂ))
    (hE : ∀ j y,y j≠0 → (y∈C ↔ ∀ p∈E j,MvPolynomial.eval (fun k ↦ y k/y j) p=0)) :
    ProjectiveAlgebraicCone C := by
  choose degree hom homogeneous evaluate using fun j p ↦ exists_homogenizeAt (N:=N) j p
  let equations : Set (MvPolynomial (Fin N) ℂ) :=
    {q | ∃ j p,p∈E j ∧ q=X j*hom j p}
  refine ⟨equations,?_,?_⟩
  · rintro q ⟨j,p,_,rfl⟩
    exact ⟨1+degree j p,(isHomogeneous_X ℂ j).mul (homogeneous j p)⟩
  · ext y
    constructor
    · intro hy q hq
      obtain ⟨j,p,hp,rfl⟩ := hq
      rw [map_mul,eval_X]
      by_cases hj : y j=0
      · rw [hj,zero_mul]
      · rw [evaluate j p y hj,(hE j y hj).mp hy p hp,mul_zero,mul_zero]
    · intro hy
      by_cases hz : y=0
      · simpa only [hz] using hzero
      · obtain ⟨j,hj⟩ : ∃ j,y j≠0 := by
          by_contra hn
          apply hz
          ext j
          by_contra hh
          exact hn ⟨j,hh⟩
        apply (hE j y hj).mpr
        intro p hp
        have h := hy (X j*hom j p) ⟨j,p,hp,rfl⟩
        rw [map_mul,eval_X,evaluate j p y hj] at h
        exact (mul_eq_zero.mp h).resolve_left hj |> fun h ↦ (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hj)
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms
open scoped BigOperators
noncomputable section
namespace PolynomialGeneration
variable {n : ℕ} {ι : Type u3} [Fintype ι] (B : PolynomialGeneration n ι)

lemma normalize_eq_smul (j : ProjectiveIndex ι) (y : ProjectiveIndex ι → ℂ) :
    normalize j y=(y j)⁻¹ • y := by
  ext k
  simp [normalize,div_eq_mul_inv,mul_comm]
lemma stencil_zero (i : StandardChart) (z : BaseCoordinates) : B.stencil i z 0=0 := by
  ext j
  simp [stencil]

lemma eval_liftPatchPolynomial (i : StandardChart) (q : ι) (p : BasePolynomial) (y : ProjectiveIndex ι → ℂ) :
    MvPolynomial.eval y (liftPatchPolynomial i q p)=baseEval p (patchCoordinates i q y) := by
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) _ ((MvPolynomial.bind₁ _) p)=_
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval _ p=MvPolynomial.eval _ p
  apply congrArg (fun f : Fin 2 → ℂ ↦ MvPolynomial.eval f p)
  funext k
  fin_cases k <;> simp [patchCoordinates]

lemma eval_recoveryPolynomial (i : StandardChart) (q : ι) (k : Fin (n+1)) (y : ProjectiveIndex ι → ℂ) :
    MvPolynomial.eval y (B.recoveryPolynomial i q k)=B.patchRecovery i q y k := by
  simp only [recoveryPolynomial,map_sum,map_mul,eval_X,eval_liftPatchPolynomial]
  rfl

lemma patchEquations_iff (hn : 0<n) (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ) :
    (∀ p∈B.patchEquations hn i q,MvPolynomial.eval y p=0) ↔
      y=B.stencil i (patchCoordinates i q y) (B.patchRecovery i q y) ∧
      VeroneseRelations n hn (B.patchRecovery i q y) := by
  simp only [patchEquations,Set.mem_union,or_imp,forall_and,Set.forall_mem_range,map_sub,map_mul,
    map_sum,map_pow,eval_X,eval_liftPatchPolynomial,eval_recoveryPolynomial,sub_eq_zero]
  change ((∀ j,y j=B.stencil i (patchCoordinates i q y) (B.patchRecovery i q y) j) ∧
    (∀ k,(B.patchRecovery i q y k)^n=(B.patchRecovery i q y (Fin.last n))^k.val*
      (B.patchRecovery i q y 0)^(n-k.val))) ∧
    (∀ k : Fin n,B.patchRecovery i q y k.succ*B.patchRecovery i q y 0=
      B.patchRecovery i q y k.castSucc*B.patchRecovery i q y (veroneseOne n hn)) ↔ _
  rw [← funext_iff]
  exact and_assoc
lemma normalized_value_equations (hn : 0<n) (i : StandardChart) (q : ι) (z : BaseCoordinates)
    (v : FiberCoordinates) (h : B.value i z v (index (i,q))≠0) :
    ∀ p∈B.patchEquations hn i q,MvPolynomial.eval (normalize (index (i,q)) (B.value i z v)) p=0 := by
  rw [B.patchEquations_iff]
  simp only [value]
  rw [B.patchCoordinates_stencil i z _ q h,B.patchRecovery_stencil i z _ q h]
  constructor
  · rw [B.stencil_smul,normalize_eq_smul]
  · exact veronese_relations n hn _ v
lemma patchEquations_reconstruct (hn : 0<n) (i : StandardChart) (q : ι) (y : ProjectiveIndex ι → ℂ)
    (hy : y (index (i,q))=1) (h : ∀ p∈B.patchEquations hn i q,MvPolynomial.eval y p=0) :
    ∃ z : BaseCoordinates,∃ v : FiberCoordinates,v≠0 ∧ ∃ c : ℂ,c≠0 ∧ y=c • B.value i z v := by
  obtain ⟨he,hv⟩ := (B.patchEquations_iff hn i q y).mp h
  have hw : B.patchRecovery i q y≠0 := by
    intro hz
    rw [hz,B.stencil_zero] at he
    have hj := congrFun he (index (i,q))
    rw [hy] at hj
    exact one_ne_zero hj
  obtain ⟨c,hc,v,hv',hw'⟩ := hv.reconstruct n hn _ hw
  refine ⟨patchCoordinates i q y,v,hv',c,hc,?_⟩
  calc
    y = B.stencil i (patchCoordinates i q y) (B.patchRecovery i q y) := he
    _ = c • B.value i (patchCoordinates i q y) v := by rw [hw',B.stencil_smul]; rfl

theorem algebraicCone_of_localization (hn : 0<n) (C : Set (ProjectiveIndex ι → ℂ))
    (hzero : 0∈C)
    (himage : ∀ i z v,v≠0 → ∀ c : ℂ,c≠0 → c • B.value i z v∈C)
    (hlocal : ∀ j y,y∈C → y j≠0 → ∃ z : BaseCoordinates,∃ v : FiberCoordinates,v≠0 ∧
      ∃ c : ℂ,c≠0 ∧ y=c • B.value (label j).1 z v) :
    ProjectiveAlgebraicCone C := by
  apply projectiveCone_of_patch_equations C hzero (fun j ↦ B.patchEquations hn (label j).1 (label j).2)
  intro j y hy
  have hj : index ((label j).1,(label j).2)=j := index_label j
  constructor
  · intro hC
    obtain ⟨z,v,_,c,hc,rfl⟩ := hlocal j y hC hy
    have hv : B.value (label j).1 z v j≠0 := by
      exact (mul_ne_zero_iff.mp hy).2
    rw [show (fun k ↦ (c • B.value (label j).1 z v) k/(c • B.value (label j).1 z v) j)=
      normalize j (c • B.value (label j).1 z v) from rfl,normalize_smul j _ c hc]
    simpa only [hj] using B.normalized_value_equations hn (label j).1 (label j).2 z v (by rw [hj]; exact hv)
  · intro h
    obtain ⟨z,v,hv,c,hc,he⟩ := B.patchEquations_reconstruct hn (label j).1 (label j).2
      (normalize j y) (by rw [hj]; exact normalize_pivot j y hy) h
    have hey : y=(y j*c) • B.value (label j).1 z v := by
      rw [normalize_eq_smul] at he
      have hh := congrArg (fun a : ProjectiveIndex ι → ℂ ↦ y j • a) he
      simpa only [smul_smul,mul_inv_cancel₀ hy,one_smul] using hh
    rw [hey]
    exact himage _ _ _ hv _ (mul_ne_zero hy hc)
end PolynomialGeneration
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Embedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section

namespace AlgebraicRankTwoBundle
variable (V : AlgebraicRankTwoBundle)
lemma dualTransition_self (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) :
    V.dualTransition i i x=1 := by
  unfold dualTransition
  rw [V.transition_self i x hx,Matrix.transpose_one]
lemma dualTransition_mul (i j k : ℕ) (x : QuadricSurface)
    (hi : x∈V.domain i) (hj : x∈V.domain j) (hk : x∈V.domain k) :
    V.dualTransition i j x*V.dualTransition j k x=V.dualTransition i k x := by
  unfold dualTransition
  rw [← Matrix.transpose_mul,V.transition_mul k j i x hk hj hi]
lemma dualTransition_nonzero (i j : ℕ) (x : QuadricSurface)
    (hi : x∈V.domain i) (hj : x∈V.domain j) {v : FiberCoordinates} (hv : v≠0) :
    (V.dualTransition i j x).mulVec v≠0 := by
  intro hz
  have hh := congrArg (V.dualTransition j i x).mulVec hz
  rw [Matrix.mulVec_mulVec,V.dualTransition_mul j i j x hj hi hj,V.dualTransition_self j x hj,
    Matrix.one_mulVec,Matrix.mulVec_zero] at hh
  exact hv hh
end AlgebraicRankTwoBundle
lemma sectionVector_compatible {V : AlgebraicRankTwoBundle} {n N : ℕ}
    (s : Fin N → SymmetricSection V n) (i j : ℕ) (x : QuadricSurface)
    (hi : x∈V.domain i) (hj : x∈V.domain j) (v : FiberCoordinates) :
    sectionVector s i x ((V.dualTransition i j x).mulVec v)=sectionVector s j x v := by
  ext a
  exact (s a).compatible i j x hi hj v

namespace StandardBundleCover
variable {V : AlgebraicRankTwoBundle} (H : StandardBundleCover V)
lemma chartIndex_lt (a : StandardChart) : H.chartIndex a<4 := (H.surj a).choose_spec.1
lemma chartIndex_chart (a : StandardChart) : V.chart (H.chartIndex a)=a := (H.surj a).choose_spec.2
lemma chartIndex_mem (a : StandardChart) (z : BaseCoordinates) : affineQuadric a z∈V.domain (H.chartIndex a) := by
  rw [H.domain,H.chartIndex_chart]
  exact ⟨H.chartIndex_lt a,⟨z,rfl⟩⟩
end StandardBundleCover

namespace SegreSectionSystem
variable {V : AlgebraicRankTwoBundle} {n : ℕ} {ι : Type u2} [Fintype ι] (S : SegreSectionSystem V n ι)
lemma nonzero (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) {v : FiberCoordinates} (hv : v≠0) :
    sectionVector S.sections i x v≠0 := by
  rw [S.value_eq i x hx]
  exact S.generation.value_nonzero _ _ hv
lemma pivot_domain (i : ℕ) (hi : i<4) (j : ℕ) (x : QuadricSurface) (hx : x∈V.domain j)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections j x v (index (V.chart i,q))≠0) :
    x∈V.domain i := by
  rw [S.value_eq j x hx] at hq
  change S.generation.stencil (V.chart j) (coordQuadric (V.chart j) x) (veronese n v) _≠0 at hq
  rw [S.generation.stencil_index] at hq
  have ho := (segreFactor_ne_zero_iff (V.chart i) (V.chart j) (coordQuadric (V.chart j) x)).mp
    (mul_ne_zero_iff.mp hq).1
  rw [S.cover.domain]
  refine ⟨hi,?_⟩
  rw [← affineQuadric_mem_range] at ho
  simpa only [affineQuadric_coord ((S.cover.domain j x).mp hx).2] using ho
lemma localize_pivot (j : ProjectiveIndex ι) (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (hv : v≠0) (hj : sectionVector S.sections i x v j≠0) :
    ∃ z : BaseCoordinates,∃ w : FiberCoordinates,w≠0 ∧
      sectionVector S.sections i x v=S.generation.value (label j).1 z w := by
  let a := (label j).1
  let k := S.cover.chartIndex a
  have hk : x∈V.domain k := by
    apply S.pivot_domain k (S.cover.chartIndex_lt a) i x hx v (label j).2
    simpa only [k,S.cover.chartIndex_chart,a,Prod.eta,index_label] using hj
  refine ⟨coordQuadric a x,(V.dualTransition k i x).mulVec v,
    V.dualTransition_nonzero k i x hk hx hv,?_⟩
  rw [← sectionVector_compatible S.sections k i x hk hx v,S.value_eq k x hk]
  simp only [k,S.cover.chartIndex_chart,a]

lemma pivot_coordinates (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) (v : FiberCoordinates)
    (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0) :
    patchCoordinates (V.chart i) q (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))=
      coordQuadric (V.chart i) x := by
  rw [S.value_eq i x hx] at hq ⊢
  exact S.generation.patchCoordinates_stencil _ _ _ _ hq
lemma pivot_recovery (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) (v : FiberCoordinates)
    (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0) :
    S.generation.patchRecovery (V.chart i) q (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))=
      (sectionVector S.sections i x v (index (V.chart i,q)))⁻¹ • veronese n v := by
  rw [S.value_eq i x hx] at hq ⊢
  exact S.generation.patchRecovery_stencil _ _ _ _ hq
lemma exists_pivot (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i) (v : FiberCoordinates) (hv : v≠0) :
    ∃ q : ι,sectionVector S.sections i x v (index (V.chart i,q))≠0 := by
  have hn := S.generation.matrix_nonzero (V.chart i) (coordQuadric (V.chart i) x) (veronese_nonzero n hv)
  by_contra hh
  apply hn
  ext q
  have he : sectionVector S.sections i x v (index (V.chart i,q))=0 := by
    by_contra he; exact hh ⟨q,he⟩
  rw [S.value_eq i x hx] at he
  simpa only [PolynomialGeneration.value,S.generation.stencil_self,Pi.zero_apply] using he

lemma injective (hn : 0<n) (i j : ℕ) (x y : QuadricSurface) (hx : x∈V.domain i) (hy : y∈V.domain j)
    (v w : FiberCoordinates) (hv : v≠0) (hw : w≠0) (c : ℂ) (hc : c≠0)
    (h : sectionVector S.sections i x v=c • sectionVector S.sections j y w) :
    x=y ∧ ∃ d : ℂ,d≠0 ∧ v=d • ((V.dualTransition i j x).mulVec w) := by
  obtain ⟨q,hq⟩ := S.exists_pivot i x hx v hv
  have hqy : sectionVector S.sections j y w (index (V.chart i,q))≠0 := by
    rw [h] at hq
    exact (mul_ne_zero_iff.mp hq).2
  have hyi := S.pivot_domain i ((S.cover.domain i x).mp hx).1 j y hy w q hqy
  let w' := (V.dualTransition i j y).mulVec w
  have hw' : w'≠0 := V.dualTransition_nonzero i j y hyi hy hw
  have hchange : sectionVector S.sections i y w'=sectionVector S.sections j y w :=
    sectionVector_compatible S.sections i j y hyi hy w
  have hpq : sectionVector S.sections i y w' (index (V.chart i,q))≠0 := by rwa [hchange]
  have hnorm : normalize (index (V.chart i,q)) (sectionVector S.sections i x v)=
      normalize (index (V.chart i,q)) (sectionVector S.sections i y w') := by
    rw [h,normalize_smul _ _ c hc,hchange]
  have hz := congrArg (patchCoordinates (V.chart i) q) hnorm
  rw [S.pivot_coordinates i x hx v q hq,S.pivot_coordinates i y hyi w' q hpq] at hz
  have hxy : x=y := by
    have he := congrArg (affineQuadric (V.chart i)) hz
    simpa only [affineQuadric_coord ((S.cover.domain i x).mp hx).2,
      affineQuadric_coord ((S.cover.domain i y).mp hyi).2] using he
  refine ⟨hxy,?_⟩
  subst y
  have hlocal : sectionVector S.sections i x v=c • sectionVector S.sections i x w' := by rwa [hchange]
  have hblock := congrArg (block (V.chart i)) hlocal
  rw [S.value_eq i x hx,S.value_eq i x hx] at hblock
  have he : (S.generation.matrix (V.chart i) (coordQuadric (V.chart i) x)).transpose.mulVec (veronese n v)=
      c • (S.generation.matrix (V.chart i) (coordQuadric (V.chart i) x)).transpose.mulVec (veronese n w') := by
    ext r
    simpa only [block,PolynomialGeneration.value,Pi.smul_apply,S.generation.stencil_self] using congrFun hblock r
  have hre := congrArg (S.generation.recover (V.chart i) (coordQuadric (V.chart i) x)).mulVec he
  rw [Matrix.mulVec_smul,S.generation.recover_matrix,S.generation.recover_matrix] at hre
  exact veronese_projective_injective n hn v w' hw' c hc hre
end SegreSectionSystem
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set MvPolynomial Matrix LaurentCech BinaryForms PolynomialGeneration
open scoped BigOperators
noncomputable section
namespace SegreSectionSystem
variable {V : AlgebraicRankTwoBundle} {n : ℕ} {ι : Type u3} [Fintype ι] (S : SegreSectionSystem V n ι)

lemma cone_algebraic (hn : 0<n) :
    ProjectiveAlgebraicCone ({0} ∪ {y | ∃ i x,x∈V.domain i ∧ ∃ v : FiberCoordinates,v≠0 ∧
      ∃ c : ℂ,c≠0 ∧ y=c • sectionVector S.sections i x v}) := by
  apply S.generation.algebraicCone_of_localization hn _ (Or.inl rfl)
  · intro a z v hv c hc
    let i := S.cover.chartIndex a
    have hx := S.cover.chartIndex_mem a z
    refine Or.inr ⟨i,affineQuadric a z,hx,v,hv,c,hc,?_⟩
    rw [S.value_eq i _ hx]
    simp only [i,S.cover.chartIndex_chart,coordQuadric_affine]
  · intro j y hy hj
    rcases hy with hy|⟨i,x,hx,v,hv,c,hc,rfl⟩
    · exact (hj (congrFun hy j)).elim
    · have hs : sectionVector S.sections i x v j≠0 := (mul_ne_zero_iff.mp hj).2
      obtain ⟨z,w,hw,he⟩ := S.localize_pivot j i x hx v hv hs
      exact ⟨z,w,hw,c,hc,congrArg (c • ·) he⟩

lemma recoveryPolynomial_value (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (k : Fin (n+1)) :
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.generation.recoveryPolynomial (V.chart i) q k)=
      (sectionVector S.sections i x v (index (V.chart i,q)))⁻¹*veronese n v k := by
  rw [S.generation.eval_recoveryPolynomial,S.pivot_recovery i x hx v q hq]
  rfl
lemma inverseDenominator_value (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (b : Fin 2) :
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseDenominator i q b 2)=
      (sectionVector S.sections i x v (index (V.chart i,q)))⁻¹*(v b)^n := by
  change MvPolynomial.eval _ (S.generation.recoveryPolynomial (V.chart i) q (veroneseEndpoint n b))=_
  rw [S.recoveryPolynomial_value i x hx v q hq,veronese_endpoint]
lemma inverseDenominator_nonzero (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (b : Fin 2) (hb : v b≠0) (k : Fin 3) :
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseDenominator i q b k)≠0 := by
  fin_cases k
  · simp [inverseDenominator]
  · simp [inverseDenominator]
  · change MvPolynomial.eval _ (S.inverseDenominator i q b 2)≠0
    rw [S.inverseDenominator_value i x hx v q hq b]
    exact mul_ne_zero (inv_ne_zero hq) (pow_ne_zero _ hb)
lemma inverseFormula (hn : 0<n) (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (q : ι) (hq : sectionVector S.sections i x v (index (V.chart i,q))≠0)
    (b : Fin 2) (hb : v b≠0) (k : Fin 3) :
    (![ (coordQuadric (V.chart i) x).1,(coordQuadric (V.chart i) x).2,v (1-b)/v b] : Fin 3 → ℂ) k=
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseNumerator hn i q b k)/
    MvPolynomial.eval (normalize (index (V.chart i,q)) (sectionVector S.sections i x v))
      (S.inverseDenominator i q b k) := by
  have hz := S.pivot_coordinates i x hx v q hq
  fin_cases k
  · change (coordQuadric (V.chart i) x).1= MvPolynomial.eval _ (X (index (flipFirst (V.chart i),q))) / MvPolynomial.eval _ 1
    simpa only [eval_X,map_one,div_one,patchCoordinates] using (congrArg Prod.fst hz).symm
  · change (coordQuadric (V.chart i) x).2= MvPolynomial.eval _ (X (index (flipSecond (V.chart i),q))) / MvPolynomial.eval _ 1
    simpa only [eval_X,map_one,div_one,patchCoordinates] using (congrArg Prod.snd hz).symm
  · change v (1-b)/v b=MvPolynomial.eval _ (S.generation.recoveryPolynomial (V.chart i) q (veroneseAdjacent n hn b)) /
      MvPolynomial.eval _ (S.generation.recoveryPolynomial (V.chart i) q (veroneseEndpoint n b))
    rw [S.recoveryPolynomial_value i x hx v q hq,S.recoveryPolynomial_value i x hx v q hq,
      mul_div_mul_left _ _ (inv_ne_zero hq),veronese_adjacent_ratio n hn v b hb]

lemma local_inverse (hn : 0<n) (i : ℕ) (x : QuadricSurface) (hx : x∈V.domain i)
    (v : FiberCoordinates) (hv : v≠0) :
    ∃ j : ProjectiveIndex ι,∃ b : Fin 2,v b≠0 ∧ sectionVector S.sections i x v j≠0 ∧
    ∃ p q : Fin 3 → MvPolynomial (ProjectiveIndex ι) ℂ,
      (∀ k,MvPolynomial.eval (normalize j (sectionVector S.sections i x v)) (q k)≠0) ∧
      ∀ i' x',x'∈V.domain i' → ∀ v' : FiberCoordinates,v'≠0 →
        sectionVector S.sections i' x' v' j≠0 →
        (∀ k,MvPolynomial.eval (normalize j (sectionVector S.sections i' x' v')) (q k)≠0) →
        x'∈V.domain i ∧ ((V.dualTransition i i' x').mulVec v') b≠0 ∧
        (∀ k : Fin 3,
          (![ (coordQuadric (V.chart i) x').1,(coordQuadric (V.chart i) x').2,
            ((V.dualTransition i i' x').mulVec v') (1-b)/((V.dualTransition i i' x').mulVec v') b] : Fin 3 → ℂ) k=
          MvPolynomial.eval (normalize j (sectionVector S.sections i' x' v')) (p k)/
          MvPolynomial.eval (normalize j (sectionVector S.sections i' x' v')) (q k)) := by
  obtain ⟨r,hr⟩ := S.exists_pivot i x hx v hv
  obtain ⟨b,hb⟩ : ∃ b,v b≠0 := by
    by_contra hh
    apply hv
    ext b
    by_contra hh'
    exact hh ⟨b,hh'⟩
  refine ⟨index (V.chart i,r),b,hb,hr,S.inverseNumerator hn i r b,S.inverseDenominator i r b,
    S.inverseDenominator_nonzero i x hx v r hr b hb,?_⟩
  intro i' x' hx' v' _ hj hden
  have hxi := S.pivot_domain i ((S.cover.domain i x).mp hx).1 i' x' hx' v' r hj
  let w := (V.dualTransition i i' x').mulVec v'
  have hchange : sectionVector S.sections i x' w=sectionVector S.sections i' x' v' :=
    sectionVector_compatible S.sections i i' x' hxi hx' v'
  have hp : sectionVector S.sections i x' w (index (V.chart i,r))≠0 := by rwa [hchange]
  have h2 := hden 2
  rw [← hchange,S.inverseDenominator_value i x' hxi w r hp b] at h2
  have hwb : w b≠0 := by
    intro hz
    exact ((mul_ne_zero_iff.mp h2).2) (by rw [hz,zero_pow (by omega : n≠0)])
  refine ⟨hxi,hwb,fun k ↦ ?_⟩
  rw [← hchange]
  exact S.inverseFormula hn i x' hxi w r hp b hwb k

theorem closedEmbedding (hn : 0<n) : GivesClosedProjectiveEmbedding S.sections := by
  refine ⟨fun i x hi v hv ↦ S.nonzero i x hi hv,?_,S.cone_algebraic hn,?_⟩
  · intro i j x y hx hy v w hv hw h
    obtain ⟨c,hc,he⟩ := h
    exact S.injective hn i j x y hx hy v w hv hw c hc he
  · exact S.local_inverse hn
end SegreSectionSystem
end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Ampleness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
noncomputable section

theorem EqualizerData.powerTwist_ample (D : EqualizerData) (m : ℕ) (hm : 0 < m) :
    IsAmple (powerPullbackTwist D.bundle m hm) := by
  let t := 3*m+1
  let e := 2*t-1
  have he : 3*m≤e := by dsimp [e,t]; omega
  have hen : e+1=2*t := by dsimp [e,t]; omega
  have hn : 0<2*t := by dsimp [t]; omega
  let S := D.ampleSystem m hm e t he hen
  exact ⟨2*t,hn,_,S.sections,S.closedEmbedding hn⟩

end
end QuadricCounterexample

end

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace QuadricCounterexample
noncomputable section

theorem main_theorem_oai : SourceMainTheorem := by
  let G := sourceGraphScalars.equalizerData.bundle
  let E : ℕ → AlgebraicRankTwoBundle := fun m ↦
    if hm : 0 < m then powerPullbackTwist G m hm else G
  refine ⟨G,E,?_,?_,?_⟩
  · intro m hm
    dsimp [E]
    rw [dite_eq_left hm]
    exact powerPullbackTwist_spec G m hm
  · intro m hm
    dsimp [E]
    rw [dite_eq_left hm]
    exact sourceGraphScalars.equalizerData.powerTwist_ample m hm
  · obtain ⟨m₀,h₀,h⟩ := source_eventually_no_positive_metric
    refine ⟨m₀,h₀,fun m hmi ↦ ?_⟩
    have hm : 0 < m := h₀.trans_le hmi
    dsimp [E]
    rw [dite_eq_left hm]
    exact h m hm hmi

end
end QuadricCounterexample

end

end OAI
end

theorem solution : type_of% @OAI.QuadricCounterexample.main_theorem_oai := @OAI.QuadricCounterexample.main_theorem_oai
