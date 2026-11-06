-- Prove2me | solution 1 for OAI.Falconer.linear_projection_gain
-- status  : ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-05T21:51:04.777588+00:00
-- url     : https://prove2.me/submissions/a21670de-d891-45a6-a668-827dd278e387

import Theorems.Thm_OAI_Falconer_controlled_dyadic_angular_gain
import Theorems.Thm_OAI_Falconer_controlled_endpoint_angular_gain
import Theorems.Thm_OAI_Falconer_endpoint_spherical_preparation
import Theorems.Thm_OAI_Falconer_publishedPlanarFurstenberg_proved




open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology

namespace OAI.Falconer.LinearProjectionGainPartial

abbrev Point (k : ℕ) := EuclideanSpace ℝ (Fin (k + 1))
abbrev Direction (k : ℕ) := Metric.sphere (0 : Point k) 1

/-- The hypotheses on the two laws, without any normalization of their mass. -/
def Laws (k : ℕ) (q t R ζ ε δ : ℝ)
    (μ : Measure (Point k)) (ν : Measure (Direction k)) : Prop :=
  μ univ ≤ 1 ∧ ν univ ≤ 1 ∧ (∀ᵐ x ∂μ, ‖x‖ ≤ R) ∧
  (∀ x : Point k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    μ (Metric.ball x r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ t)) ∧
  (∀ w : Direction k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ν (Metric.ball w r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ q)) ∧
  (q = (k : ℝ) - 1 → ∀ H : Submodule ℝ (Point k), Module.finrank ℝ H = k →
    ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ν {w | Metric.infDist (w : Point k) (H : Set _) ≤ r}
      ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ ζ))

/-- Each fiber has its own finite list of affine lines. -/
def FiberCover (k : ℕ) (q C ε δ : ℝ) (E : Set (Point k × Direction k)) : Prop :=
  ∀ w : Direction k, ∃ A : Finset (Point k), (A.card : ℝ) ≤ δ ^ (-q - ε) ∧
    ∀ x : Point k, (x, w) ∈ E → ∃ a ∈ A,
      ‖(ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto (x - a)‖ ≤ C * δ

/-- A raw-measure estimate on one small cap. The cap radius and all budgets must
be chosen before the laws, incidence relation, and cap center. This is the
remaining bridge, rather than a theorem assumed or added to the environment. -/
def SmallCapGain (k : ℕ) (q t C R ζ : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (μ : Measure (Point k)) (ν : Measure (Direction k)),
    Laws k q t R ζ ε δ μ ν → ∀ (w₀ : Direction k) (E : Set (Point k × Direction k)),
    NullMeasurableSet E (μ.prod ν) → FiberCover k q C ε δ E →
    (∀ u ∈ E, dist u.2 w₀ ≤ ρ) → (μ.prod ν) E ≤ ENNReal.ofReal (δ ^ c)

/-- Precise missing bridge lemma type, including both slicing regimes. -/
def SmallCapBridge : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ q t : ℝ,
    (k : ℝ) - 1 ≤ q → q ≤ (k : ℝ) - 1 / 2 →
    (k : ℝ) - 1 / 2 < t → t < (k : ℝ) →
    ∀ C : ℝ, 0 ≤ C → ∀ R : ℝ, 0 ≤ R →
    ∀ ζ : ℝ, (q = (k : ℝ) - 1 → 0 < ζ) → SmallCapGain k q t C R ζ

theorem fiberCover_mono {k : ℕ} {q C ε δ : ℝ} {E F : Set (Point k × Direction k)}
    (h : FiberCover k q C ε δ E) (hFE : F ⊆ E) : FiberCover k q C ε δ F := by
  intro w
  obtain ⟨A, hA, hcover⟩ := h w
  exact ⟨A, hA, fun x hx => hcover x (hFE hx)⟩

/-- The standalone tube definition has exactly the port's unit-vector formula. -/
theorem perpendicular_projection_formula {k : ℕ} (w : Direction k) (v : Point k) :
    ((ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto v : Point k) =
      v - inner ℝ (w : Point k) v • (w : Point k) := by
  have hw : ‖(w : Point k)‖ = 1 := by simpa using w.property
  rw [Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hw]

/-- Reanchor a tube at an incident point; its width increases by at most two. -/
theorem reanchor_tube {k : ℕ} (w : Direction k) (x y a : Point k) {s : ℝ}
    (hx : ‖(ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto (x - a)‖ ≤ s)
    (hy : ‖(ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto (y - a)‖ ≤ s) :
    ‖(ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto (x - y)‖ ≤ 2 * s := by
  let P := (ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto
  have hxy : P (x - y) = P (x - a) - P (y - a) := by rw [← map_sub]; congr 1; abel
  change ‖P (x - y)‖ ≤ 2 * s
  rw [hxy]
  exact (norm_sub_le _ _).trans (by change ‖P (x - a)‖ + ‖P (y - a)‖ ≤ 2 * s; linarith)

/-- Fixed finite sums of power-small masses have a power-small bound with no
output constant, after reducing the gain and shrinking the scale threshold. -/
theorem absorb_finite_constant (M c : ℝ) (hc : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ < d → M * δ ^ c ≤ δ ^ (c / 2) := by
  have hlim : Tendsto (fun δ : ℝ => M * δ ^ (c / 2)) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.rpow_const_nhds_zero (by linarith : 0 < c / 2)).const_mul M
  have hev : ∀ᶠ δ : ℝ in 𝓝 0, M * δ ^ (c / 2) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨d, hd, fun δ hδ hδd => ?_⟩
  have hb := hbound (y := δ) (by simpa [Real.dist_eq, abs_of_pos hδ] using hδd)
  have hp : 0 ≤ δ ^ (c / 2) := Real.rpow_nonneg hδ.le _
  have heq : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  rw [heq, ← mul_assoc]
  simpa using mul_le_mul_of_nonneg_right hb.le hp

/-- A finite cover by small caps suffices; disjoint caps are unnecessary. -/
theorem finite_caps {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ A : Finset (Direction k), ∀ w : Direction k, ∃ a ∈ A, dist w a < ρ := by
  classical
  have hcompact : IsCompact (univ : Set (Direction k)) := isCompact_univ
  obtain ⟨A, hA⟩ := hcompact.elim_finite_subcover
    (fun a : Direction k => Metric.ball a ρ) (fun _ => Metric.isOpen_ball)
    (by intro w _; exact mem_iUnion.mpr ⟨w, Metric.mem_ball_self hρ⟩)
  refine ⟨A, fun w => ?_⟩
  simpa only [mem_iUnion, Metric.mem_ball, exists_prop] using hA (mem_univ w)

/-- Fully proved global conclusion conditional on the explicitly named bridge.
There is no axiom or sorry supplying that bridge. -/
theorem global_of_smallCapGain
    {k : ℕ} {q t C R ζ : ℝ} (hlocal : SmallCapGain k q t C R ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (μ : Measure (Point k)) (ν : Measure (Direction k)),
    Laws k q t R ζ ε δ μ ν → ∀ E : Set (Point k × Direction k),
    NullMeasurableSet E (μ.prod ν) → FiberCover k q C ε δ E →
    (μ.prod ν) E ≤ ENNReal.ofReal (δ ^ c) := by
  classical
  obtain ⟨ρ, hρ, ε, hε, c, hc, δ₀, hδ₀, hgain⟩ := hlocal
  obtain ⟨A, hA⟩ := finite_caps (k := k) hρ
  obtain ⟨d, hd, hsum⟩ := absorb_finite_constant (A.card : ℝ) c hc
  refine ⟨ε, hε, c / 2, by linarith, min δ₀ d, lt_min hδ₀ hd, ?_⟩
  intro δ hδ hδsmall μ ν hlaws E hE hcover
  let F : Direction k → Set (Point k × Direction k) :=
    fun a => E ∩ Prod.snd ⁻¹' Metric.ball a ρ
  have hF (a : Direction k) : NullMeasurableSet (F a) (μ.prod ν) :=
    hE.inter ((Metric.isOpen_ball.measurableSet.preimage measurable_snd).nullMeasurableSet)
  have hb (a : Direction k) : (μ.prod ν) (F a) ≤ ENNReal.ofReal (δ ^ c) := by
    apply hgain δ hδ (lt_min_iff.mp hδsmall).1 μ ν hlaws a (F a) (hF a)
      (fiberCover_mono hcover inter_subset_left)
    intro u hu
    exact (Metric.mem_ball.mp hu.2).le
  have hsub : E ⊆ ⋃ a ∈ A, F a := by
    intro u hu
    obtain ⟨a, ha, hua⟩ := hA u.2
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hu, hua⟩⟩
  calc
    (μ.prod ν) E ≤ (μ.prod ν) (⋃ a ∈ A, F a) := measure_mono hsub
    _ ≤ ∑ a ∈ A, (μ.prod ν) (F a) := measure_biUnion_finset_le A F
    _ ≤ ∑ _a ∈ A, ENNReal.ofReal (δ ^ c) := Finset.sum_le_sum fun a _ => hb a
    _ = ENNReal.ofReal ((A.card : ℝ) * δ ^ c) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.rpow_nonneg hδ.le _)]
      congr 1
      simp
    _ ≤ ENNReal.ofReal (δ ^ (c / 2)) :=
      ENNReal.ofReal_le_ofReal (hsum δ hδ (lt_min_iff.mp hδsmall).2)

end OAI.Falconer.LinearProjectionGainPartial


open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology

namespace OAI.Falconer.LinearProjectionGainPartial

/-- The port's normalized estimate, stated using the target's raw hypotheses. -/
def UnitDyadicGain (k : ℕ) (q t C ζ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ d : ℝ, 0 < d ∧
  ∀ N : ℕ, (1 / 2 : ℝ) ^ N < d →
  ∀ (μ : Measure (Point k)) (ν : Measure (Direction k)),
  Laws k q t (1 / 4) ζ ε ((1 / 2 : ℝ) ^ N) μ ν →
  ∀ E : Set (Point k × Direction k), MeasurableSet E →
  (∀ u ∈ E, ‖u.1‖ ≤ 1 / 4) →
  FiberCover k q C ε ((1 / 2 : ℝ) ^ N) E →
  (μ.prod ν) E ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ N) ^ c)


/-- Translate a restricted point law into the fixed source ball. -/
theorem translated_laws {k : ℕ} {q t R ζ ε δ : ℝ}
    {μ : Measure (Point k)} {ν : Measure (Direction k)}
    (h : Laws k q t R ζ ε δ μ ν) (b : Point k) :
    Laws k q t (1 / 4) ζ ε δ
      (Measure.map (fun x => x - b) (μ.restrict (Metric.closedBall b (1 / 4)))) ν := by
  obtain ⟨hm, hn, hs, hb, hq, hp⟩ := h
  refine ⟨?_, hn, ?_, ?_, hq, hp⟩
  · rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
    exact (Measure.restrict_le_self _).trans hm
  · rw [ae_map_iff (by fun_prop : Measurable (fun x : Point k => x - b)).aemeasurable
      (measurableSet_le measurable_norm measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  · intro x r hδr hr
    rw [Measure.map_apply (by fun_prop) measurableSet_ball]
    have he : (fun y : Point k => y - b) ⁻¹' Metric.ball x r = Metric.ball (x + b) r := by
      ext y
      simp only [mem_preimage, Metric.mem_ball, dist_eq_norm]
      congr 2
      abel
    rw [he]
    exact (Measure.restrict_le_self _).trans (hb (x + b) r hδr hr)


/-- Translated relations retain their finite covers without changing width. -/
theorem translated_cover {k : ℕ} {q C ε δ : ℝ}
    {E : Set (Point k × Direction k)} (h : FiberCover k q C ε δ E) (b : Point k) :
    FiberCover k q C ε δ
      ((fun u : Point k × Direction k => (u.1 + b, u.2)) ⁻¹'
        (E ∩ Prod.fst ⁻¹' Metric.closedBall b (1 / 4))) := by
  classical
  intro w
  obtain ⟨A, hA, hc⟩ := h w
  refine ⟨A.image (fun a => a - b), ?_, ?_⟩
  · exact (show ((A.image (fun a => a - b)).card : ℝ) ≤ A.card by
      exact_mod_cast Finset.card_image_le).trans hA
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hc (x + b) hx.1
    refine ⟨a - b, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    convert hxa using 1 <;> congr 2 <;> abel


/-- Translation of a localized relation preserves its product mass. -/
theorem translated_mass {k : ℕ} (μ : Measure (Point k)) (ν : Measure (Direction k))
    [SFinite μ] [SFinite ν] (E : Set (Point k × Direction k)) (hE : MeasurableSet E)
    (b : Point k) :
    ((Measure.map (fun x => x - b) (μ.restrict (Metric.closedBall b (1 / 4)))).prod ν)
      ((fun u : Point k × Direction k => (u.1 + b, u.2)) ⁻¹'
        (E ∩ Prod.fst ⁻¹' Metric.closedBall b (1 / 4))) =
    (μ.prod ν) (E ∩ Prod.fst ⁻¹' Metric.closedBall b (1 / 4)) := by
  let F := E ∩ Prod.fst ⁻¹' Metric.closedBall b (1 / 4)
  have hF : MeasurableSet F := hE.inter ((measurableSet_closedBall).preimage measurable_fst)
  have he : ν = Measure.map id ν := Measure.map_id.symm
  conv_lhs => rw [he]
  rw [Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    Measure.map_apply (by fun_prop) (hF.preimage (by fun_prop))]
  have hp : Prod.map (fun x : Point k => x - b) id ⁻¹'
      ((fun u : Point k × Direction k => (u.1 + b, u.2)) ⁻¹' F) = F := by
    ext u
    simp [Prod.map]
  rw [hp, Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply hF]
  congr 1
  apply inter_eq_left.mpr
  intro u hu
  exact ⟨hu.2, mem_univ _⟩


/-- A normalized dyadic estimate extends to bounded support and completed relations.
A finite spatial cover avoids any change of scale. -/
theorem bounded_dyadic_gain {k : ℕ} {q t C R ζ : ℝ}
    (hunit : UnitDyadicGain k q t C ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ d : ℝ, 0 < d ∧
    ∀ N : ℕ, (1 / 2 : ℝ) ^ N < d →
    ∀ (μ : Measure (Point k)) (ν : Measure (Direction k)),
    Laws k q t R ζ ε ((1 / 2 : ℝ) ^ N) μ ν →
    ∀ E : Set (Point k × Direction k), NullMeasurableSet E (μ.prod ν) →
    FiberCover k q C ε ((1 / 2 : ℝ) ^ N) E →
    (μ.prod ν) E ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ N) ^ c) := by
  classical
  obtain ⟨ε, hε, c, hc, d, hd, hg⟩ := hunit
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : Point k) R).elim_finite_subcover
    (fun b : Point k => Metric.ball b (1 / 4)) (fun _ => Metric.isOpen_ball)
    (by intro x _; exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  obtain ⟨d', hd', habs⟩ := absorb_finite_constant (A.card : ℝ) c hc
  refine ⟨ε, hε, c / 2, by positivity, min d d', lt_min hd hd', ?_⟩
  intro N hN μ ν hl E hE hcov
  let δ : ℝ := (1 / 2 : ℝ) ^ N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  letI : IsFiniteMeasure μ := ⟨hl.1.trans_lt (by simp)⟩
  letI : IsFiniteMeasure ν := ⟨hl.2.1.trans_lt (by simp)⟩
  obtain ⟨E₀, hsub, hE₀, heq⟩ := hE.exists_measurable_subset_ae_eq
  let F := E₀ ∩ {u : Point k × Direction k | ‖u.1‖ ≤ R}
  have hF : MeasurableSet F := hE₀.inter (measurableSet_le (by fun_prop) measurable_const)
  have hFE : F ⊆ E := inter_subset_left.trans hsub
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    apply measure_congr
    filter_upwards [heq, Measure.quasiMeasurePreserving_fst.ae hl.2.2.1] with u hu hs
    apply propext
    change (u ∈ E₀ ∧ ‖u.1‖ ≤ R) ↔ u ∈ E
    simp only [hs, and_true]
    exact Iff.of_eq hu
  let P : Point k → Set (Point k × Direction k) :=
    fun b => F ∩ Prod.fst ⁻¹' Metric.closedBall b (1 / 4)
  have hb (b : Point k) : (μ.prod ν) (P b) ≤ ENNReal.ofReal (δ ^ c) := by
    let μb := Measure.map (fun x : Point k => x - b) (μ.restrict (Metric.closedBall b (1 / 4)))
    let Eb := (fun u : Point k × Direction k => (u.1 + b, u.2)) ⁻¹' P b
    have hEb : MeasurableSet Eb :=
      (hF.inter ((measurableSet_closedBall).preimage measurable_fst)).preimage (by fun_prop)
    have hbound : ∀ u ∈ Eb, ‖u.1‖ ≤ 1 / 4 := by
      intro u hu
      have hh : dist (u.1 + b) b ≤ 1 / 4 := hu.2
      simpa only [dist_eq_norm, add_sub_cancel_right] using hh
    have hh := hg N (lt_min_iff.mp hN).1 μb ν (translated_laws hl b) Eb hEb hbound
      (translated_cover (fiberCover_mono hcov hFE) b)
    rw [translated_mass μ ν F hF b] at hh
    exact hh
  have hcover : F ⊆ ⋃ b ∈ A, P b := by
    intro u hu
    have hx : u.1 ∈ Metric.closedBall (0 : Point k) R := by
      have hnorm : ‖u.1‖ ≤ R := hu.2
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp (hA hx)
    exact mem_iUnion₂.mpr ⟨b, hb, hu, (Metric.mem_ball.mp hxb).le⟩
  rw [← hmass]
  calc
    (μ.prod ν) F ≤ (μ.prod ν) (⋃ b ∈ A, P b) := measure_mono hcover
    _ ≤ ∑ b ∈ A, (μ.prod ν) (P b) := measure_biUnion_finset_le A P
    _ ≤ ∑ _b ∈ A, ENNReal.ofReal (δ ^ c) := Finset.sum_le_sum (fun b _ => hb b)
    _ = ENNReal.ofReal ((A.card : ℝ) * δ ^ c) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (δ ^ (c / 2)) := ENNReal.ofReal_le_ofReal
      (habs δ hδ (lt_min_iff.mp hN).2)


end OAI.Falconer.LinearProjectionGainPartial

/- Helper proofs copied from port_sources.txt. Original module names below
identify their provenance. Only the listed platform nodes are imported. -/
section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SmallGaussianChart
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed direction-chart radius for the controlled Gaussian slice geometry -/

namespace Falconer

theorem exists_small_gaussian_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 ∧
      4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
  let A : ℝ := 4*(h:ℝ)+1+8*(h:ℝ)*(h+2:ℝ)
  let ρ : ℝ := 1/(8*(A+1))
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 8*(A+1)*ρ = 1 := by dsimp [ρ]; field_simp
  have hp : A*ρ ≤ 1/8 := by nlinarith
  have hcoef : (h:ℝ)*((h+2:ℝ)*2) ≤ A := by dsimp [A]; nlinarith
  refine ⟨ρ,hρ,?_,?_,?_⟩
  · nlinarith [mul_nonneg hA hρ.le]
  · have hb := mul_le_mul_of_nonneg_right hcoef hρ.le
    nlinarith
  · calc
      _ = A*ρ := by dsimp [A]; ring
      _ ≤ 1/8 := hp
      _ ≤ 1/4 := by norm_num

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic number of dyadic tests fits inside the chosen power loss -/

namespace Falconer
open Real Filter
open scoped Topology

theorem dyadic_log_depth (N : ℕ) :
    1-Real.log (1/(2:ℝ)^N)/Real.log 2 = (N:ℝ)+1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [one_div,Real.log_inv,Real.log_pow]
  field_simp
  ring

theorem eventually_dyadic_loss_absorption {ε κ : ℝ} (hεκ : ε < κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ C*(1-Real.log δ/Real.log 2)*δ^(-ε) ≤ δ^(-κ) := by
  have hr : 0 < κ-ε := sub_pos.mpr hεκ
  have hp : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hp₀ : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hr.ne'] using (Real.continuous_rpow_const hr.le).tendsto (0:ℝ)
    exact hp₀.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have ht : Tendsto (fun δ : ℝ => C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div,sub_zero,mul_zero] using (hp.sub (hl.div_const (Real.log 2))).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsmall,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hs hδone
  have hδ := hδone.1
  refine ⟨hδ,?_⟩
  calc
    _ = (C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))*δ^(-κ) := by
      calc
        _ = C*(1-Real.log δ/Real.log 2)*δ^((κ-ε)+(-κ)) := by congr 2; ring
        _ = C*(1-Real.log δ/Real.log 2)*(δ^(κ-ε)*δ^(-κ)) := by rw [Real.rpow_add hδ]
        _ = _ := by ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the concrete slice-selection losses into the planar gain -/

namespace Falconer
open Real Filter
open scoped Topology

theorem gaussian_scale_power {δ κ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    (δ^(-κ))^j = δ^(-((j:ℝ)*κ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  congr 1
  ring

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarGainNumerics
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorbing the explicit losses in the planar measure obstruction

Only fixed constants, logarithms and ceilings are absorbed here. The
underlying incidence estimate has already been proved from the cited
published input.
-/

namespace Falconer
open Real Filter
open scoped Topology

theorem rpow_absorb_constant {δ t u C : ℝ} (hδ : 0 < δ)
    (hC : C ≤ δ^(-(u-t))) : C * δ^(-t) ≤ δ^(-u) := by
  calc
    _ ≤ δ^(-(u-t)) * δ^(-t) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the concrete slice-selection losses into the planar gain -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_gaussian_scale_losses {η : ℝ} (hη : 0 < η)
    (K₀ V A b : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      4*V*(δ^(-(η/100)))^10 < δ^(-η) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let κ := η/100
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hten : 0 < η-10*κ := by dsimp [κ]; linarith
  have htwelve : 0 < η-12*κ := by dsimp [κ]; linarith
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -κ < 0 by linarith)).eventually
    (eventually_ge_atTop K₀)
  have hnorm := (tendsto_rpow_neg_nhdsGT_zero (show -(η-10*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop (4*V))
  have hcover := (tendsto_rpow_neg_nhdsGT_zero (show -(η-12*κ) < 0 by linarith)).eventually
    (eventually_ge_atTop A)
  filter_upwards [hlarge,hnorm,hcover,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)]
    with δ hlarge hnorm hcover hδone
  have hδ := hδone.1
  refine ⟨hδ,hlarge,?_,?_⟩
  · change 4*V*(δ^(-κ))^10 < δ^(-η)
    rw [gaussian_scale_power hδ]
    calc
      _ < δ^(-(η-10*κ))*δ^(-((10:ℝ)*κ)) :=
        mul_lt_mul_of_pos_right hnorm (Real.rpow_pos_of_pos hδ _)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  · change A*(δ^(-κ))^12*δ^(-b) ≤ δ^(-b-η)
    rw [gaussian_scale_power hδ]
    calc
      _ = A*δ^(-(12*κ+b)) := by rw [mul_assoc,← Real.rpow_add hδ]; congr 2; ring
      _ ≤ δ^(-(b+η)) := rpow_absorb_constant hδ (by
        rw [show -((b+η)-(12*κ+b)) = -(η-12*κ) by ring]
        exact hcover)
      _ = _ := by congr 1; ring

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarLossBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One scale choice supplies every scalar inequality in the planar slice application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem inverse_power_gap {δ η H : ℝ} (hδ : 0 < δ) (hH : 0 < H)
    (hgap : H < δ^(-η)) : δ^η < 1/H := by
  apply (lt_div_iff₀ hH).mpr
  calc
    δ^η*H < δ^η*δ^(-η) := mul_lt_mul_of_pos_left hgap (Real.rpow_pos_of_pos hδ η)
    _ = 1 := by
      rw [Real.rpow_neg hδ.le]
      exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ η))

theorem eventually_gaussian_planar_loss_budget {η : ℝ} (hη : 0 < η)
    {V a : ℝ} (hV : 1 ≤ V) (ha : 1 ≤ a) (f b A K₀ : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ K₀ ≤ δ^(-(η/100)) ∧
      1 ≤ 4*(δ^(-(η/100)))^10*V ∧
      (4*(δ^(-(η/100)))^10*V)*(4*a)^f ≤ δ^(-η) ∧
      (4*(δ^(-(η/100)))^10*V)*(8*a)^b ≤ δ^(-η) ∧
      δ^η < 1/(4*(δ^(-(η/100)))^10*V) ∧
      A*(δ^(-(η/100)))^12*δ^(-b) ≤ δ^(-b-η) := by
  let W : ℝ := V*((4*a)^f+(8*a)^b+1)
  have hVpos : 0 < V := by linarith
  have ha0 : 0 < a := by linarith
  have hfpos : 0 < (4*a)^f := Real.rpow_pos_of_pos (by positivity) _
  have hbpos : 0 < (8*a)^b := Real.rpow_pos_of_pos (by positivity) _
  have hVW : V < W := by dsimp [W]; nlinarith
  have hpf : V*(4*a)^f ≤ W := by dsimp [W]; nlinarith
  have hqb : V*(8*a)^b ≤ W := by dsimp [W]; nlinarith
  filter_upwards [eventually_gaussian_scale_losses hη (max K₀ 1) W A b]
    with δ hδ
  rcases hδ with ⟨hδ,hK,hgap,hcover⟩
  have hK₀ : K₀ ≤ δ^(-(η/100)) := (le_max_left _ _).trans hK
  have hK1 : 1 ≤ δ^(-(η/100)) := (le_max_right _ _).trans hK
  have hKpow : 1 ≤ (δ^(-(η/100)))^10 := one_le_pow₀ hK1
  have hH : 0 < 4*(δ^(-(η/100)))^10*V := by positivity
  have hHW : 4*(δ^(-(η/100)))^10*V < δ^(-η) := by
    apply lt_trans _ hgap
    nlinarith [Real.rpow_pos_of_pos hδ (-(η/100))]
  refine ⟨hδ,hK₀,?_,?_,?_,inverse_power_gap hδ hH hHW,hcover⟩
  · nlinarith
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]
  · apply le_trans _ hgap.le
    nlinarith [pow_nonneg (Real.rpow_nonneg hδ.le (-(η/100))) 10]

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianBandConstant_pos : 0 < gaussianBandConstant := by
  unfold gaussianBandConstant
  positivity

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularized two-vector Gaussian band bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianPairBandConstant_pos : 0 < gaussianPairBandConstant := by
  unfold gaussianPairBandConstant
  have := gaussianBandConstant_pos
  positivity

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMomentScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed coefficient for the original finite-scale moment bounds -/

namespace Falconer

theorem exists_gaussian_moment_coefficient (h : ℕ) (t q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (4*gaussianVectorBandConstant)^h*L*gaussianFrostmanFactor h t ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*L*gaussianFrostmanFactor h q ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*(|L*gaussianFrostmanFactor h q|+1) ≤ C*L := by
  let P := (4*gaussianVectorBandConstant)^h*gaussianFrostmanFactor h t
  let Q := (2*gaussianPairBandConstant)^h*gaussianFrostmanFactor h q
  let U := (2*gaussianPairBandConstant)^h*(|gaussianFrostmanFactor h q|+1)
  let C := |P|+|Q|+U+1
  have hG := gaussianPairBandConstant_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hPC : P ≤ C := by dsimp [C]; linarith [le_abs_self P,abs_nonneg Q]
  have hQC : Q ≤ C := by dsimp [C]; linarith [le_abs_self Q,abs_nonneg P]
  have hUC : U ≤ C := by dsimp [C]; linarith [abs_nonneg P,abs_nonneg Q]
  refine ⟨C,hC,?_⟩
  intro L hL
  have hL0 : 0 ≤ L := by linarith
  refine ⟨?_,?_,?_⟩
  · simpa only [P,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hPC hL0
  · simpa only [Q,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hQC hL0
  · calc
      _ = (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+1) := by
        rw [abs_mul,abs_of_nonneg hL0]
      _ ≤ (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+L) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hL _) (by positivity)
      _ = U*L := by dsimp [U]; ring
      _ ≤ C*L := mul_le_mul_of_nonneg_right hUC hL0

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FrameEmbedding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear isometry associated with a finite orthonormal frame -/

namespace Falconer
variable {d h : ℕ}

theorem frameLinearMap_orthonormal {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (frameLinearMap v ∘ (EuclideanSpace.basisFun (Fin h) ℝ).toBasis) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  change inner ℝ (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i))
    (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ j)) = _
  simpa only [frameLinearMap_basis] using hv i j

theorem orthonormal_frame_embedding {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    ∃ e : Space h →ₗᵢ[ℝ] Space d,
      ∀ i, e (EuclideanSpace.basisFun (Fin h) ℝ i) = v i := by
  let e : Space h →ₗᵢ[ℝ] Space d := (frameLinearMap v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin h) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin h) ℝ).orthonormal (frameLinearMap_orthonormal hv)
  refine ⟨e,?_⟩
  intro i
  change frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i
  exact frameLinearMap_basis v i

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_TransverseFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniformly transverse row frame for each fixed spherical chart -/

namespace Falconer
variable {n h : ℕ}

theorem exists_transverse_row_frame (hhn : h ≤ n) {w : Space (n+1)} (hw : ‖w‖ = 1) :
    ∃ e : Space h →ₗᵢ[ℝ] Space (n+1),
      ∀ i, inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0 := by
  let u := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let R : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have hR : R u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let f : Fin h → Fin (n+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp [f] at he
    omega
  let v : Fin h → Space (n+1) := fun i => R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))
  have hv : Orthonormal ℝ v := by
    exact ((EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.comp f hf).comp_linearIsometryEquiv R
  obtain ⟨e,he⟩ := orthonormal_frame_embedding hv
  refine ⟨e,fun i => ?_⟩
  rw [he,← hR]
  change inner ℝ (R u) (R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))) = 0
  rw [R.inner_map_map]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.2 (by
    intro heq
    have hz := congrArg Fin.val heq
    dsimp [f] at hz
    omega)

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLocalBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussianLocalBandConstant_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianLocalBandConstant n ρ := by
  unfold gaussianLocalBandConstant gaussianVolumeNormalization
  positivity

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ActiveCoverScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original tube count after codimension-h slicing -/

namespace Falconer

theorem gaussian_active_cover_scale {δ ε κ q Nc D : ℝ} (h : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεκ : ε ≤ κ) (hD : 0 ≤ D)
    (hNc : Nc ≤ δ^(-q-ε)) :
    (δ^(-κ))^11*(Nc*(2*(D*δ))^h) ≤
      (2*D)^h*(δ^(-κ))^12*δ^(-(q-(h:ℝ))) := by
  have hε : δ^(-ε) ≤ δ^(-κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεκ)
  have hpower : δ^(-q-ε)*δ^h = δ^(-ε)*δ^(-(q-(h:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (δ^(-κ))^11*(δ^(-q-ε)*(2*(D*δ))^h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNc (by positivity)) (by positivity)
    _ = (2*D)^h*(δ^(-κ))^11*(δ^(-ε)*δ^(-(q-(h:ℝ)))) := by
      rw [show 2*(D*δ) = (2*D)*δ by ring,mul_pow]
      calc
        _ = (2*D)^h*(δ^(-κ))^11*(δ^(-q-ε)*δ^h) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (2*D)^h*(δ^(-κ))^11*(δ^(-κ)*δ^(-(q-(h:ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg hδ.le _)) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OriginalDirectionChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a small direction chart on the original incidence labels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sphere_chart_pair_inner_nonnegative (w v c : Sphere d)
    (hw : dist w c ≤ 1/2) (hv : dist v c ≤ 1/2) :
    0 ≤ inner ℝ (w:Space d) (v:Space d) := by
  have hd : dist w v ≤ 1 := (dist_triangle w c v).trans (by rw [dist_comm c v]; linarith)
  have hn : ‖(w:Space d)-(v:Space d)‖ ≤ 1 := by simpa only [Subtype.dist_eq,dist_eq_norm] using hd
  have hsq := norm_sub_sq_real (w:Space d) (v:Space d)
  rw [sphere_norm,sphere_norm] at hsq
  nlinarith [norm_nonneg ((w:Space d)-(v:Space d))]

theorem original_direction_chart_selection
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0∞}
    (hmean : ENNReal.ofReal ((2/ρ+1)^d)*a < (μ.prod ν) E) :
    ∃ c : Sphere d, a < (μ.prod (ν.restrict (closedBall c ρ))) E := by
  classical
  obtain ⟨S,_,hcover,hcard,_⟩ := finite_separated_cap_net d (show 0 < 2*ρ by positivity)
  have hcover' (w : Sphere d) : ∃ c ∈ S, dist w c ≤ ρ := by
    have hr : (2*ρ)/2 = ρ := by ring
    simpa only [hr] using hcover w
  let F : Sphere d → Set (Space d × Sphere d) := fun c => E ∩ (univ ×ˢ closedBall c ρ)
  have hsub : E ⊆ ⋃ c ∈ S, F c := by
    intro z hz
    obtain ⟨c,hc,hd⟩ := hcover' z.2
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hz,mem_univ _,hd⟩⟩
  have hmass : (μ.prod ν) E ≤ ∑ c ∈ S, (μ.prod ν) (F c) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le S F)
  have he (c : Sphere d) : (μ.prod ν) (F c) = (μ.prod (ν.restrict (closedBall c ρ))) E := by
    have hprod : μ.prod (ν.restrict (closedBall c ρ)) =
        (μ.prod ν).restrict (univ ×ˢ closedBall c ρ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := μ) (ν := ν) univ (closedBall c ρ)
    rw [hprod,Measure.restrict_apply hE]
  by_contra! hn
  have hsum : (μ.prod ν) E ≤ (S.card:ℝ≥0∞)*a := hmass.trans (by
    calc
      _ ≤ ∑ _c ∈ S, a := Finset.sum_le_sum (fun c _ => by rw [he]; exact hn c)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul])
  have hcard' : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal ((2/ρ+1)^d) := by
    have hh : (S.card:ℝ) ≤ (2/ρ+1)^d := by
      have hr : 4/(2*ρ)+1 = 2/ρ+1 := by field_simp; ring
      simpa only [hr] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  exact (not_le_of_gt hmean) (hsum.trans (mul_le_mul' hcard' le_rfl))

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NonendpointChartGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform nonendpoint angular decay on a fixed original direction chart -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_chart_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C ρ : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
    (hstable : (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2)
    (hchart : 4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  obtain ⟨η,δF,hη,hδF,hgain⟩ := controlled_dyadic_angular_gain hpublished hq hq' hqt ht hC
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t q
  let κ₀ := η/100
  let ε := κ₀/2
  let c := κ₀/2
  let M := (h+2:ℝ)*(2*ρ)+1
  let Z := M+1
  let V := (2*Z)^h
  let a₀ := 4+8*(h:ℝ)
  let D := 1+2*(1/4)+C*M
  let B₀ := (2:ℝ)^h*gaussianLocalBandConstant (h+1) ρ^h
  have hκ : 0 < κ₀ := by dsimp [κ₀]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hεκ : ε < κ₀ := by dsimp [ε]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 1 ≤ V := by
    apply one_le_pow₀
    change 1 ≤ 2*(M+1)
    linarith
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+1) hρ
    dsimp [B₀]
    positivity
  have hplan := eventually_gaussian_planar_loss_budget hη hV ha₀ (t-(h:ℝ))
    (q-(h:ℝ)) ((2*D)^h) (4*(1+2*(2:ℝ)^h+1))
  have hdepth := eventually_dyadic_loss_absorption hεκ Cm
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(κ₀-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop (1/B₀))
  obtain ⟨δ₁,hδ₁,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp
      (hplan.and (hdepth.and habs))
  refine ⟨ε,c,min δF (min δ₁ (min ρ 1)),hε,hc,
    lt_min hδF (lt_min hδ₁ (lt_min hρ (by norm_num))),?_⟩
  intro N κ _ _ μ ν _ _ w₀ E J a hδsmall hν hμ hμmass hνmass hμball hνball
    hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-κ₀)
  let L : ℝ := δ^(-ε)
  let Nc : ℝ := δ^(-q-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_left _ _)) |>.le
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le (min_le_right _ _)).trans_le
    ((min_le_right _ _).trans (min_le_right _ _)) |>.le
  obtain ⟨hp,⟨_,hd⟩,ha⟩ := hready ⟨hδ,hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  rcases hp with ⟨_,hlarge,hH,hpcoef,hqcoef,hlow,hcoverScale⟩
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 0 < K := Real.rpow_pos_of_pos hδ _
  have hL0 : 0 ≤ L := by linarith
  have hCmL : 0 ≤ Cm*L := mul_nonneg hCm.le hL0
  have hcard : ((N+1:ℕ):ℝ)*(Cm*L) ≤ K := by
    rw [dyadic_log_depth N] at hd
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hd
  have hCK : Cm*L ≤ K := by
    have hN : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left hCmL hN).trans hcard
  have hpair : ∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,Measure.quasiMeasurePreserving_snd.ae hν]
      with u hu hv
    exact sphere_chart_pair_inner_nonnegative u.1 u.2 w₀ (hu.trans hρhalf) (hv.trans hρhalf)
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+1) (by omega) (sphere_norm w₀)
  have hchartδ : 4*(h:ℝ)*δ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
    nlinarith [mul_le_mul_of_nonneg_left hδρ (by positivity : 0 ≤ 4*(h:ℝ))]
  have hbox : (1/4)*((h+2:ℝ)*(2*ρ)+1)+δ ≤ Z := by
    change (1/4)*M+δ ≤ M+1
    nlinarith
  have hactive : K^11*(Nc*(2*(δ+(2*(1/4))*δ+(C*δ)*M))^h) ≤ δ^(-(q-(h:ℝ))-η) := by
    have hh := gaussian_active_cover_scale h hδ hδ1 hεκ.le hD.le (le_refl Nc)
    have hr : δ+(2*(1/4))*δ+(C*δ)*M = D*δ := by dsimp [D]; ring
    rw [hr]
    exact hh.trans hcoverScale
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hg := hgain N κ μ ν w₀ B E J a ρ L L K (Cm*L) Nc Z a₀
    (hδsmall.trans_le (min_le_left _ _)) hρ.le hδρ hB hν hstable hchartδ hμ hμmass hνmass
    hL0 hL0 hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hZ hCP hCD hCM
    hcard hCK hlarge hbox ha₀ hH (le_refl a₀) hpcoef hqcoef hlow hactive
    hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+1) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^κ₀ := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ gaussianLocalBandConstant (h+1) ρ^h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le κ₀),mul_assoc] using hr
  have habs' : (1/B₀)*δ^κ₀ ≤ δ^c := by
    have hh := rpow_absorb_constant (t := -κ₀) (u := -c) hδ (by
      convert ha using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf))
    simpa only [neg_neg] using hh
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^κ₀ := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs'

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NonendpointAngularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonendpoint angular gain in every ambient dimension h+2 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem nonendpoint_dyadic_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2)),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε)) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρhalf,hstable,hchart⟩ := exists_small_gaussian_chart_radius h
  obtain ⟨ε,c₁,δ₁,hε,hc₁,hδ₁,hgain⟩ := nonendpoint_chart_angular_gain hpublished hq hq' hqt ht
    hC hρ hρhalf hstable hchart
  let H : ℝ := (2/ρ+1)^(h+2)
  let c := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := (tendsto_rpow_neg_nhdsGT_zero (show -(c₁-c) < 0 by dsimp [c]; linarith)).eventually
    (eventually_ge_atTop H)
  obtain ⟨δ₂,hδ₂,hready⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < 1 by norm_num)).mp habs
  refine ⟨ε,c,min δ₁ δ₂,hε,hc,lt_min hδ₁ hδ₂,?_⟩
  intro N κ _ _ μ ν _ _ E J a hδsmall hμ hμmass hνmass hμball hνball hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hH : H*δ^c₁ ≤ δ^c := by
    have ha : H ≤ δ^(-(c₁-c)) := hready ⟨hδ,hδsmall.trans_le (min_le_right _ _)⟩
    have hh := rpow_absorb_constant (t := -c₁) (u := -c) hδ (by
      convert ha using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf))
    simpa only [neg_neg] using hh
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (x : Sphere (h+2)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^q) :=
    (Measure.restrict_le_self _).trans (hνball x j hj)
  have hg := hgain N κ μ ν' w₀ E J a (hδsmall.trans_le (min_le_left _ _))
    hνsupport hμ hμmass hν'mass hμball hν'ball hE hJ hJN hEb hanchors hcover
  have hgle : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₁) := by
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
      ENNReal.ofReal_le_ofReal hg
  exact (not_lt_of_ge hgle) hw₀

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteAnchorLabels
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite anchor labels for the measurable original tube lists -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem finiteAnchorLabels_mem (G J : Finset (Space d)) (a : {a // a ∈ G}) :
    a ∈ finiteAnchorLabels G J ↔ a.val ∈ J := by
  classical
  exact Finset.mem_subtype

theorem finiteAnchorLabels_card (G J : Finset (Space d)) (hJG : J ⊆ G) :
    (finiteAnchorLabels G J).card = J.card := by
  classical
  rw [finiteAnchorLabels,Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun a ha => hJG ha)

theorem finiteAnchorLabels_measurable (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (a : {a // a ∈ G}) :
    MeasurableSet {w | a ∈ finiteAnchorLabels G (J w)} := by
  simpa only [finiteAnchorLabels_mem] using hJ a.val

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TubeCoverEnumeration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the admissible finite lists from a bounded anchor net -/

namespace Falconer
open Set
variable {X : Type*}

theorem bounded_finset_enumeration (G : Finset X) (N : ℕ) :
    ∃ C : ℕ → Finset X, (∀ n, C n ⊆ G ∧ (C n).card ≤ N) ∧
      ∀ J : Finset X, J ⊆ G → J.card ≤ N → ∃ n, C n = J := by
  classical
  let S := G.powerset.filter (fun J => J.card ≤ N)
  have hs : (∅ : Finset X) ∈ S := by simp [S]
  have : Nonempty {J : Finset X // J ∈ S} := ⟨⟨∅,hs⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat {J : Finset X // J ∈ S}
  refine ⟨fun n => (f n).val,?_,?_⟩
  · intro n
    have hp := Finset.mem_filter.mp (f n).property
    exact ⟨Finset.mem_powerset.mp hp.1,hp.2⟩
  · intro J hJG hJN
    have hJS : J ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJG,hJN⟩
    obtain ⟨n,hn⟩ := hf ⟨J,hJS⟩
    exact ⟨n,congrArg Subtype.val hn⟩

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

/-- Moving a unit direction changes the perpendicular test by at most twice
its angular displacement times the size of the tested vector. -/
theorem perpendicularPart_direction_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (v : E) :
    ‖perpendicularPart w v - perpendicularPart z v‖ ≤ 2 * ‖w-z‖ * ‖v‖ := by
  have he : perpendicularPart w v - perpendicularPart z v =
      inner ℝ z v • (z-w) + inner ℝ (z-w) v • w := by
    simp only [perpendicularPart, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ z v • (z-w)‖ + ‖inner ℝ (z-w) v • w‖ := norm_add_le _ _
    _ = |inner ℝ z v| * ‖z-w‖ + |inner ℝ (z-w) v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, mul_one]
    _ ≤ (‖z‖ * ‖v‖) * ‖z-w‖ + (‖z-w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z v)
        (norm_nonneg _)) (abs_real_inner_le_norm (z-w) v)
    _ = _ := by rw [hz, one_mul, norm_sub_rev z w]; ring

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TubeAnchorNet
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite bounded anchor nets for the original direction-wise tube covers -/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem exists_bounded_anchor_net (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ a ∈ S, ‖a‖ ≤ D) ∧
      ∀ x : Space d, ‖x‖ ≤ D → ∃ a ∈ S, ‖x-a‖ ≤ δ := by
  classical
  obtain ⟨T,hT,hfin,hcover⟩ := (isCompact_closedBall (0 : Space d) D).finite_cover_balls hδ
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro a ha
    simpa only [mem_closedBall,dist_zero_right] using hT (hfin.mem_toFinset.mp ha)
  · intro x hx
    have hxc : x ∈ closedBall (0 : Space d) D := by simpa only [mem_closedBall,dist_zero_right] using hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hcover hxc)
    refine ⟨a,hfin.mem_toFinset.mpr ha,?_⟩
    simpa only [mem_ball,dist_eq_norm] using hxa.le

theorem perpendicular_anchor_rounding {w x a y b : Space d} (hw : ‖w‖ = 1)
    {ε δ : ℝ} (hx : ‖perpendicularPart w (x-a)‖ ≤ ε)
    (hy : ‖perpendicularPart w (y-a)‖ ≤ ε) (hb : ‖y-b‖ ≤ δ) :
    ‖perpendicularPart w (x-b)‖ ≤ 2*ε+δ := by
  have he : perpendicularPart w (x-b) =
      (perpendicularPart w (x-a)-perpendicularPart w (y-a))+perpendicularPart w (y-b) := by
    simp only [perpendicularPart,inner_sub_right]
    module
  rw [he]
  exact (norm_add_le _ _).trans
    (((add_le_add (norm_sub_le _ _) (norm_perpendicularPart_le hw _)).trans
      (add_le_add (add_le_add hx hy) hb)).trans_eq (by ring))

theorem rounded_tube_cover (w : Sphere d) (E : Set (Space d))
    (S G : Finset (Space d)) {ε δ : ℝ}
    (hnet : ∀ x ∈ E, ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (hcover : ∀ x ∈ E, ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ J : Finset (Space d), J ⊆ G ∧ J.card ≤ S.card ∧
      ∀ x ∈ E, ∃ b ∈ J, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
  classical
  let P := fun a : Space d => ∃ y ∈ E, ‖perpendicularPart (w:Space d) (y-a)‖ ≤ ε
  have hround (a : Space d) (ha : P a) :
      ∃ b ∈ G, ∀ x ∈ E, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε →
        ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
    obtain ⟨y,hy,hya⟩ := ha
    obtain ⟨b,hb,hyb⟩ := hnet y hy
    exact ⟨b,hb,fun _ _ hx => perpendicular_anchor_rounding (sphere_norm w) hx hya hyb⟩
  let b : Space d → Space d := fun a => if ha : P a then (hround a ha).choose else 0
  let J := (S.filter P).image b
  refine ⟨J,?_,(Finset.card_image_le.trans (Finset.card_filter_le _ _)),?_⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hp := (Finset.mem_filter.mp ha).2
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.1
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    have hp : P a := ⟨x,hx,hxa⟩
    refine ⟨b a,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩,?_⟩
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.2 x hx hxa

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TubeCoverChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable choice of countably listed original-label tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W ι : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem tube_cover_uncovered_mass_measurable
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : Finset ι) :
    Measurable (fun w => μ {x | (x,w) ∈ E ∧ ∀ i ∈ C, x ∉ U i w}) := by
  have hC : MeasurableSet {p : W × X | ∀ i ∈ C, p.2 ∉ U i p.1} := by
    simp only [ofPred_forall]
    exact C.measurableSet_biInter (fun i _ => (hU i).compl)
  exact measurable_measure_prodMk_left ((hE.preimage measurable_swap).inter hC)

theorem exists_measurable_tube_cover_choice
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : ℕ → Finset ι)
    (hcover : ∀ w, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ i ∈ C n, x ∉ U i w} = 0) :
    ∃ J : W → Finset ι, (∀ i, MeasurableSet {w | i ∈ J w}) ∧
      (∀ w, μ {x | (x,w) ∈ E ∧ ∀ i ∈ J w, x ∉ U i w} = 0) ∧
      ∀ w, ∃ n, J w = C n := by
  classical
  let j : W → ℕ := fun w => Nat.find (hcover w)
  have hj : Measurable j := measurable_find hcover (fun n =>
    measurableSet_eq_fun (tube_cover_uncovered_mass_measurable μ E hE U hU (C n)) measurable_const)
  refine ⟨fun w => C (j w),?_,?_,?_⟩
  · intro i
    exact hj ((Set.to_countable {n | i ∈ C n}).measurableSet)
  · intro w
    exact Nat.find_spec (hcover w)
  · intro w
    exact ⟨j w,rfl⟩

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MeasurableTubeCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable bounded-grid covers of the original direction fibers -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem original_tube_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset (Space d),
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} = 0 := by
  classical
  obtain ⟨G,hGb,hGn⟩ := exists_bounded_anchor_net (d := d) D hδ
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  let U : Space d → Sphere d → Set (Space d) := fun a w =>
    {x | ‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ}
  have hU (a : Space d) : MeasurableSet {p : Sphere d × Space d | p.2 ∈ U a p.1} := by
    dsimp [U,perpendicularPart]
    exact measurableSet_le (by fun_prop) measurable_const
  have hc : ∀ w : Sphere d, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ a ∈ C n, x ∉ U a w} = 0 := by
    intro w
    obtain ⟨S,hSN,hS⟩ := hcover w
    obtain ⟨J,hJG,hJS,hJ⟩ := rounded_tube_cover w {x | (x,w) ∈ E} S G
      (fun x hx => hGn x (hbounded (x,w) hx)) hS
    obtain ⟨n,hn⟩ := hCs J hJG (hJS.trans hSN)
    refine ⟨n,?_⟩
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    obtain ⟨a,ha,hxa⟩ := hJ x hx.1
    exact (hx.2 a (hn.symm ▸ ha) hxa).elim
  obtain ⟨J,hJ,hzero,hJC⟩ := exists_measurable_tube_cover_choice μ E hE U hU C hc
  refine ⟨G,hGb,J,hJ,?_,hzero⟩
  intro w
  obtain ⟨n,hn⟩ := hJC w
  simpa only [hn] using hC n

theorem finite_tube_cover_relation_measurable
    (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (hJG : ∀ w, J w ⊆ G) (ε : ℝ) :
    MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
  have hm : MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ G, a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
    have hu : MeasurableSet (⋃ a ∈ G, {t : Space d × Sphere d |
        a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε}) := by
      apply G.measurableSet_biUnion
      intro a _
      have hp : MeasurableSet {t : Space d × Sphere d |
          ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
        dsimp [perpendicularPart]
        exact measurableSet_le (by fun_prop) measurable_const
      exact ((hJ a).preimage measurable_snd).inter hp
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [mem_ofPred_eq,mem_iUnion,exists_prop]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · rintro ⟨a,ha,hp⟩
    exact ⟨a,hJG t.2 ha,ha,hp⟩
  · rintro ⟨a,_,ha,hp⟩
    exact ⟨a,ha,hp⟩

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PreparedTubeRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a pointwise covered relation without losing original fiber mass -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem prepare_original_tube_relation (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G}, ∃ F : Set (Space d × Sphere d),
        MeasurableSet F ∧ F ⊆ E ∧
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        (∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) ∧
        ∀ t ∈ F, ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a.val)‖ ≤ 2*ε+δ := by
  classical
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  let C : Set (Space d × Sphere d) :=
    {t | ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ 2*ε+δ}
  have hC : MeasurableSet C := finite_tube_cover_relation_measurable G J hJ
    (fun w => (hJG w).1) _
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),E ∩ C,hE.inter hC,inter_subset_left,
    finiteAnchorLabels_measurable G J hJ,?_,?_,?_⟩
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    have he : {x | (x,w) ∈ E ∧ (x,w) ∉ E ∩ C} =
        {x | (x,w) ∈ E ∧ ∀ a ∈ J w, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} := by
      ext x
      constructor
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun a ha hp => hn ⟨hx,?_⟩⟩
        exact ⟨a,ha,hp⟩
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun ht => ?_⟩
        obtain ⟨a,ha,hp⟩ := ht.2
        exact hn a ha hp
    rw [he]
    exact hzero w
  · intro t ht
    obtain ⟨a,ha,hp⟩ := ht.2
    refine ⟨⟨a,(hJG t.2).1 ha⟩,?_,hp⟩
    exact (finiteAnchorLabels_mem G (J t.2) _).mpr ha

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Measures_OriginalCoverRestriction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Null original fiber losses stay null for every retained slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem product_inter_eq_of_null_original_fibers
    (μ α : Measure X) (β : Measure W) [SFinite α] [SFinite β] (hα : α ≪ μ)
    (E F : Set (X × W)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) :
    (α.prod β) (E ∩ F) = (α.prod β) E := by
  have hz : (α.prod β) (E \ F) = 0 := by
    rw [Measure.prod_apply_symm (hE.diff hF)]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun w => hα (hzero w))
  apply measure_congr
  have hnot : ∀ᵐ t ∂α.prod β, t ∉ E \ F := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hnot] with t ht
  apply propext
  change (t ∈ E ∧ t ∈ F) ↔ t ∈ E
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    by_contra hn
    exact ht ⟨h, hn⟩

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Radial_NonendpointTubeGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonendpoint angular decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem nonendpoint_dyadic_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (Space (h+2) × Sphere (h+2))),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
    (∀ w : Sphere (h+2), ∃ S : Finset (Space (h+2)),
      (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε) ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S,
        ‖perpendicularPart (w:Space (h+2)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,δ₀,hε,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_angular_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,δ₀,hε,hc,hδ₀,?_⟩
  intro N μ ν _ _ E hδsmall hμ hμmass hνmass hμball hνball hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-q-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N {a // a ∈ G} μ ν F J (fun a => a.val) hδsmall hμ hμmass hνmass
    hμball hνball hF hJ ?_ (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-q-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bounds for nonsingular systems of linear bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {j : ℕ}

theorem coordinateBox_measurable (r : ℝ) : MeasurableSet (coordinateBox j r) := by
  simp only [coordinateBox,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem coordinateBox_volume {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space j)) (coordinateBox j r) = ENNReal.ofReal ((2*r)^j) := by
  rw [← (PiLp.volume_preserving_toLp (Fin j)).measure_preimage
    (coordinateBox_measurable r).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin j → ℝ)) ⁻¹' coordinateBox j r =
      Set.pi univ (fun _ : Fin j => Icc (-r) r) := by
    ext x
    simp [coordinateBox,abs_le,Pi.le_def,forall_and]
  rw [he,volume_pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r)]

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointDyadicScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic cutoff and power conversions for endpoint assembly -/

namespace Falconer
open Filter
open scoped Topology

theorem dyadic_inverse_tendsto :
    Tendsto (fun N : ℕ => 1/(2:ℝ)^N) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div,inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1))
  · filter_upwards [] with N
    change 0 < 1/(2:ℝ)^N
    positivity

theorem dyadic_inverse_rpow (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^(-c) = (1/(2:ℝ)^N)^c := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

theorem dyadic_loss_conversion (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^c = (1/(2:ℝ)^N)^(-c) := by
  simpa only [neg_neg] using dyadic_inverse_rpow N (-c)

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointPowerAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict power gaps used in endpoint row and triple selection -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt {p q : ℝ} (hpq : q < p) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ C*δ^p < δ^q := by
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show q-p < 0 by linarith)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  calc
    _ < δ^(q-p)*δ^p := mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = _ := by rw [← Real.rpow_add hδ.1]; congr 1; ring

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointRowBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two radial row deletions fit inside the original incidence budget -/

namespace Falconer
open Real Filter
open scoped Topology ENNReal

theorem eventually_endpoint_row_base {u τ c₁ c₂ : ℝ}
    (hu : 0 < u) (hc₁ : τ+10*u < c₁) (hc₂ : τ+10*u < c₂) (V : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4 := by
  have h₀ := eventually_const_mul_rpow_lt (show u < 2*u by linarith) (12*V)
  have h₁ := eventually_const_mul_rpow_lt (show u < c₁-τ-9*u by linarith) (12*V)
  have h₂ := eventually_const_mul_rpow_lt (show u < c₂-τ-9*u by linarith) (12*V)
  filter_upwards [h₀,h₁,h₂] with δ h₀ h₁ h₂
  exact ⟨h₀.1,by nlinarith [h₀.2,h₁.2,h₂.2]⟩

theorem endpoint_row_cost_power {δ : ℝ} (hδ : 0 < δ) (u τ c V : ℝ) :
    δ^(-6*u)*δ^(-3*u)*V*(δ^c/δ^τ) = V*δ^(c-τ-9*u) := by
  rw [← Real.rpow_sub hδ]
  calc
    _ = V*(δ^(-6*u)*δ^(-3*u)*δ^(c-τ)) := by ring
    _ = _ := by rw [← Real.rpow_add hδ,← Real.rpow_add hδ]; congr 1; ring_nf

theorem endpoint_row_base_ennreal {δ u τ c₁ c₂ V : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V)
    (Z A₁ A₂ : ℝ≥0∞) (hZ : Z ≤ ENNReal.ofReal V)
    (hA₁ : A₁ ≤ ENNReal.ofReal (δ^c₁)) (hA₂ : A₂ ≤ ENNReal.ofReal (δ^c₂))
    (hbudget : V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4) :
    ENNReal.ofReal (δ^(2*u))*Z+
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A₁/ENNReal.ofReal (δ^τ))+
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A₂/ENNReal.ofReal (δ^τ)) ≤
        ENNReal.ofReal (δ^u/4) := by
  have hterm (A : ℝ≥0∞) (c : ℝ) (hA : A ≤ ENNReal.ofReal (δ^c)) :
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A/ENNReal.ofReal (δ^τ)) ≤
        ENNReal.ofReal (V*δ^(c-τ-9*u)) := by
    calc
      _ ≤ (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*ENNReal.ofReal V)*
          (ENNReal.ofReal (δ^c)/ENNReal.ofReal (δ^τ)) :=
        mul_le_mul' (mul_le_mul' le_rfl hZ) (ENNReal.div_le_div_right hA _)
      _ = ENNReal.ofReal (δ^(-6*u)*δ^(-3*u)*V*(δ^c/δ^τ)) := by
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hδ _),
          ← ENNReal.ofReal_mul (by positivity)]
      _ = _ := by rw [endpoint_row_cost_power hδ]
  have hb : ENNReal.ofReal (δ^(2*u))*Z ≤ ENNReal.ofReal (V*δ^(2*u)) := by
    calc
      _ ≤ ENNReal.ofReal (δ^(2*u))*ENNReal.ofReal V := mul_le_mul' le_rfl hZ
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity),mul_comm]
  apply (add_le_add (add_le_add hb (hterm A₁ c₁ hA₁)) (hterm A₂ c₂ hA₂)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hbudget

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointApplicationNumerics
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar endpoint budgets in the form used by the controlled slice -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem endpoint_stable_small {h : ℕ} {δ ρ : ℝ} (hδ : δ ≤ ρ)
    (hs : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) : 2*(h:ℝ)*δ < 1 := by
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hn : (h+3:ℝ) ≥ 1 := by linarith
  have hb : (h:ℝ)*ρ ≤ 1/4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hδ hh]

theorem endpoint_active_cover_power {h : ℕ} {δ ε u C ρ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεu : ε ≤ u) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hcount : (2*(1+2*(1/4)+C*((h+3:ℝ)*(2*ρ)+1)))^h*δ^(-1-12*u) ≤ δ^(-1-40*u)) :
    (δ^(-u))^11*(δ^(-(h+1:ℝ)-ε)*
      (2*(δ+(2*(1/4))*δ+(C*δ)*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ δ^(-1-40*u) := by
  let D : ℝ := 1+2*(1/4)+C*((h+3:ℝ)*(2*ρ)+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hh := gaussian_active_cover_scale h hδ hδ1 hεu hD
    (le_refl (δ^(-(h+1:ℝ)-ε)))
  have hr : δ+(2*(1/4))*δ+(C*δ)*((h+3:ℝ)*(2*ρ)+1) = D*δ := by dsimp [D]; ring
  rw [hr]
  have hq : -((h+1:ℝ)-(h:ℝ)) = -1 := by ring
  rw [hq] at hh
  simp only [gaussian_scale_power hδ,Nat.cast_ofNat] at hh
  have hp : δ^(-(12*u))*δ^((-1:ℝ)) = δ^(-1-12*u) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  rw [mul_assoc,hp] at hh
  simpa only [gaussian_scale_power hδ,Nat.cast_ofNat] using hh.trans hcount

theorem endpoint_bad_mass_ennreal {δ u τ : ℝ} (hδ : 0 < δ)
    (hbad : δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3)) :
    ENNReal.ofReal (δ^τ)+2*ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal (δ^τ) ≤
      ENNReal.ofReal ((δ^(2*u))^3/(4*((δ^(-u))^6)^3)) := by
  have hp : (δ^(-u))^6 = δ^(-6*u) := by
    simpa only [Nat.cast_ofNat,neg_mul] using gaussian_scale_power hδ 6
  rw [hp]
  calc
    _ = ENNReal.ofReal (δ^τ+2*δ^(-6*u)*δ^τ) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ^(-6*u)),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbad

theorem endpoint_selection_row_budget {δ u τ c₁ c₂ V : ℝ}
    (hδ : 0 < δ) (hV : 0 ≤ V) (Z A₁ A₂ : ℝ≥0∞)
    (hZ : Z ≤ ENNReal.ofReal V)
    (hA₁ : A₁ ≤ ENNReal.ofReal (δ^c₁)) (hA₂ : A₂ ≤ ENNReal.ofReal (δ^c₂))
    (hbase : V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4) :
    ENNReal.ofReal (δ^(2*u))*Z+
      (ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal ((δ^(-u))^3)*Z)*(A₁/ENNReal.ofReal (δ^τ))+
      (ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal ((δ^(-u))^3)*Z)*(A₂/ENNReal.ofReal (δ^τ)) ≤
      ENNReal.ofReal (1/(4*δ^(-u))) := by
  have hh := endpoint_row_base_ennreal hδ hV Z A₁ A₂ hZ hA₁ hA₂ hbase
  have hp (j : ℕ) : (δ^(-u))^j = δ^(-((j:ℝ)*u)) := gaussian_scale_power hδ j
  have hi : δ^u/4 = 1/(4*δ^(-u)) := by rw [Real.rpow_neg hδ.le]; field_simp
  rw [hp 6,hp 3]
  simpa only [Nat.cast_ofNat,neg_mul,hi] using hh

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointCountBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The strict dimension gap absorbs all endpoint tube-counting losses -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_count_power {δ : ℝ} (hδ : 0 < δ) (C a κ s : ℝ) :
    (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 =
      ((6*C+35)^6*((6:ℝ)^s)^2)*δ^(2*s-3-6*a-5*κ) := by
  have hp (t : ℝ) (k : ℕ) : (δ^t)^k = δ^(t*(k:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  rw [Real.mul_rpow (by norm_num) hδ.le,div_pow,mul_pow,mul_pow,
    hp (-1-κ) 3,hp a 6,hp (-κ) 2,hp s 2]
  calc
    _ = ((6*C+35)^6*((6:ℝ)^s)^2)*
        (δ^((-1-κ)*3)/δ^(a*6)*δ^(-κ*2)*δ^(s*2)) := by ring_nf
    _ = _ := by
      rw [← Real.rpow_sub hδ,← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring_nf

theorem eventually_endpoint_count_budget {s a κ : ℝ}
    (hgap : 0 < 2*s-3-6*a-7*κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2 := by
  let K : ℝ := (6*C+35)^6*((6:ℝ)^s)^2
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show -(2*s-3-6*a-7*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop K)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  rw [endpoint_count_power hδ.1]
  calc
    _ < δ^(-(2*s-3-6*a-7*κ))*δ^(2*s-3-6*a-5*κ) :=
      mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = (δ^κ)^2 := by
      rw [← Real.rpow_add hδ.1,← Real.rpow_natCast,← Real.rpow_mul hδ.1.le]
      congr 1
      ring_nf

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Measures_EndpointMassRatios
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common-triple mass and bad-triple thresholds are compatible -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_common_mass_ratio {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (δ^(2*u))^3/(2*(δ^(-6*u))^5) = (1/2)*δ^(36*u) := by
  have hp : (δ^(2*u))^3 = δ^(6*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hq : (δ^(-6*u))^5 = δ^(-30*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hp,hq]
  calc
    _ = (1/2)*(δ^(6*u)/δ^(-30*u)) := by ring
    _ = _ := by rw [← Real.rpow_sub hδ]; congr 2; ring

theorem endpoint_bad_mass_ratio {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (δ^(2*u))^3/(4*(δ^(-6*u))^3) = (1/4)*δ^(24*u) := by
  have hp : (δ^(2*u))^3 = δ^(6*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hq : (δ^(-6*u))^3 = δ^(-18*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hp,hq]
  calc
    _ = (1/4)*(δ^(6*u)/δ^(-18*u)) := by ring
    _ = _ := by rw [← Real.rpow_sub hδ]; congr 2; ring

theorem eventually_endpoint_mass_thresholds {u τ : ℝ}
    (hu : 0 < u) (hτ : 30*u < τ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      δ^(40*u) ≤ (δ^(2*u))^3/(2*(δ^(-6*u))^5) ∧
      δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3) := by
  have hb := eventually_const_mul_rpow_lt (show 24*u < τ-6*u by linarith) 12
  have hm := eventually_const_mul_rpow_lt (show 36*u < 40*u by linarith) 2
  filter_upwards [hb,hm,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hb hm hδ
  refine ⟨hδ.1,?_,?_⟩
  · rw [endpoint_common_mass_ratio hδ.1]
    linarith [hm.2]
  · rw [endpoint_bad_mass_ratio hδ.1]
    have hM : 1 ≤ δ^(-6*u) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2 (by linarith)
    have hh : δ^τ+2*δ^(-6*u)*δ^τ ≤ 3*δ^(-6*u)*δ^τ := by
      nlinarith [mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hδ.1.le τ)]
    have he : δ^(-6*u)*δ^τ = δ^(τ-6*u) := by rw [← Real.rpow_add hδ.1]; congr 1; ring
    rw [mul_assoc,he] at hh
    linarith [hb.2]

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSelectionLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One loss parameter for radial pruning, row selection and endpoint counting -/

namespace Falconer

theorem exists_endpoint_selection_losses {ε c₁ c₂ g : ℝ}
    (hε : 0 < ε) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hg : 0 < g) :
    ∃ u τ : ℝ, 0 < u ∧ 0 < τ ∧ u < ε ∧ 30*u < τ ∧
      τ+10*u < c₁ ∧ τ+10*u < c₂ ∧ 280*u < g := by
  let τ : ℝ := min c₁ c₂/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ₁ : 2*τ ≤ c₁ := by dsimp [τ]; linarith [min_le_left c₁ c₂]
  have hτ₂ : 2*τ ≤ c₂ := by dsimp [τ]; linarith [min_le_right c₁ c₂]
  let u : ℝ := min ε (min (τ/100) (g/560))/2
  have hu : 0 < u := by dsimp [u]; positivity
  have huε : 2*u ≤ ε := by dsimp [u]; linarith [min_le_left ε (min (τ/100) (g/560))]
  have huτ : 2*u ≤ τ/100 := by
    dsimp [u]
    linarith [(min_le_right ε (min (τ/100) (g/560))).trans (min_le_left (τ/100) (g/560))]
  have hug : 2*u ≤ g/560 := by
    dsimp [u]
    linarith [(min_le_right ε (min (τ/100) (g/560))).trans (min_le_right (τ/100) (g/560))]
  exact ⟨u,τ,hu,hτ,by linarith,by linarith,by linarith,by linarith,by linarith⟩

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EndpointAngularParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous scalar budgets for the endpoint angular application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem exists_endpoint_angular_parameters {ε₀ c₁ c₂ s a : ℝ}
    (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hgap : 0 < 2*s-3-6*a) (ha : a < 1/2)
    (Cm Large V Cpoint Ccover C H : ℝ) :
    ∃ u ε τ : ℝ, 0 < u ∧ 0 < ε ∧ 0 < τ ∧ ε < ε₀ ∧ ε < u ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        let δ := 1/(2:ℝ)^N
        ((N+1:ℕ):ℝ)*(Cm*δ^(-ε)) ≤ δ^(-u) ∧
        Large ≤ δ^(-u) ∧ Cpoint*δ^(-6*u) ≤ δ^(-40*u) ∧
        V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4 ∧
        δ^(40*u) ≤ (δ^(2*u))^3/(2*(δ^(-6*u))^5) ∧
        δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3) ∧
        Ccover*δ^(-1-12*u) ≤ δ^(-1-40*u) ∧
        144*H*δ ≤ 3*(δ^a)^2 ∧
        (δ^(-1-40*u))^3*((6*C+35)/δ^a)^6*(δ^(-40*u)*(6*δ)^s)^2 < (δ^(40*u))^2 := by
  obtain ⟨u,τ,hu,hτ,huε,huτ,hc₁',hc₂',hug⟩ :=
    exists_endpoint_selection_losses hε₀ hc₁ hc₂ hgap
  let ε := u/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεu : ε < u := by dsimp [ε]; linarith
  have hεε₀ : ε < ε₀ := hεu.trans huε
  have hdepth := eventually_dyadic_loss_absorption hεu Cm
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -u < 0 by linarith)).eventually
    (eventually_ge_atTop Large)
  have hcoef := eventually_const_mul_rpow_lt (show -40*u < -6*u by linarith) Cpoint
  have hbase := eventually_endpoint_row_base hu hc₁' hc₂' V
  have hmass := eventually_endpoint_mass_thresholds hu huτ
  have hcover := eventually_const_mul_rpow_lt (show -1-40*u < -1-12*u by linarith) Ccover
  have herr := eventually_const_mul_rpow_lt (show (0:ℝ) < 1-2*a by linarith) (48*H)
  have hcount := eventually_endpoint_count_budget
    (s := s) (a := a) (κ := 40*u) (by nlinarith [hug]) C
  have hready := hdepth.and (hlarge.and (hcoef.and (hbase.and (hmass.and
    (hcover.and (herr.and hcount))))))
  have hn := dyadic_inverse_tendsto.eventually hready
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hn
  refine ⟨u,ε,τ,hu,hε,hτ,hεε₀,hεu,N₀,?_⟩
  intro N hN
  rcases hN₀ N hN with ⟨hd,hL,hC,hB,hM,hT,hE,hF⟩
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨?_,hL,hC.2.le,hB.2,hM.2.1,hM.2.2,hT.2.le,?_,by simpa only [neg_mul] using hF.2⟩
  · have hh := hd.2
    rw [dyadic_log_depth N] at hh
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hh
  · have hp : δ^(1-2*a)*(δ^a)^2 = δ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le,← Real.rpow_add hδ]
      norm_num only [Nat.cast_ofNat]
      rw [show 1-2*a+a*(2:ℝ) = 1 by ring,Real.rpow_one]
    have hh := mul_lt_mul_of_pos_right hE.2 (sq_pos_of_pos (Real.rpow_pos_of_pos hδ a))
    have heq : (48*H)*δ^(1-2*a)*(δ^a)^2 = (48*H)*δ := by rw [mul_assoc,hp]
    rw [Real.rpow_zero,one_mul,heq] at hh
    nlinarith

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original direction labels in affine gnomonic coordinates -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem gnomonicCoordinates_measurable : Measurable (@gnomonicCoordinates n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  fun_prop

theorem northLift_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    northLift (gnomonicCoordinates w) = ((w:Space (n+1)) 0)⁻¹ • (w:Space (n+1)) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [northLift_zero,PiLp.smul_apply,smul_eq_mul]
    exact (inv_mul_cancel₀ hw.ne').symm
  · simp only [northLift_succ,gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
    exact mul_comm _ _

theorem gnomonicChart_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    gnomonicChart (gnomonicCoordinates w) = w := by
  apply Subtype.ext
  change ‖northLift (gnomonicCoordinates w)‖⁻¹ • northLift (gnomonicCoordinates w) = _
  rw [northLift_gnomonicCoordinates w hw,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hw),sphere_norm,mul_one,inv_inv,smul_smul]
  rw [mul_inv_cancel₀ hw.ne',one_smul]

end Falconer

/-! # Explicit inverse and cone coordinates for the gnomonic measure formula -/

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting an original direction law to its affine chart -/

namespace Falconer
open Set Metric MeasureTheory
variable {n : ℕ}

theorem gnomonicCoordinates_map_recover (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0) :
    Measure.map gnomonicChart (Measure.map gnomonicCoordinates ν) = ν := by
  rw [Measure.map_map (gnomonicChart_continuous n).measurable gnomonicCoordinates_measurable]
  calc
    _ = Measure.map id ν := Measure.map_congr (by
      filter_upwards [hν] with w hw
      exact gnomonicChart_gnomonicCoordinates w hw)
    _ = ν := Measure.map_id

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small spherical cap has bounded original affine coordinates -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

theorem gnomonic_cap_first_coordinate (w : Sphere (n+1))
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ 1/2) :
    7/8 ≤ (w:Space (n+1)) 0 := by
  have hh := norm_sub_sq_real (w:Space (n+1)) (northLift (0 : Space n))
  rw [sphere_norm,northLift_zero_norm,inner_northLift_zero] at hh
  have hd : ‖(w:Space (n+1))-northLift (0 : Space n)‖ ≤ 1/2 := by
    simpa only [Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  nlinarith [norm_nonneg ((w:Space (n+1))-northLift (0 : Space n))]

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SmallGnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small chart law lies in the unit cube used by radial pruning -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

lemma gnomonic_cap_coordinates_norm_le (w : Sphere (n+1)) {ρ : ℝ}
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ ρ) (hρ : ρ ≤ 1/2) :
    ‖gnomonicCoordinates w‖ ≤ 2*ρ := by
  have hw0 := gnomonic_cap_first_coordinate w (hw.trans hρ)
  have hp : 0 < (w:Space (n+1)) 0 := by linarith
  let v : Space (n+1) := (w:Space (n+1))-northLift 0
  let t : Space n := WithLp.toLp 2 (fun i => v i.succ)
  have ht : ‖t‖ ≤ ‖v‖ := by
    have hs : ‖t‖^2 ≤ ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
      simp only [t]
      exact le_add_of_nonneg_left (sq_nonneg (v 0))
    nlinarith [norm_nonneg t,norm_nonneg v]
  have hv : ‖v‖ ≤ ρ := by
    simpa only [v,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  have he : gnomonicCoordinates w = ((w:Space (n+1)) 0)⁻¹ • t := by
    ext i
    simp only [gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,t,
      v,PiLp.sub_apply,northLift_succ,PiLp.zero_apply,sub_zero,div_eq_mul_inv]
    ring
  have hi : ((w:Space (n+1)) 0)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact (mul_le_mul_of_nonneg_left (ht.trans hv) (inv_nonneg.mpr hp.le)).trans
    (mul_le_mul_of_nonneg_right hi (by linarith [norm_nonneg v]))

lemma small_gnomonic_cap_law (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space n)) ≤ 1/8) :
    ∀ᵐ p ∂Measure.map gnomonicCoordinates ν, ‖p‖ ≤ 1/4 := by
  rw [ae_map_iff gnomonicCoordinates_measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [hν] with w hw
  have hh := gnomonic_cap_coordinates_norm_le w hw (by norm_num : (1/8:ℝ) ≤ 1/2)
  norm_num at hh ⊢
  exact hh

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointChartGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform endpoint angular decay on a small original direction cap -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem endpoint_chart_angular_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsProbabilityMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  let s : ℝ := t-(h:ℝ)
  let a : ℝ := (2*s-3)/12
  have hs : 3/2 < s := by dsimp [s]; linarith
  have hs' : s < 2 := by dsimp [s]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have ha' : a < 1/2 := by dsimp [a]; linarith
  have hgap : 0 < 2*s-3-6*a := by dsimp [a]; linarith
  obtain ⟨ε₀,c₁,c₂,hε₀,hc₁,hc₂,Np,hprep⟩ := endpoint_spherical_preparation (h := h) hLW hζ ha
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t (h+1:ℝ)
  let Mrow : ℝ := (h+3:ℝ)*(2*ρ)+1
  let Z : ℝ := Mrow+1
  let V : ℝ := (2*Z)^h
  let a₀ : ℝ := 4+4*(h:ℝ)
  let D : ℝ := 1+2*(1/4)+C*Mrow
  let B₀ : ℝ := (2:ℝ)^h*gaussianLocalBandConstant (h+2) ρ^h
  have hMrow : 0 < Mrow := by dsimp [Mrow]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+2) hρ
    dsimp [B₀]
    positivity
  obtain ⟨u,ε,τ,hu,hε,hτ,hεε₀,hεu,Ns,hscalar⟩ :=
    exists_endpoint_angular_parameters hε₀ hc₁ hc₂ hgap ha' Cm
      (4*(1+2*(2:ℝ)^h+1)) V ((4*a₀)^s) ((2*D)^h) C (h:ℝ)
  have hcut := dyadic_inverse_tendsto.eventually
    ((eventually_const_mul_rpow_lt (show u/2 < u by linarith) (1/B₀)).and
      (Ioc_mem_nhdsGT hρ))
  obtain ⟨Nc,hcut⟩ := eventually_atTop.mp hcut
  refine ⟨ε,u/2,hε,by positivity,Np+Ns+Nc,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hν hμ hμmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-u)
  let L : ℝ := δ^(-ε)
  let Ncover : ℝ := δ^(-(h+1:ℝ)-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨habs,hδρ'⟩ := hcut N (by omega)
  have hδρ : δ ≤ ρ := hδρ'.2
  have hδ1 : δ ≤ 1 := hδρ.trans (hρsmall.trans (by norm_num))
  obtain ⟨hcard,hlarge,hcoef,hbase,hmass,hbad,hcount,herror,hbudget⟩ := hscalar N (by omega)
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 1 ≤ K := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -u ≤ 0 by linarith)
  have hCK : Cm*L ≤ K := by
    have hN1 : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left (by positivity : 0 ≤ Cm*L) hN1).trans hcard
  have hloss : L ≤ ((2:ℝ)^N)^ε₀ := by
    rw [dyadic_loss_conversion]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεε₀.le)
  have hcap : ∀ᵐ (w : Sphere (h+3)) ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8 := by
    filter_upwards [hν] with w hw
    exact hw.trans hρsmall
  obtain ⟨G,hG,hpairCost,htripleCost⟩ := hprep N (by omega) ν hcap
    (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
      (by simpa only [Nat.cast_add,Nat.cast_one] using
        (mul_le_mul_of_nonneg_right hloss
          (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) (h+1:ℝ))))))
    (fun w r hr hr1 => (hslab w r (by simpa only [one_div] using hr) hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss
        (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
  let ν₀ : Measure (Space (h+2)) := Measure.map gnomonicCoordinates ν
  have hpos : ∀ᵐ (w : Sphere (h+3)) ∂ν, 0 < (w:Space (h+3)) 0 := by
    filter_upwards [hcap] with w hw
    have hh := gnomonic_cap_first_coordinate w (hw.trans (by norm_num : (1/8:ℝ) ≤ 1/2))
    linarith
  have hνeq : Measure.map gnomonicChart ν₀ = ν := gnomonicCoordinates_map_recover ν hpos
  have hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1 := by
    filter_upwards [small_gnomonic_cap_law ν hcap] with p hp
    linarith
  have hpair : ∀ᵐ w : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
      0 ≤ inner ℝ (w.1:Space (h+3)) (w.2:Space (h+3)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcap,
      Measure.quasiMeasurePreserving_snd.ae hcap] with w hw hv
    exact sphere_chart_pair_inner_nonnegative w.1 w.2 (gnomonicChart (0 : Space (h+2)))
      (hw.trans (by norm_num)) (hv.trans (by norm_num))
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+2) (by omega)
    (sphere_norm (gnomonicChart (0 : Space (h+2))))
  have hKpow (j : ℕ) : K^j = δ^(-((j:ℝ)*u)) := gaussian_scale_power hδ j
  have hbox : volume (coordinateBox h ((1/4)*Mrow+δ)) ≤ ENNReal.ofReal V := by
    rw [coordinateBox_volume (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    change 2*((1/4)*Mrow+δ) ≤ 2*(Mrow+1)
    nlinarith
  have hpc : (∫⁻ A, endpointPairCost ν₀ δ G A
      ∂(gaussianRows (h+3) h).restrict
        (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ)))) ≤
      ENNReal.ofReal (δ^c₁) := by
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    simpa only [endpointPairCost,dyadic_inverse_rpow] using hpairCost
  have htc : (∫⁻ A, endpointTripleCost ν₀ δ (2*δ^a) G A
      ∂(gaussianRows (h+3) h).restrict
        (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ)))) ≤
      ENNReal.ofReal (δ^c₂) := by
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    simpa only [endpointTripleCost,dyadic_inverse_rpow] using htripleCost
  have hrow := endpoint_selection_row_budget hδ hV _ _ _ hbox hpc htc hbase
  have hactive := endpoint_active_cover_power hδ hδ1 hεu.le hC hρ.le hcount
  have hsmall := endpoint_stable_small hδρ hstable
  have hbad' := endpoint_bad_mass_ennreal hδ hbad
  have hcoef' : K^6*(4*a₀)^s ≤ δ^(-(40*u)) := by
    rw [hKpow]
    simpa only [Nat.cast_ofNat,neg_mul,mul_neg,mul_comm] using hcoef
  have hmass' : δ^(40*u) ≤ (δ^(2*u))^3/(2*(K^6)^5) := by
    rw [hKpow]
    simpa only [Nat.cast_ofNat,neg_mul] using hmass
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Ncover := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  have hg := controlled_endpoint_angular_gain μ ν ν₀ hνeq B (gnomonicChart (0 : Space (h+2)))
    E J v G hG hρ.le hδρ hB hν hstable hsmall hμ hν₀ hμmass (by simp)
    (by positivity : 0 ≤ L) (by positivity : 0 ≤ L) (by linarith : (h:ℝ) < t)
    hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hCP hCD hCM hcard hCK hlarge
    ha.le hC (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _)
    ha₀ le_rfl hbad' hmass' hactive hcoef' herror
    (by simpa only [neg_mul] using hbudget) hrow hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+2) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^u := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (pow_nonneg hlocal.le h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le u),mul_assoc] using hr
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^u := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs.2.le

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the retained original-label slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedSliceLaw_apply (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) :
    (normalizedSliceLaw μ hμ : Measure X) S = (μ univ)⁻¹*μ S := rfl

theorem normalizedSliceLaw_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) {L B : ℝ≥0∞}
    (hL : L ≤ μ univ) (hS : μ S ≤ B) :
    (normalizedSliceLaw μ hμ : Measure X) S ≤ L⁻¹*B := by
  rw [normalizedSliceLaw_apply]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hL) hS

theorem normalizedSliceLaw_ae (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂(normalizedSliceLaw μ hμ : Measure X), P x :=
  Measure.ae_smul_measure hP _

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointNormalize
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization costs for the endpoint direction law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedSliceLaw_power_bound (ν : Measure Y) [IsFiniteMeasure ν]
    (hν : ν univ ≠ 0) {δ σ ε q r : ℝ} (hδ : 0 < δ) (_hr : 0 ≤ r)
    (hmass : ENNReal.ofReal (δ^σ) ≤ ν univ) (S : Set Y)
    (hS : ν S ≤ ENNReal.ofReal (δ^(-ε)*r^q)) :
    (normalizedSliceLaw ν hν : Measure Y) S ≤ ENNReal.ofReal (δ^(-ε-σ)*r^q) := by
  apply (normalizedSliceLaw_bound ν hν S hmass hS).trans_eq
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ σ),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_neg hδ.le]
  calc
    _ = (δ^(-ε)*δ^(-σ))*r^q := by ring
    _ = _ := by rw [← Real.rpow_add hδ]; congr 2

theorem incidence_le_normalized_direction (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (hν : ν univ ≠ 0) (hmass : ν univ ≤ 1)
    (E : Set (X × Y)) :
    (μ.prod ν) E ≤ (μ.prod (normalizedSliceLaw ν hν : Measure Y)) E := by
  change (μ.prod ν) E ≤ (μ.prod ((ν univ)⁻¹ • ν)) E
  rw [Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul]
  have hi : 1 ≤ (ν univ)⁻¹ := by
    simpa only [inv_one] using ENNReal.inv_le_inv.mpr hmass
  simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_right hi ((μ.prod ν) E)

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSubprobability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint small-cap gain for original subprobability direction laws -/

namespace Falconer
open Set MeasureTheory Real
open scoped ENNReal

theorem endpoint_chart_subprobability_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  obtain ⟨ε₀,c₀,hε₀,hc₀,N₀,hgain⟩ := endpoint_chart_angular_gain hLW ht ht' hζ hC hρ hρsmall hstable
  let ε := ε₀/2
  let c := min ε c₀
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := lt_min hε hc₀
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hν hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hpow {p q : ℝ} (hpq : p ≤ q) : δ^q ≤ δ^p :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hpq
  by_cases hmass : ν univ ≤ ENNReal.ofReal (δ^ε)
  · calc
      (μ.prod ν) E ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = μ univ*ν univ := by rw [← univ_prod_univ,Measure.prod_prod]
      _ ≤ 1*ENNReal.ofReal (δ^ε) := mul_le_mul' hμmass hmass
      _ ≤ ENNReal.ofReal (δ^c) := by
        rw [one_mul]
        exact ENNReal.ofReal_le_ofReal (hpow (min_le_left _ _))
  · have hmass' : ENNReal.ofReal (δ^ε) ≤ ν univ := (lt_of_not_ge hmass).le
    have hν0 : ν univ ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ ε)).trans_le hmass')
    let ν' : Measure (Sphere (h+3)) := normalizedSliceLaw ν hν0
    have hnorm (S : Set (Sphere (h+3))) (r q : ℝ) (hr : 0 ≤ r)
        (hS : ν S ≤ ENNReal.ofReal (δ^(-ε)*r^q)) :
        ν' S ≤ ENNReal.ofReal (δ^(-ε₀)*r^q) := by
      have hh := normalizedSliceLaw_power_bound ν hν0 hδ hr hmass' S hS
      have he : -ε-ε = -ε₀ := by dsimp [ε]; ring
      simpa only [he] using hh
    have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
        ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε₀)*(1/(2:ℝ)^j)^(h+1:ℝ)) :=
      hnorm _ _ _ (by positivity) (hνball w j hj)
    have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
        ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal (δ^(-ε₀)*r^ζ) :=
      hnorm _ r ζ (hδ.le.trans hr) (hslab w r hr hr1)
    have hL : δ^(-ε) ≤ δ^(-ε₀) := hpow (neg_le_neg hεle)
    have hg := hgain N hN ι μ ν' E J v (normalizedSliceLaw_ae ν hν0 hν) hμ hμmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL
          (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      hν'ball hslab' hE hJ
      (fun w => (hJN w).trans (hpow (by linarith : -(h+1:ℝ)-ε₀ ≤ -(h+1:ℝ)-ε)))
      hEb hanchors hcover
    have hg' : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₀) := by
      simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
        ENNReal.ofReal_le_ofReal hg
    exact (incidence_le_normalized_direction μ ν hν0 hνmass E).trans
      (hg'.trans (ENNReal.ofReal_le_ofReal (hpow (min_le_right _ _))))

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation transport of the original point and direction laws -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

theorem sphereMap_distance (e : Space d ≃ₗᵢ[ℝ] Space d) (v w : Sphere d) :
    dist (sphereMap e v) (sphereMap e w) = dist v w := e.dist_map v w

theorem sphereMap_symm_apply (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e (sphereMap e.symm w) = w := by
  apply Subtype.ext
  exact e.apply_symm_apply w

theorem sphereMap_apply_symm (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e.symm (sphereMap e w) = w := by
  apply Subtype.ext
  exact e.symm_apply_apply w

theorem sphereMap_ball_preimage (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    sphereMap e ⁻¹' ball w r = ball (sphereMap e.symm w) r := by
  rw [← sphereMap_symm_apply e w]
  ext v
  simp only [mem_preimage,mem_ball,sphereMap_distance]
  rw [sphereMap_apply_symm e]

theorem rotated_point_ball (μ : Measure (Space d)) (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) (r : ℝ) :
    (Measure.map e μ) (ball x r) = μ (ball (e.symm x) r) := by
  rw [Measure.map_apply e.continuous.measurable measurableSet_ball]
  congr 1
  ext y
  change dist (e y) x < r ↔ dist y (e.symm x) < r
  rw [← e.apply_symm_apply x,e.dist_map,e.symm_apply_apply]

theorem rotated_direction_ball (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) (ball w r) = ν (ball (sphereMap e.symm w) r) := by
  rw [Measure.map_apply (continuous_sphereMap e).measurable measurableSet_ball,
    sphereMap_ball_preimage]

theorem rotated_direction_slab (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) {v : Sphere d | |inner ℝ (w:Space d) (v:Space d)| ≤ r} =
      ν {v : Sphere d | |inner ℝ (sphereMap e.symm w:Space d) (v:Space d)| ≤ r} := by
  have hm : MeasurableSet {v : Sphere d | |inner ℝ (w:Space d) (v:Space d)| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.map_apply (continuous_sphereMap e).measurable hm]
  congr 1
  ext v
  change |inner ℝ (w:Space d) (e (v:Space d))| ≤ r ↔ |inner ℝ (e.symm (w:Space d)) (v:Space d)| ≤ r
  rw [← e.inner_map_map (e.symm (w:Space d)) (v:Space d),e.apply_symm_apply]

theorem rotated_perpendicular_norm (e : Space d ≃ₗᵢ[ℝ] Space d) (w x a : Space d) :
    ‖perpendicularPart (e w) (e x-e a)‖ = ‖perpendicularPart w (x-a)‖ := by
  calc
    _ = ‖e (perpendicularPart w (x-a))‖ := by
      congr 1
      simp only [perpendicularPart,map_sub,map_smul,inner_sub_right,e.inner_map_map]
    _ = _ := e.norm_map _

theorem rotated_incidence (μ : Measure (Space d)) (ν : Measure (Sphere d))
    [SFinite μ] [SFinite ν] (e : Space d ≃ₗᵢ[ℝ] Space d)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    ((Measure.map e μ).prod (Measure.map (sphereMap e) ν))
      ((Prod.map e.symm (sphereMap e.symm)) ⁻¹' E) = (μ.prod ν) E := by
  have he := e.continuous.measurable
  have hw := (continuous_sphereMap e).measurable
  have hE' := hE.preimage (e.symm.continuous.measurable.prodMap
    (continuous_sphereMap e.symm).measurable)
  rw [Measure.map_prod_map μ ν he hw,Measure.map_apply (he.prodMap hw) hE']
  congr 1
  ext p
  change (e.symm (e p.1),sphereMap e.symm (sphereMap e p.2)) ∈ E ↔ p ∈ E
  rw [e.symm_apply_apply,sphereMap_apply_symm]

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedTubeData
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation of the original measurable tube relation and its finite labels -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι : Type*}

theorem rotatedTubeRelation_measurable (e : Space d ≃ₗᵢ[ℝ] Space d)
    {E : Set (Space d × Sphere d)} (hE : MeasurableSet E) :
    MeasurableSet (rotatedTubeRelation e E) :=
  hE.preimage (e.symm.continuous.measurable.prodMap (continuous_sphereMap e.symm).measurable)

theorem rotatedTubeRelation_point_bound (e : Space d ≃ₗᵢ[ℝ] Space d)
    {E : Set (Space d × Sphere d)} {D : ℝ} (hE : ∀ u ∈ E, ‖u.1‖ ≤ D) :
    ∀ u ∈ rotatedTubeRelation e E, ‖u.1‖ ≤ D := by
  intro u hu
  have hh := hE _ hu
  change ‖e.symm u.1‖ ≤ D at hh
  simpa only [e.symm.norm_map] using hh

theorem rotatedTubeRelation_cover [DecidableEq ι]
    (e : Space d ≃ₗᵢ[ℝ] Space d) {E : Set (Space d × Sphere d)}
    (J : Sphere d → Finset ι) (v : ι → Space d) {r : ℝ}
    (hE : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-v i)‖ ≤ r) :
    ∀ u ∈ rotatedTubeRelation e E, ∃ i ∈ J (sphereMap e.symm u.2),
      ‖perpendicularPart (u.2:Space d) (u.1-e (v i))‖ ≤ r := by
  intro u hu
  obtain ⟨i,hi,hp⟩ := hE _ hu
  refine ⟨i,hi,?_⟩
  have he := rotated_perpendicular_norm e (e.symm (u.2:Space d)) (e.symm u.1) (v i)
  rw [e.apply_symm_apply,e.apply_symm_apply] at he
  rw [he]
  exact hp

theorem rotated_point_norm_ae (μ : Measure (Space d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    ∀ᵐ x ∂Measure.map e μ, ‖x‖ ≤ D := by
  rw [ae_map_iff e.continuous.measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  simpa only [e.norm_map] using hμ

theorem rotated_direction_cap_ae (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) {w₀ : Sphere d} {ρ : ℝ}
    (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ) :
    ∀ᵐ w ∂Measure.map (sphereMap e) ν, dist w (sphereMap e w₀) ≤ ρ := by
  rw [ae_map_iff (continuous_sphereMap e).measurable.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  simpa only [sphereMap_distance] using hν

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointOrientedGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint small-cap estimate in every orientation -/

namespace Falconer
open Set MeasureTheory Real
open scoped ENNReal

theorem endpoint_oriented_chart_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (w₀ : Sphere (h+3)) (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  obtain ⟨ε,c,hε,hc,N₀,hgain⟩ := endpoint_chart_subprobability_gain hLW ht ht' hζ hC hρ hρsmall hstable
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN ι _ _ μ ν _ _ w₀ E J v hν hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let north : Sphere (h+3) := gnomonicChart (0 : Space (h+2))
  let e : Space (h+3) ≃ₗᵢ[ℝ] Space (h+3) :=
    (ℝ ∙ ((w₀:Space (h+3))-(north:Space (h+3))))ᗮ.reflection
  have he : sphereMap e w₀ = north := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((sphere_norm w₀).trans (sphere_norm north).symm)
  let μ' := Measure.map e μ
  let ν' := Measure.map (sphereMap e) ν
  let E' := rotatedTubeRelation e E
  let J' : Sphere (h+3) → Finset ι := fun w => J (sphereMap e.symm w)
  let v' : ι → Space (h+3) := fun i => e (v i)
  have hν' : ∀ᵐ w ∂ν', dist w north ≤ ρ := by
    rw [← he]
    exact rotated_direction_cap_ae ν e hν
  have hμ'mass : μ' univ ≤ 1 := by
    simpa only [μ',Measure.map_apply e.continuous.measurable MeasurableSet.univ,preimage_univ] using hμmass
  have hν'mass : ν' univ ≤ 1 := by
    simpa only [ν',Measure.map_apply (continuous_sphereMap e).measurable MeasurableSet.univ,preimage_univ] using hνmass
  have hμ'ball (x : Space (h+3)) (j : ℕ) (hj : j ≤ N) :
      μ' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    rw [rotated_point_ball]
    exact hμball _ j hj
  have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ)) := by
    rw [rotated_direction_ball]
    exact hνball _ j hj
  have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ) := by
    rw [rotated_direction_slab]
    exact hslab _ r hr hr1
  have hg := hgain N hN ι μ' ν' E' J' v' hν' (rotated_point_norm_ae μ e hμ)
    hμ'mass hν'mass hμ'ball hν'ball hslab' (rotatedTubeRelation_measurable e hE)
    (fun i => (hJ i).preimage (continuous_sphereMap e.symm).measurable)
    (fun w => hJN (sphereMap e.symm w)) (rotatedTubeRelation_point_bound e hEb)
    (fun w i hi => by simpa only [v',e.norm_map] using hanchors (sphereMap e.symm w) i hi)
    (rotatedTubeRelation_cover e J v hcover)
  have hmass : (μ'.prod ν') E' = (μ.prod ν) E := rotated_incidence μ ν e E hE
  rw [hmass] at hg
  exact hg

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointChartRadius
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed small cap for the three-dimensional endpoint slice -/

namespace Falconer

theorem exists_endpoint_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/8 ∧ (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2 := by
  obtain ⟨r,hr,_,hst,_⟩ := exists_small_gaussian_chart_radius (h+1)
  have hcast : ((h+1:ℕ):ℝ)+2 = (h+3:ℝ) := by push_cast; ring
  rw [hcast] at hst
  refine ⟨min r (1/8),lt_min hr (by norm_num),min_le_right _ _,?_⟩
  have hh : (h:ℝ)*((h+3:ℝ)*(2*r)) ≤ ((h+1:ℕ):ℝ)*((h+3:ℝ)*(2*r)) :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity)
  apply le_trans _ (hh.trans hst)
  gcongr
  exact min_le_left _ _

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EndpointAngularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform endpoint angular gain in every ambient dimension h+3 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem endpoint_dyadic_angular_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρsmall,hstable⟩ := exists_endpoint_chart_radius h
  obtain ⟨ε,c₁,hε,hc₁,N₁,hgain⟩ := endpoint_oriented_chart_gain hLW ht ht' hζ hC hρ hρsmall hstable
  let H : ℝ := (2/ρ+1)^(h+3)
  let c : ℝ := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := dyadic_inverse_tendsto.eventually
    (eventually_const_mul_rpow_lt (show c < c₁ by dsimp [c]; linarith) H)
  obtain ⟨N₂,habs⟩ := eventually_atTop.mp habs
  refine ⟨ε,c,hε,hc,N₁+N₂,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hH : H*δ^c₁ ≤ δ^c := (habs N (by omega)).2.le
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ)) :=
    (Measure.restrict_le_self _).trans (hνball w j hj)
  have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
      ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
        ENNReal.ofReal (δ^(-ε)*r^ζ) :=
    (Measure.restrict_le_self _).trans (hslab w r hr hr1)
  have hg := hgain N (by omega) ι μ ν' w₀ E J v hνsupport hμ hμmass hν'mass
    hμball hν'ball hslab' hE hJ hJN hEb hanchors hcover
  exact (not_lt_of_ge hg) hw₀

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EndpointTubeGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem endpoint_dyadic_tube_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (hC : 0 ≤ C) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ E : Set (Space (h+3) × Sphere (h+3)),
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
      (∀ w : Sphere (h+3), ∃ S : Finset (Space (h+3)),
        (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε) ∧
        ∀ x, (x,w) ∈ E → ∃ a ∈ S,
          ‖perpendicularPart (w:Space (h+3)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,hε,hc,N₀,hgain⟩ := endpoint_dyadic_angular_gain hLW ht ht' hζ
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ ν _ _ E hμ hμmass hνmass hμball hνball hslab hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-(h+1:ℝ)-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N hN {a // a ∈ G} μ ν F J (fun a => a.val)
    hμ hμmass hνmass hμball hνball hslab hF hJ ?_
    (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-(h+1:ℝ)-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteHolder
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The equal-exponent finite Hölder inequality for coordinate deletion

This is the finite sum inequality needed in the induction proving the exact
lattice Loomis–Whitney input. It follows from weighted arithmetic–geometric
mean after normalizing each row by its actual sum.
-/
namespace Falconer
open scoped BigOperators

variable {ι α : Type*}

theorem finite_holder_equal (I : Finset ι) (B : Finset α) (hI : I.Nonempty)
    (f : ι → α → ℝ) (hf : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ f i x) :
    (∑ x ∈ B, ∏ i ∈ I, (f i x) ^ (1/(I.card:ℝ))) ≤
      ∏ i ∈ I, (∑ x ∈ B, f i x) ^ (1/(I.card:ℝ)) := by
  classical
  let p : ℝ := 1/(I.card:ℝ)
  let M : ι → ℝ := fun i => ∑ x ∈ B, f i x
  have hcard : 0 < (I.card:ℝ) := by exact_mod_cast hI.card_pos
  have hp : 0 < p := one_div_pos.mpr hcard
  have hweights : ∑ _i ∈ I, p = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul,p]
    exact mul_one_div_cancel hcard.ne'
  have hMnonneg : ∀ i ∈ I, 0 ≤ M i := fun i hi =>
    Finset.sum_nonneg (fun x hx => hf i hi x hx)
  by_cases hM : ∀ i ∈ I, 0 < M i
  · let g : ι → α → ℝ := fun i x => f i x / M i
    have hg : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ g i x :=
      fun i hi x hx => div_nonneg (hf i hi x hx) (hMnonneg i hi)
    have hgsum : ∀ i ∈ I, ∑ x ∈ B, g i x = 1 := by
      intro i hi
      simp only [g,← Finset.sum_div,M]
      exact div_self (hM i hi).ne'
    have hmean : ∀ x ∈ B, (∏ i ∈ I, (g i x)^p) ≤ ∑ i ∈ I, p*g i x := by
      intro x hx
      exact Real.geom_mean_le_arith_mean_weighted I (fun _ => p) (fun i => g i x)
        (fun _ _ => hp.le) hweights (fun i hi => hg i hi x hx)
    have hsum : (∑ x ∈ B, ∏ i ∈ I, (g i x)^p) ≤ 1 := by
      calc
        _ ≤ ∑ x ∈ B, ∑ i ∈ I, p*g i x := Finset.sum_le_sum hmean
        _ = ∑ i ∈ I, p*(∑ x ∈ B, g i x) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
        _ = 1 := by
          calc
            _ = ∑ i ∈ I, p := Finset.sum_congr rfl (fun i hi => by rw [hgsum i hi,mul_one])
            _ = 1 := hweights
    have hprod : ∀ x ∈ B, (∏ i ∈ I, (f i x)^p) =
        (∏ i ∈ I, (M i)^p)*(∏ i ∈ I, (g i x)^p) := by
      intro x hx
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      change (f i x)^p = (M i)^p*(f i x/M i)^p
      rw [Real.div_rpow (hf i hi x hx) (hMnonneg i hi)]
      have hne : (M i)^p ≠ 0 := (Real.rpow_pos_of_pos (hM i hi) _).ne'
      field_simp
    change (∑ x ∈ B, ∏ i ∈ I, (f i x)^p) ≤ ∏ i ∈ I, (M i)^p
    calc
      _ = (∏ i ∈ I, (M i)^p)*(∑ x ∈ B, ∏ i ∈ I, (g i x)^p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hprod
      _ ≤ (∏ i ∈ I, (M i)^p)*1 :=
        mul_le_mul_of_nonneg_left hsum (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hMnonneg i hi) _))
      _ = _ := mul_one _
  · push Not at hM
    obtain ⟨i,hi,hMi⟩ := hM
    have hzero : M i = 0 := le_antisymm hMi (hMnonneg i hi)
    have hrow : ∀ x ∈ B, f i x = 0 := by
      intro x hx
      apply le_antisymm _ (hf i hi x hx)
      calc
        f i x ≤ ∑ y ∈ B, f i y := Finset.single_le_sum (fun y hy => hf i hi y hy) hx
        _ = 0 := hzero
    have hleft : (∑ x ∈ B, ∏ j ∈ I, (f j x)^p) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.prod_eq_zero hi
      rw [hrow x hx,Real.zero_rpow hp.ne']
    change (∑ x ∈ B, ∏ i ∈ I, (f i x)^p) ≤ ∏ i ∈ I, (M i)^p
    rw [hleft]
    exact Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hMnonneg j hj) _)

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LoomisWhitneyCoordinates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coordinate splitting for the Loomis–Whitney induction -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem sum_tuple_cons {n : ℕ} (f : (Fin (n+1) → X) → ℝ) :
    (∑ z, f z) = ∑ x, ∑ y : Fin n → X, f (Fin.cons x y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp f]
  exact Fintype.sum_prod_type _

omit [Fintype X] in
theorem finite_holder_two_successor {n : ℕ} (B : Finset X) (f g : X → ℝ)
    (hf : ∀ x ∈ B, 0 ≤ f x) (hg : ∀ x ∈ B, 0 ≤ g x) :
    (∑ x ∈ B, (f x)^(1/((n+1:ℕ):ℝ))*(g x)^((n:ℝ)/(n+1:ℕ))) ≤
      (∑ x ∈ B, f x)^(1/((n+1:ℕ):ℝ))*(∑ x ∈ B, g x)^((n:ℝ)/(n+1:ℕ)) := by
  classical
  let h : Fin (n+1) → X → ℝ := Fin.cases f (fun _ => g)
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin (n+1))), ∀ x ∈ B, 0 ≤ h i x := by
    intro i _ x hx
    refine Fin.cases (hf x hx) (fun _ => hg x hx) i
  have hc := finite_holder_equal Finset.univ B (by simp) h hh
  have hp (u v : ℝ) (hv : 0 ≤ v) :
      (∏ i : Fin (n+1), (Fin.cases u (fun _ => v) i)^(1/((n+1:ℕ):ℝ))) =
        u^(1/((n+1:ℕ):ℝ))*v^((n:ℝ)/(n+1:ℕ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← Real.rpow_mul_natCast hv]
    congr 2
    push_cast
    ring
  have hleft : (∑ x ∈ B, ∏ i : Fin (n+1), h i x^(1/((n+1:ℕ):ℝ))) =
      ∑ x ∈ B, f x^(1/((n+1:ℕ):ℝ))*g x^((n:ℝ)/(n+1:ℕ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← hp (f x) (g x) (hg x hx)]
    apply Finset.prod_congr rfl
    intro i _
    refine Fin.cases rfl (fun _ => rfl) i
  have hright : (∏ i : Fin (n+1), (∑ x ∈ B, h i x)^(1/((n+1:ℕ):ℝ))) =
      (∑ x ∈ B, f x)^(1/((n+1:ℕ):ℝ))*(∑ x ∈ B, g x)^((n:ℝ)/(n+1:ℕ)) := by
    have he : (fun i : Fin (n+1) => ∑ x ∈ B, h i x) =
        Fin.cases (∑ x ∈ B, f x) (fun _ => ∑ x ∈ B, g x) := by
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    change (∏ i : Fin (n+1), ((fun i => ∑ x ∈ B, h i x) i)^(1/((n+1:ℕ):ℝ))) = _
    rw [he]
    exact hp _ _ (Finset.sum_nonneg hg)
  simpa only [Finset.card_univ,Fintype.card_fin,hleft,hright] using hc

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeightedLoomisStep
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite weighted Loomis–Whitney induction step -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finite_root_product_raise {ι : Type*} (I : Finset ι) {n : ℕ} (hn : 0 < n)
    (b : ι → ℝ) (hb : ∀ i ∈ I, 0 ≤ b i) :
    (∏ i ∈ I, (b i)^(1/(n:ℝ)))^((n:ℝ)/((n+1:ℕ):ℝ)) =
      ∏ i ∈ I, (b i)^(1/((n+1:ℕ):ℝ)) := by
  rw [← Real.finsetProd_rpow I _ (fun i hi => Real.rpow_nonneg (hb i hi) _) _]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Real.rpow_mul (hb i hi)]
  congr 1
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem finite_weighted_loomis_step {n : ℕ} (hn : 0 < n)
    (ih : FiniteWeightedLoomis n X) : FiniteWeightedLoomis (n+1) X := by
  classical
  intro f hf
  let g : Fin (n+1) → (Fin n → X) → ℝ := fun i y => ∑ x : X, f i.succ (Fin.cons x y)
  have hg : ∀ i y, 0 ≤ g i y := fun i y => Finset.sum_nonneg (fun x _ => hf _ _)
  let H : (Fin (n+1) → X) → ℝ := fun y => ∏ i : Fin (n+1), (g i (eraseFinCoordinate i y))^(1/(n:ℝ))
  have hH : ∀ y, 0 ≤ H y := fun y => Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hg _ _) _)
  let p : ℝ := 1/((n+1:ℕ):ℝ)
  let q : ℝ := (n:ℝ)/((n+1:ℕ):ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hh : (∑ y, H y) ≤ ∏ i : Fin (n+1), (∑ z, g i z)^(1/(n:ℝ)) := ih g hg
  have hfirst :
      (∑ z : Fin (n+2) → X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i z))^p) ≤
        ∑ y : Fin (n+1) → X, (f 0 y)^p*(H y)^q := by
    rw [sum_tuple_cons,Finset.sum_comm]
    apply Finset.sum_le_sum
    intro y _
    have he : (∑ x : X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i (Fin.cons x y)))^p) =
        (f 0 y)^p*(∑ x : X, ∏ i : Fin (n+1), (f i.succ (Fin.cons x (eraseFinCoordinate i y)))^p) := by
      simp only [Fin.prod_univ_succ,remove_coordinate_cons_zero,remove_coordinate_cons_succ,
        Finset.mul_sum]
    rw [he]
    have hc := finite_holder_equal (Finset.univ : Finset (Fin (n+1)))
      (Finset.univ : Finset X) (by simp)
      (fun i x => f i.succ (Fin.cons x (eraseFinCoordinate i y))) (fun i _ x _ => hf _ _)
    have hr : (∏ i : Fin (n+1), (g i (eraseFinCoordinate i y))^p) = (H y)^q :=
      (finite_root_product_raise Finset.univ hn _ (fun i _ => hg _ _)).symm
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hf _ _) _)
    rw [← hr]
    simpa only [Finset.card_univ,Fintype.card_fin,p,g] using hc
  have houter := finite_holder_two_successor (n := n) (Finset.univ : Finset (Fin (n+1) → X))
    (f 0) H (fun y _ => hf _ _) (fun y _ => hH y)
  have hraise := Real.rpow_le_rpow (Finset.sum_nonneg (fun y _ => hH y)) hh hq
  have hgSum (i : Fin (n+1)) : (∑ z : Fin n → X, g i z) = ∑ y : Fin (n+1) → X, f i.succ y := by
    rw [sum_tuple_cons]
    exact Finset.sum_comm
  have hraise' : (∑ y, H y)^q ≤ ∏ i : Fin (n+1), (∑ y, f i.succ y)^p := by
    apply hraise.trans_eq
    rw [finite_root_product_raise Finset.univ hn _ (fun i _ => Finset.sum_nonneg (fun y _ => hg _ _))]
    apply Finset.prod_congr rfl
    intro i _
    rw [hgSum]
  change (∑ z : Fin (n+2) → X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i z))^p) ≤
    ∏ i : Fin (n+2), (∑ y : Fin (n+1) → X, f i y)^p
  apply hfirst.trans
  apply houter.trans
  rw [Fin.prod_univ_succ]
  exact mul_le_mul_of_nonneg_left hraise' (Real.rpow_nonneg (Finset.sum_nonneg (fun y _ => hf _ _)) _)

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeightedLoomisBase
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Base and induction for the finite weighted projection inequality -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finite_weighted_loomis_one : FiniteWeightedLoomis 1 X := by
  classical
  intro f _hf
  simp only [Nat.cast_one,div_one,Real.rpow_one]
  change (∑ z : Fin 2 → X, ∏ i : Fin 2, f i (eraseFinCoordinate i z)) ≤
    ∏ i : Fin 2, ∑ y : Fin 1 → X, f i y
  simp only [Fin.prod_univ_two]
  have he : (∑ z : Fin 2 → X, f 0 (eraseFinCoordinate 0 z)*f 1 (eraseFinCoordinate 1 z)) =
      ∑ w : (Fin 1 → X) × (Fin 1 → X), f 0 w.1*f 1 w.2 := by
    rw [← (twoCoordinateEquiv (X := X)).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro w _
    have hh := (twoCoordinateEquiv (X := X)).apply_symm_apply w
    exact congrArg (fun z : (Fin 1 → X) × (Fin 1 → X) => f 0 z.1*f 1 z.2) hh
  rw [he,Fintype.sum_prod_type]
  exact le_of_eq (by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro y _; rw [Finset.mul_sum])

theorem finite_weighted_loomis_whitney (n : ℕ) (hn : 1 ≤ n) : FiniteWeightedLoomis n X := by
  induction n,hn using Nat.le_induction with
  | base => exact finite_weighted_loomis_one
  | succ n hn ih => exact finite_weighted_loomis_step (by omega) ih

end Falconer

end OAI
end



section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteLatticeLoomis
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite lattice Loomis–Whitney inequality used in the manuscript -/
namespace Falconer
open scoped BigOperators

theorem finite_loomis_whitney_card {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin (n+1) → X)) :
    S.card^n ≤ ∏ i : Fin (n+1), (S.image (eraseFinCoordinate i)).card := by
  classical
  let f : Fin (n+1) → (Fin n → X) → ℝ := fun i y =>
    if y ∈ S.image (eraseFinCoordinate i) then 1 else 0
  have hf : ∀ i y, 0 ≤ f i y := by intro i y; dsimp [f]; positivity
  have hpoint : ∀ z : Fin (n+1) → X,
      (if z ∈ S then (1:ℝ) else 0) ≤ ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ)) := by
    intro z
    by_cases hz : z ∈ S
    · have hm : ∀ i : Fin (n+1), eraseFinCoordinate i z ∈ S.image (eraseFinCoordinate i) :=
        fun i => Finset.mem_image.mpr ⟨z,hz,rfl⟩
      simp only [hz,ite_true, if_true,f,hm,Real.one_rpow,Finset.prod_const_one,le_refl]
    · simp only [hz,ite_false, if_false]
      exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hf _ _) _)
  have hcount : (S.card:ℝ) ≤
      ∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ)^(1/(n:ℝ)) := by
    calc
      _ = ∑ z : Fin (n+1) → X, if z ∈ S then (1:ℝ) else 0 := by simp
      _ ≤ ∑ z : Fin (n+1) → X, ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ)) :=
        Finset.sum_le_sum (fun z _ => hpoint z)
      _ ≤ ∏ i : Fin (n+1), (∑ y : Fin n → X, f i y)^(1/(n:ℝ)) :=
        finite_weighted_loomis_whitney n hn f hf
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        change (∑ y : Fin n → X, if y ∈ S.image (eraseFinCoordinate i) then (1:ℝ) else 0) = _
        simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hcount n
  have hright : (∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ)^(1/(n:ℝ)))^n =
      ∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  rw [hright] at hpower
  exact_mod_cast hpower

theorem published_finite_loomis_whitney : PublishedFiniteLoomisWhitney := by
  classical
  intro n hn S
  let A : Finset ℤ := S.biUnion (fun z => Finset.univ.image z)
  have hA : ∀ z ∈ S, ∀ i : Fin (n+1), z i ∈ A := by
    intro z hz i
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let lift : {z // z ∈ S} → (Fin (n+1) → A) := fun z i => ⟨z.val i,hA z.val z.property i⟩
  let T := S.attach.image lift
  have hlift : Function.Injective lift := by
    intro z w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hcard : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  have hproj : ∀ i : Fin (n+1), (T.image (eraseFinCoordinate i)).card =
      (S.image (dropGridCoordinate i)).card := by
    intro i
    let lower : (Fin n → A) → (Fin n → ℤ) := fun z j => (z j).val
    have hlower : Function.Injective lower := by
      intro z w he
      funext j
      exact Subtype.ext (congrFun he j)
    rw [← Finset.card_image_of_injective _ hlower]
    congr 1
    dsimp only [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun z => dropGridCoordinate i z.val) = _
    calc
      _ = (S.attach.image Subtype.val).image (dropGridCoordinate i) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val) (g := dropGridCoordinate i)).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hh := finite_loomis_whitney_card n hn T
  rw [hcard] at hh
  simpa only [hproj] using hh

end Falconer

end OAI
end




open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace Topology

namespace OAI.Falconer.LinearProjectionGainPartial

/-- A slab around a unit normal lies in the corresponding hyperplane neighborhood. -/
theorem slab_subset_plate {k : ℕ} (w : Direction k) (r : ℝ) :
    {v : Direction k | |inner ℝ (w : Point k) (v : Point k)| ≤ r} ⊆
    {v | Metric.infDist (v : Point k) ((ℝ ∙ (w : Point k))ᗮ : Set (Point k)) ≤ r} := by
  intro v hv
  let y : Point k := (v : Point k) - inner ℝ (w : Point k) (v : Point k) • (w : Point k)
  have hw : ‖(w : Point k)‖ = 1 := by simpa using w.property
  have hy : y ∈ (ℝ ∙ (w : Point k))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [y, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hw]
  have hd : dist (v : Point k) y = |inner ℝ (w : Point k) (v : Point k)| := by
    rw [dist_eq_norm]
    simp [y, norm_smul, hw, Real.norm_eq_abs]
  exact (Metric.infDist_le_dist_of_mem hy).trans (hd.trans_le hv)

theorem unit_dyadic_gain
    (k : ℕ) (hk : 2 ≤ k) (q t : ℝ)
    (hq : (k : ℝ) - 1 ≤ q) (hq' : q ≤ (k : ℝ) - 1 / 2)
    (ht : (k : ℝ) - 1 / 2 < t) (ht' : t < (k : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (ζ : ℝ) (hζ : q = (k : ℝ) - 1 → 0 < ζ) :
    UnitDyadicGain k q t C ζ := by
  obtain ⟨h, hkEq⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm] at hkEq
  subst k
  have hcast : ((h + 2 : ℕ) : ℝ) = (h : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hq hq' ht ht' hζ
  by_cases he : q = (h : ℝ) + 1
  · have hz : 0 < ζ := hζ (by linarith)
    obtain ⟨ε, c, hε, hc, N₀, hg⟩ := endpoint_dyadic_tube_gain
      published_finite_loomis_whitney (h := h) (t := t) (ζ := ζ) (C := C)
      (by linarith) (by linarith) hz hC
    refine ⟨ε, hε, c, hc, (1 / 2 : ℝ) ^ N₀, by positivity, ?_⟩
    intro N hN μ ν hl E hE hEb hcov
    obtain ⟨hm, hn, hs, hmb, hnb, hp⟩ := hl
    letI : IsFiniteMeasure μ := ⟨hm.trans_lt (by simp)⟩
    letI : IsFiniteMeasure ν := ⟨hn.trans_lt (by simp)⟩
    have hN₀ : N₀ ≤ N := by
      by_contra hh
      have hh' : N ≤ N₀ := by omega
      have hh'' := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hh'
      exact (not_lt_of_ge hh'') hN
    have hdim (w : Direction (h + 2)) :
        Module.finrank ℝ (ℝ ∙ (w : Point (h + 2)))ᗮ = h + 2 := by
      letI : Fact (Module.finrank ℝ (Point (h + 2)) = (h + 2) + 1) := ⟨by simp [Point]⟩
      apply Submodule.finrank_orthogonal_span_singleton
      have hw : ‖(w : Point (h + 2))‖ = 1 := by simpa using w.property
      exact norm_ne_zero_iff.mp (by rw [hw]; norm_num)
    have hg' := hg N hN₀ μ ν E hs hm hn
      (fun x j hj => by
        simpa only [one_div, inv_pow] using hmb x ((1 / 2 : ℝ) ^ j)
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)
          (pow_le_one₀ (by norm_num) (by norm_num)))
    rw [show (1 / 2 : ℝ) ^ N = 1 / (2 : ℝ) ^ N by simp [div_pow]]
    apply hg'
    · intro w j hj
      simpa only [he, one_div, inv_pow] using hnb w ((1 / 2 : ℝ) ^ j)
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)
        (pow_le_one₀ (by norm_num) (by norm_num))
    · intro w r hr hr1
      apply (measure_mono (slab_subset_plate w r)).trans
      simpa only [one_div, inv_pow] using
        (hp (by rw [he, hcast]; ring) _ (hdim w) r
          (by simpa only [one_div, inv_pow] using hr) hr1)
    · exact hE
    · exact hEb
    · intro w
      obtain ⟨A, hA, hAc⟩ := hcov w
      refine ⟨A, by simpa only [he, one_div, inv_pow] using hA, ?_⟩
      intro x hx
      obtain ⟨a, ha, hxa⟩ := hAc x hx
      refine ⟨a, ha, ?_⟩
      change ‖((ℝ ∙ (w : Point (h + 2)))ᗮ.orthogonalProjectionOnto (x - a) :
        Point (h + 2))‖ ≤ C * ((1 / 2 : ℝ) ^ N) at hxa
      rw [perpendicular_projection_formula] at hxa
      simpa only [perpendicularPart, one_div, inv_pow] using hxa
  · have hqgt : (h : ℝ) + 1 < q := by
      apply lt_of_not_ge
      intro hle
      apply he
      linarith
    obtain ⟨ε, c, d, hε, hc, hd, hg⟩ := nonendpoint_dyadic_tube_gain
      publishedPlanarFurstenberg_proved (h := h + 1) (t := t) (q := q) (C := C)
      (by push_cast; linarith) (by push_cast; linarith)
      (by linarith) (by push_cast; linarith) hC
    refine ⟨ε, hε, c, hc, d, hd, ?_⟩
    intro N hN μ ν hl E hE hEb hcov
    obtain ⟨hm, hn, hs, hmb, hnb, _⟩ := hl
    letI : IsFiniteMeasure μ := ⟨hm.trans_lt (by simp)⟩
    letI : IsFiniteMeasure ν := ⟨hn.trans_lt (by simp)⟩
    rw [show (1 / 2 : ℝ) ^ N = 1 / (2 : ℝ) ^ N by simp [div_pow]]
    apply hg N μ ν E (by simpa only [one_div, inv_pow] using hN) hs hm hn
    · intro x j hj
      simpa only [one_div, inv_pow] using hmb x ((1 / 2 : ℝ) ^ j)
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)
        (pow_le_one₀ (by norm_num) (by norm_num))
    · intro w j hj
      simpa only [one_div, inv_pow] using hnb w ((1 / 2 : ℝ) ^ j)
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)
        (pow_le_one₀ (by norm_num) (by norm_num))
    · exact hE
    · exact hEb
    · intro w
      obtain ⟨A, hA, hAc⟩ := hcov w
      refine ⟨A, by simpa only [one_div, inv_pow] using hA, ?_⟩
      intro x hx
      obtain ⟨a, ha, hxa⟩ := hAc x hx
      refine ⟨a, ha, ?_⟩
      change ‖((ℝ ∙ (w : Point (h + 2)))ᗮ.orthogonalProjectionOnto (x - a) :
        Point (h + 2))‖ ≤ C * ((1 / 2 : ℝ) ^ N) at hxa
      rw [perpendicular_projection_formula] at hxa
      simpa only [perpendicularPart, one_div, inv_pow] using hxa

end OAI.Falconer.LinearProjectionGainPartial


open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace OAI.Falconer.LinearProjectionGainPartial

/-- A positive loss margin absorbs the fixed factor in replacing a real scale
by a comparable larger scale. -/
theorem input_scale_slack (p η ε : ℝ) (hεη : ε < η) (hpη : 0 ≤ p + η) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ u : ℝ, 0 < δ → δ < d →
      0 < u → u ≤ 2 * δ → δ ^ (-p - ε) ≤ u ^ (-p - η) := by
  have hlim : Tendsto (fun δ : ℝ => δ ^ (η - ε)) (𝓝 0) (𝓝 0) :=
    tendsto_id.rpow_const_nhds_zero (sub_pos.mpr hεη)
  have hev : ∀ᶠ δ : ℝ in 𝓝 0, δ ^ (η - ε) < (2 : ℝ) ^ (-p - η) :=
    hlim.eventually (gt_mem_nhds (Real.rpow_pos_of_pos (by norm_num) _))
  obtain ⟨d, hd, hbound⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨d, hd, fun δ u hδ hδd hu huδ => ?_⟩
  have hb := hbound (y := δ) (by simpa [Real.dist_eq, abs_of_pos hδ] using hδd)
  calc
    δ ^ (-p - ε) = δ ^ (-p - η) * δ ^ (η - ε) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    _ ≤ δ ^ (-p - η) * (2 : ℝ) ^ (-p - η) :=
      mul_le_mul_of_nonneg_left hb.le (Real.rpow_nonneg hδ.le _)
    _ = (2 * δ) ^ (-p - η) := by rw [Real.mul_rpow (by norm_num) hδ.le, mul_comm]
    _ ≤ u ^ (-p - η) := Real.rpow_le_rpow_of_nonpos hu huδ (by linarith)

/-- The still-missing local bridge can be restricted to dyadic scales. -/
def DyadicSmallCapGain (k : ℕ) (q t C R ζ : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ N : ℕ, (1 / 2 : ℝ) ^ N < δ₀ →
    ∀ (μ : Measure (Point k)) (ν : Measure (Direction k)),
    Laws k q t R ζ ε ((1 / 2 : ℝ) ^ N) μ ν →
    ∀ (w₀ : Direction k) (E : Set (Point k × Direction k)),
    NullMeasurableSet E (μ.prod ν) → FiberCover k q C ε ((1 / 2 : ℝ) ^ N) E →
    (∀ u ∈ E, dist u.2 w₀ ≤ ρ) →
    (μ.prod ν) E ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ N) ^ c)

/-- Exact missing bridge type. In particular there is no assertion that the
endpoint's pair and triple budgets are automatic from the controlled node. -/
def DyadicSmallCapBridge : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ q t : ℝ,
    (k : ℝ) - 1 ≤ q → q ≤ (k : ℝ) - 1 / 2 →
    (k : ℝ) - 1 / 2 < t → t < (k : ℝ) →
    ∀ C : ℝ, 0 ≤ C → ∀ R : ℝ, 0 ≤ R →
    ∀ ζ : ℝ, (q = (k : ℝ) - 1 → 0 < ζ) → DyadicSmallCapGain k q t C R ζ

/-- Transfer all three ball/plate bounds to a larger comparable scale, using
only a comparison of the multiplicative loss. -/
theorem laws_change_scale {k : ℕ} {q t R ζ ε η δ u : ℝ}
    {μ : Measure (Point k)} {ν : Measure (Direction k)}
    (h : Laws k q t R ζ ε δ μ ν) (hu0 : 0 ≤ u) (hδu : δ ≤ u)
    (hK : δ ^ (-ε) ≤ u ^ (-η)) : Laws k q t R ζ η u μ ν := by
  obtain ⟨hm, hn, hs, ht, hq, hz⟩ := h
  refine ⟨hm, hn, hs, ?_, ?_, ?_⟩
  · intro x r hur hr
    exact (ht x r (hδu.trans hur) hr).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (hu0.trans hur) _)))
  · intro w r hur hr
    exact (hq w r (hδu.trans hur) hr).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (hu0.trans hur) _)))
  · intro he H hH r hur hr
    exact (hz he H hH r (hδu.trans hur) hr).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg (hu0.trans hur) _)))

/-- Non-dyadic scales follow by rounding upward, reducing the allowed input loss,
and reducing the output gain. There is no change to the measures or relation. -/
theorem smallCapGain_of_dyadic {k : ℕ} {q t C R ζ : ℝ}
    (hq : 0 ≤ q) (hC : 0 ≤ C) (hlocal : DyadicSmallCapGain k q t C R ζ) :
    SmallCapGain k q t C R ζ := by
  obtain ⟨ρ, hρ, η, hη, c, hc, d₀, hd₀, hgain⟩ := hlocal
  obtain ⟨d₁, hd₁, hballs⟩ := input_scale_slack 0 η (η / 2) (by linarith) (by linarith)
  obtain ⟨d₂, hd₂, hcounts⟩ := input_scale_slack q η (η / 2) (by linarith) (by linarith)
  obtain ⟨d₃, hd₃, hout⟩ := absorb_finite_constant ((2 : ℝ) ^ c) c hc
  let d := min 1 (min (d₀ / 2) (min d₁ (min d₂ d₃)))
  have hd : 0 < d := lt_min (by norm_num)
    (lt_min (by positivity) (lt_min hd₁ (lt_min hd₂ hd₃)))
  refine ⟨ρ, hρ, η / 2, by linarith, c / 2, by linarith, d, hd, ?_⟩
  intro δ hδ hδd μ ν hlaws w₀ E hE hcover hcap
  have hδ₁ : δ < 1 := lt_of_lt_of_le hδd (min_le_left _ _)
  have hδrest : δ < min (d₀ / 2) (min d₁ (min d₂ d₃)) :=
    lt_of_lt_of_le hδd (min_le_right _ _)
  have hδ₀ : δ < d₀ / 2 := (lt_min_iff.mp hδrest).1
  have hδd₁ : δ < d₁ := (lt_min_iff.mp (lt_min_iff.mp hδrest).2).1
  have hδd₂ : δ < d₂ := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hδrest).2).2).1
  have hδd₃ : δ < d₃ := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hδrest).2).2).2
  obtain ⟨N, hNlow, hNhigh⟩ := exists_nat_pow_near_of_lt_one hδ hδ₁.le
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let u : ℝ := (1 / 2 : ℝ) ^ N
  have hu : 0 < u := pow_pos (by norm_num) _
  have hδu : δ ≤ u := hNhigh
  have huδ : u ≤ 2 * δ := by
    have : u * (1 / 2) < δ := by simpa [u, pow_succ] using hNlow
    linarith
  have hu₀ : u < d₀ := by linarith
  have hK : δ ^ (-(η / 2)) ≤ u ^ (-η) := by
    simpa using hballs δ u hδ hδd₁ hu huδ
  have hlaws' := laws_change_scale hlaws hu.le hδu hK
  have hcover' : FiberCover k q C η u E := by
    intro w
    obtain ⟨A, hA, hcov⟩ := hcover w
    refine ⟨A, hA.trans (hcounts δ u hδ hδd₂ hu huδ), ?_⟩
    intro x hx
    obtain ⟨a, ha, hxa⟩ := hcov x hx
    exact ⟨a, ha, hxa.trans (mul_le_mul_of_nonneg_left hδu hC)⟩
  calc
    (μ.prod ν) E ≤ ENNReal.ofReal (u ^ c) := hgain N hu₀ μ ν hlaws' w₀ E hE hcover' hcap
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ c * δ ^ c) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.mul_rpow (by norm_num) hδ.le]
      exact Real.rpow_le_rpow hu.le huδ hc.le
    _ ≤ ENNReal.ofReal (δ ^ (c / 2)) := ENNReal.ofReal_le_ofReal (hout δ hδ hδd₃)

/-- An arbitrary finite cover of a bounded fiber can be replaced, with no
cardinality increase, by anchors in the fiber itself. This does not assert a
measurable choice of these covers as the direction varies. -/
theorem bounded_fiber_anchors {k : ℕ} {q C R ε δ : ℝ}
    {E : Set (Point k × Direction k)}
    (hE : ∀ u ∈ E, ‖u.1‖ ≤ R) (hcover : FiberCover k q C ε δ E) :
    ∀ w : Direction k, ∃ A : Finset (Point k),
      (A.card : ℝ) ≤ δ ^ (-q - ε) ∧ (∀ a ∈ A, ‖a‖ ≤ R) ∧
      ∀ x : Point k, (x, w) ∈ E → ∃ a ∈ A,
        ‖(ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto (x - a)‖ ≤ (2 * C) * δ := by
  classical
  intro w
  obtain ⟨A, hA, hcov⟩ := hcover w
  let P := (ℝ ∙ (w : Point k))ᗮ.orthogonalProjectionOnto
  let I := A.filter (fun a => ∃ y : Point k, (y, w) ∈ E ∧ ‖P (y - a)‖ ≤ C * δ)
  have hex (a : {a // a ∈ I}) :
      ∃ y : Point k, (y, w) ∈ E ∧ ‖P (y - a.val)‖ ≤ C * δ :=
    (Finset.mem_filter.mp a.property).2
  choose y hy using hex
  let A' := I.attach.image y
  have hcard : A'.card ≤ A.card := calc
    A'.card ≤ I.attach.card := Finset.card_image_le
    _ = I.card := Finset.card_attach
    _ ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hcardR : (A'.card : ℝ) ≤ A.card := by exact_mod_cast hcard
  refine ⟨A', hcardR.trans hA, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hE (y i, w) (hy i).1
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hcov x hx
    have haI : a ∈ I := Finset.mem_filter.mpr ⟨ha, x, hx, hxa⟩
    let i : {a // a ∈ I} := ⟨a, haI⟩
    refine ⟨y i, Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, rfl⟩, ?_⟩
    simpa [mul_assoc] using reanchor_tube w x (y i) a hxa (hy i).2

/-- The two port estimates, followed by finite spatial localization, close
    the dyadic bridge. The resulting estimate is uniform over all directions. -/
theorem missing_dyadic_small_cap_bridge : DyadicSmallCapBridge := by
  intro k hk q t hq hq' ht ht' C hC R _hR ζ hζ
  obtain ⟨ε, hε, c, hc, d, hd, hg⟩ := bounded_dyadic_gain (R := R)
    (unit_dyadic_gain k hk q t hq hq' ht ht' C hC ζ hζ)
  exact ⟨1, by norm_num, ε, hε, c, hc, d, hd,
    fun N hN μ ν hl _w₀ E hE hcov _hcap => hg N hN μ ν hl E hE hcov⟩

end OAI.Falconer.LinearProjectionGainPartial

open Set MeasureTheory
open scoped ENNReal InnerProductSpace
open OAI.Falconer.LinearProjectionGainPartial

theorem solution_of_bridge
    (bridge : OAI.Falconer.LinearProjectionGainPartial.DyadicSmallCapBridge)
    (k : ℕ) (hk : 2 ≤ k) (q t : ℝ)
    (hq : (k : ℝ) - 1 ≤ q) (hq' : q ≤ (k : ℝ) - 1 / 2)
    (ht : (k : ℝ) - 1 / 2 < t) (ht' : t < (k : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (R : ℝ) (hR : 0 ≤ R)
    (ζ : ℝ) (hζ : q = (k : ℝ) - 1 → 0 < ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        (ν : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)),
      μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ᵐ x ∂μ, ‖x‖ ≤ R) →
      (∀ x : EuclideanSpace ℝ (Fin (k + 1)), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ t)) →
      (∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
        ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν (Metric.ball w r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ q)) →
      (q = (k : ℝ) - 1 →
        ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 1))),
        Module.finrank ℝ H = k → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν {w | Metric.infDist (w : EuclideanSpace ℝ (Fin (k + 1))) (H : Set _) ≤ r}
          ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ ζ)) →
      ∀ E : Set (EuclideanSpace ℝ (Fin (k + 1)) ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1),
      NullMeasurableSet E (μ.prod ν) →
      (∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
        ∃ A : Finset (EuclideanSpace ℝ (Fin (k + 1))),
          (A.card : ℝ) ≤ δ ^ (-q - ε) ∧
          ∀ x : EuclideanSpace ℝ (Fin (k + 1)), (x, w) ∈ E →
            ∃ a ∈ A,
              ‖(ℝ ∙ (w : EuclideanSpace ℝ (Fin (k + 1))))ᗮ.orthogonalProjectionOnto
                (x - a)‖ ≤ C * δ) →
      (μ.prod ν) E ≤ ENNReal.ofReal (δ ^ c) := by
  have hq0 : 0 ≤ q := by
    have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcap := smallCapGain_of_dyadic hq0 hC
    (bridge k hk q t hq hq' ht ht' C hC R hR ζ hζ)
  obtain ⟨ε, hε, c, hc, δ₀, hδ₀, hgain⟩ := global_of_smallCapGain hcap
  refine ⟨ε, hε, c, hc, δ₀, hδ₀, ?_⟩
  intro δ hδ hδsmall μ ν hμ hν hs hμball hνball hplate E hE hcover
  exact hgain δ hδ hδsmall μ ν ⟨hμ, hν, hs, hμball, hνball, hplate⟩ E hE hcover


theorem solution
    (k : ℕ) (hk : 2 ≤ k) (q t : ℝ)
    (hq : (k : ℝ) - 1 ≤ q) (hq' : q ≤ (k : ℝ) - 1 / 2)
    (ht : (k : ℝ) - 1 / 2 < t) (ht' : t < (k : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (R : ℝ) (hR : 0 ≤ R)
    (ζ : ℝ) (hζ : q = (k : ℝ) - 1 → 0 < ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin (k + 1))))
        (ν : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)),
      μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ᵐ x ∂μ, ‖x‖ ≤ R) →
      (∀ x : EuclideanSpace ℝ (Fin (k + 1)), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ t)) →
      (∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
        ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν (Metric.ball w r) ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ q)) →
      (q = (k : ℝ) - 1 →
        ∀ H : Submodule ℝ (EuclideanSpace ℝ (Fin (k + 1))),
        Module.finrank ℝ H = k → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν {w | Metric.infDist (w : EuclideanSpace ℝ (Fin (k + 1))) (H : Set _) ≤ r}
          ≤ ENNReal.ofReal (δ ^ (-ε) * r ^ ζ)) →
      ∀ E : Set (EuclideanSpace ℝ (Fin (k + 1)) ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1),
      NullMeasurableSet E (μ.prod ν) →
      (∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1,
        ∃ A : Finset (EuclideanSpace ℝ (Fin (k + 1))),
          (A.card : ℝ) ≤ δ ^ (-q - ε) ∧
          ∀ x : EuclideanSpace ℝ (Fin (k + 1)), (x, w) ∈ E →
            ∃ a ∈ A,
              ‖(ℝ ∙ (w : EuclideanSpace ℝ (Fin (k + 1))))ᗮ.orthogonalProjectionOnto
                (x - a)‖ ≤ C * δ) →
      (μ.prod ν) E ≤ ENNReal.ofReal (δ ^ c) := by
  exact solution_of_bridge missing_dyadic_small_cap_bridge k hk q t hq hq' ht ht' C hC R hR ζ hζ
