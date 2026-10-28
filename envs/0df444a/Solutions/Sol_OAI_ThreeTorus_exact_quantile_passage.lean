-- Prove2me | solution 1 for OAI.ThreeTorus.exact_quantile_passage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:10:37.172304+00:00
-- url     : https://prove2.me/submissions/fb6a43ec-e157-426f-951f-9fc1be4d45c5

import Mathlib
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_exact_quantile_circle_spectral_estimate

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Jitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cumulative distribution, smooth quantile inverse, and positive smooth neutral jitter laws. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics

/-! Approximation of a positive smooth law.
The cumulative distribution and its local smooth inverse are constructed from
the positive smooth density, not assumed as an additional hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus

lemma cumulative_sub (ρ : ℝ → ℝ) (hi : Integrable ρ) (x y : ℝ) :
    cumulative ρ y - cumulative ρ x = ∫ t in x..y, ρ t :=
  intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn

lemma cumulative_eq_primitive (ρ : ℝ → ℝ) (hi : Integrable ρ) :
    cumulative ρ = fun y => cumulative ρ 0 + ∫ t in 0..y, ρ t := by
  funext y
  linarith [cumulative_sub ρ hi 0 y]

lemma hasDerivAt_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ) (y : ℝ) :
    HasDerivAt (cumulative ρ) (ρ y) y := by
  rw [cumulative_eq_primitive ρ hi]
  convert (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 y)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (cumulative ρ 0) using 1
  all_goals try with_reducible_and_instances rfl

lemma contDiff_cumulative {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cumulative ρ) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (hasDerivAt_cumulative hρ.continuous hi y).differentiableAt, ?_⟩
  have hd : deriv (cumulative ρ) = ρ := funext fun y =>
    (hasDerivAt_cumulative hρ.continuous hi y).deriv
  rw [hd]
  exact hρ

lemma strictMono_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) : StrictMono (cumulative ρ) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_cumulative hc hi) hp

lemma cumulative_atBot {ρ : ℝ → ℝ} :
    Tendsto (cumulative ρ) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

lemma cumulative_atTop {ρ : ℝ → ℝ} (hi : Integrable ρ) (hm : ∫ y, ρ y = 1) :
    Tendsto (cumulative ρ) atTop (𝓝 1) := by
  change Tendsto (fun y : ℝ => ∫ x in Iic y, ρ x) atTop (𝓝 1)
  simpa only [hm, id_eq] using
    (aecover_Iic (μ := (volume : Measure ℝ)) tendsto_id).integral_tendsto_of_countably_generated hi

lemma cumulative_mem_Ioo {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (y : ℝ) :
    cumulative ρ y ∈ Ioo (0 : ℝ) 1 := by
  have hs := strictMono_cumulative hc hi hp
  constructor
  · exact (hs.monotone.le_of_tendsto cumulative_atBot (y-1)).trans_lt
      (hs (by linarith : y-1 < y))
  · exact (hs (by linarith : y < y+1)).trans_le
      (hs.monotone.ge_of_tendsto (cumulative_atTop hi hm) (y+1))

lemma range_cumulative {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    range (cumulative ρ) = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨y,rfl⟩
    exact cumulative_mem_Ioo hc hi hp hm y
  · intro z hz
    obtain ⟨a,ha⟩ := (cumulative_atBot.eventually (gt_mem_nhds hz.1)).exists
    obtain ⟨b,hb⟩ := ((cumulative_atTop hi hm).eventually (lt_mem_nhds hz.2)).exists
    exact intermediate_value_univ a b
      (continuous_iff_continuousAt.mpr fun y => (hasDerivAt_cumulative hc hi y).continuousAt)
      ⟨ha.le,hb.le⟩

lemma cumulative_quantile {ρ : ℝ → ℝ} (hc : Continuous ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    cumulative ρ (quantile ρ a) = a := by
  apply invFun_eq
  change a ∈ range (cumulative ρ)
  rw [range_cumulative hc hi hp hm]
  exact ha

lemma contDiffAt_invFun_of_deriv_ne_zero {F : ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hinj : Injective F)
    {x d : ℝ} (hd : HasDerivAt F d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFun F) (F x) := by
  let e := hF.contDiffAt.toOpenPartialHomeomorph F (hd.hasFDerivAt_equiv hd0) (by simp)
  have hx : x ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = F := rfl
  have hy : F x ∈ e.target := by simpa only [he] using e.map_source hx
  have hs : e.symm (F x) = x := by simpa only [he] using e.left_inv hx
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (F x) := by
    apply e.contDiffAt_symm_deriv hd0 hy
    · simpa only [he, hs] using hd
    · simpa only [he, hs] using hF.contDiffAt (x := x)
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hy] with y hy'
  apply hinj
  have hr : F (e.symm y) = y := by simpa only [he] using e.right_inv hy'
  rw [invFun_eq ⟨e.symm y,hr⟩, hr]

lemma contDiffOn_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (quantile ρ) (Ioo (0 : ℝ) 1) := by
  intro a ha
  have hh := contDiffAt_invFun_of_deriv_ne_zero (contDiff_cumulative hρ hi)
    (strictMono_cumulative hρ.continuous hi hp).injective
    (hasDerivAt_cumulative hρ.continuous hi (quantile ρ a)) (hp _).ne'
  rw [cumulative_quantile hρ.continuous hi hp hm ha] at hh
  exact hh.contDiffWithinAt

lemma hasDerivAt_quantile {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (quantile ρ) (ρ (quantile ρ a))⁻¹ a := by
  apply HasDerivAt.of_local_left_inverse
    ((contDiffOn_quantile hρ hi hp hm).contDiffAt (isOpen_Ioo.mem_nhds ha)).continuousAt
    (hasDerivAt_cumulative hρ.continuous hi _) (hp _).ne'
  filter_upwards [isOpen_Ioo.mem_nhds ha] with y hy
  exact cumulative_quantile hρ.continuous hi hp hm hy

lemma contDiff_periodize {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (periodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R + |x| + 1)
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : ∀ᶠ y in 𝓝 x, support (fun k : ℤ => f (y+k)) ⊆ (s : Set ℤ) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    intro k hk
    have hy' : |y| < |x| + 1 := by
      have := abs_add_le (y-x) x
      have hy'' : |y-x| < 1 := hy
      simpa only [sub_add_cancel] using this.trans_lt (by linarith : |y-x|+|x| < |x|+1)
    have hk' : |y+(k : ℝ)| ≤ R := by
      simpa only [Real.norm_eq_abs] using hR (y+k) (subset_tsupport f hk)
    have hz : |(k : ℝ)| < (N : ℝ) := calc
      |(k : ℝ)| = |(y+k)-y| := by congr 1; ring
      _ ≤ |y+k| + |y| := abs_sub _ _
      _ < ↑N := by linarith
    have hh : -(N : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ ↑N := (abs_le.mp hz.le)
    show k ∈ Finset.Icc (-(N : ℤ)) N
    rw [Finset.mem_Icc]
    exact_mod_cast hh
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∑ k ∈ s, f (y+k)) :=
    ContDiff.sum fun k _ => hf.comp (contDiff_id.add contDiff_const)
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  exact finsum_eq_sum_of_support_subset _ hy

lemma periodize_eq_on_unit {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : periodize f x = f x := by
  unfold periodize
  convert finsum_eq_single (fun k : ℤ => f (x+k)) 0 ?_ using 1
  · simp
  · intro k hk
    by_contra hn
    have hh := hs (show x+(k : ℝ) ∈ support f from hn)
    have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hx.2, hh.1]
    have h2 : (k : ℝ) < (1 : ℝ) := by linarith [hx.1, hh.2]
    have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (1 : ℤ) := by exact_mod_cast h2
    omega

lemma periodize_eq_fract {f : ℝ → ℝ} (hs : support f ⊆ Ioo (0 : ℝ) 1) (x : ℝ) :
    periodize f x = f (Int.fract x) := by
  have hh := (periodize_periodic f).sub_zsmul_eq (x := x) ⌊x⌋
  have he : periodize f (Int.fract x) = periodize f x := by
    simpa only [Int.fract, zsmul_eq_mul, mul_one] using hh
  rw [← he]
  exact periodize_eq_on_unit hs ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

lemma contDiff_cutoff_quantile {ρ ξ : ℝ → ℝ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1)
    (hξ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ)
    (hs : tsupport ξ ⊆ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => ξ a * quantile ρ a) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  by_cases ha : a ∈ tsupport ξ
  · exact hξ.contDiffAt.mul ((contDiffOn_quantile hρ hi hp hm).contDiffAt
      (isOpen_Ioo.mem_nhds (hs ha)))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ha] with b hb
    simp only [Pi.zero_apply] at hb
    simp only [hb, zero_mul]

lemma lawJitter_smooth {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawJitter ρ c) :=
  contDiff_periodize (contDiff_cutoff_quantile hρ hi hp hm c.ξ_smooth c.ξ_support)
    c.ξ_compact.mul_right

lemma lawJitter_eq_quantile {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hδ : 0 < δ) {a : ℝ} (ha : a ∈ Icc δ (1-δ)) :
    lawJitter ρ c a = quantile ρ a := by
  rw [lawJitter, periodize_eq_on_unit, c.ξ_one a ha, one_mul]
  · exact (support_mul_subset_left _ _).trans ((subset_tsupport _).trans c.ξ_support)
  · constructor <;> linarith [ha.1,ha.2]

lemma lawJitter_deriv_pos {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Ioo δ (1-δ)) :
    HasDerivAt (lawJitter ρ c) (ρ (quantile ρ a))⁻¹ a ∧
      0 < (ρ (quantile ρ a))⁻¹ := by
  refine ⟨?_, inv_pos.mpr (hp _)⟩
  apply (hasDerivAt_quantile hρ hi hp hm
    (show a ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [ha.1], by linarith [ha.2]⟩)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩

lemma lawPsi_smooth {δ : ℝ} (c : LawCutoffs δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lawPsi c) :=
  contDiff_periodize c.ψ_smooth c.ψ_compact

lemma lawPsi_eq {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : lawPsi c a = c.ψ a := by
  apply periodize_eq_on_unit _ ha
  intro x hx
  have hh := c.ψ_support (subset_tsupport _ hx)
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma lawPsi_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (a : ℝ) :
    0 ≤ lawPsi c a ∧ lawPsi c a ≤ 1 := by
  have hs : support c.ψ ⊆ Ioo (0 : ℝ) 1 := fun x hx => by
    have hh := c.ψ_support (subset_tsupport _ hx)
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  rw [lawPsi, periodize_eq_fract hs]
  exact ⟨c.ψ_nonneg _, c.ψ_le_one _⟩

lemma integral_cutoff_lower {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    1-4*δ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hi : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  calc
    1-4*δ = ∫ a in Icc (2*δ) (1-2*δ), (1 : ℝ) := by
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-2*δ-2*δ)]
      ring
    _ = ∫ a in Icc (2*δ) (1-2*δ), c.ψ a^2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro a ha
      change 1 = c.ψ a^2
      rw [c.ψ_one a ha, one_pow]
    _ ≤ ∫ a in Ioo (0 : ℝ) 1, c.ψ a^2 := by
      apply setIntegral_mono_set hi.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      exact Eventually.of_forall fun a ha => ⟨by linarith [ha.1], by linarith [ha.2]⟩

lemma missing_cutoff_mass {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ a in Ioo (0 : ℝ) 1, (1-c.ψ a^2)) ≤ 4*δ := by
  have hs : HasCompactSupport (fun a : ℝ => c.ψ a^2) :=
    c.ψ_compact.comp_left (g := fun t : ℝ => t^2) (by norm_num)
  have hψ : Integrable (fun a : ℝ => c.ψ a^2) :=
    (c.ψ_smooth.continuous.pow 2).integrable_of_hasCompactSupport hs
  have hunit : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (0 : ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [integral_sub hunit hψ.integrableOn]
  have he : (∫ a in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  rw [he]
  linarith [integral_cutoff_lower c hδ hδ']

end ThreeTorus

namespace ThreeTorus
open Set Function MeasureTheory
open scoped Topology

lemma continuous_neutralCircleCutoff {δ : ℝ} (c : LawCutoffs δ) :
    Continuous (neutralCircleCutoff c) :=
by
  apply Continuous.quotient_lift
  exact (lawPsi_smooth c).continuous

lemma neutralCircleCutoff_bounds {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ)
    (a : UnitAddCircle) : 0 ≤ neutralCircleCutoff c a ∧ neutralCircleCutoff c a ≤ 1 := by
  induction a using Quotient.inductionOn with
  | h a => exact lawPsi_bounds c hδ a

lemma neutralCircleCutoff_error {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) :
    (∫ a, (1-neutralCircleCutoff c a^2) ∂AddCircle.haarAddCircle) ≤ 4*δ := by
  have he := AddCircle.integral_preimage 1 0 (fun a => (1-neutralCircleCutoff c a^2))
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,one_smul] at he
  rw [← he]
  change (∫ a in Ioc (0:ℝ) 1, (1-lawPsi c a^2)) ≤ 4*δ
  have hi : (∫ a in Ioc (0:ℝ) 1, (1-lawPsi c a^2)) =
      ∫ a in Ioo (0:ℝ) 1, (1-c.ψ a^2) := by
    rw [integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro a ha
    dsimp only
    rw [lawPsi_eq c hδ ⟨ha.1.le,ha.2.le⟩]
  rw [hi]
  exact missing_cutoff_mass c hδ hδ'

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_StationaryPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform signed stationary phase, oscillatory integral estimates, and summed coefficient-mass control. -/

noncomputable section

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
namespace ThreeTorus

lemma quadratic_gaussian_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hi : Integrable (fun x : ℝ => Complex.exp (-Real.pi * b * x ^ 2)) := by
    have hb' : 0 < ((Real.pi : ℂ) * b).re := by
      simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using mul_pos Real.pi_pos hb
    simpa only [neg_mul, mul_zero, zero_mul, add_zero] using
      integrable_cexp_quadratic hb' 0 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner (𝓕⁻ f).integrable hi
  have hinv : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = (f : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  have h' : (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      ∫ x : ℝ, (𝓕⁻ f) x * (𝓕 fun y : ℝ => Complex.exp (-Real.pi * b * y ^ 2)) x := by
    rw [flip_innerₗ] at h
    change (∫ x : ℝ, (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x •
      Complex.exp (-Real.pi * b * x ^ 2)) = _ at h
    simpa only [hinv, smul_eq_mul] using! h
  rw [h', fourier_gaussian_pi hb, ← integral_const_mul]
  congr 1
  ext x
  ring

lemma norm_quadratic_exp_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * b * x ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have he : (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2).re = -Real.pi * b.re * x ^ 2 := by
    simp [mul_re, mul_im, pow_two]
  rw [he]
  have := mul_nonneg (mul_nonneg Real.pi_pos.le hb) (sq_nonneg x)
  linarith

/-- The Gaussian identity extends to the imaginary boundary after pairing with
an integrable Schwartz amplitude. This uses dominated convergence, never a
non-absolutely convergent Bochner integral for a bare Fresnel kernel. -/
lemma quadratic_boundary_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ}
    (hb : 0 ≤ b.re) (hbslit : b ∈ Complex.slitPlane) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hb0 : b ≠ 0 := Complex.slitPlane_ne_zero hbslit
  have hparam : Tendsto (fun ε : ℝ => b + (ε : ℂ)) (𝓝[>] 0) (𝓝 b) := by
    have hcast : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using hcast.const_add b
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hre : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < (b + (ε : ℂ)).re := by
    filter_upwards [heps] with ε hε
    simp only [add_re, ofReal_re]
    linarith
  have hleft : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      f x * Complex.exp (-Real.pi * (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      ?_ ?_ f.integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hε.le x)
        (norm_nonneg (f x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((hparam.const_mul _).mul_const _).cexp)
  have hintegral : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (𝓕⁻ f) x * Complex.exp (-Real.pi / (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, (𝓕⁻ f) x * Complex.exp (-Real.pi / b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖(𝓕⁻ f) x‖)
      ?_ ?_ (𝓕⁻ f).integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul, div_eq_mul_inv]
      have hb' : 0 ≤ (b + (ε : ℂ))⁻¹.re := by
        rw [Complex.inv_re]
        exact div_nonneg hε.le (Complex.normSq_nonneg _)
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hb' x)
        (norm_nonneg ((𝓕⁻ f) x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((tendsto_const_nhds.div hparam hb0).mul_const _).cexp)
  have hpow : Tendsto (fun ε : ℝ => 1 / (b + (ε : ℂ)) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    apply tendsto_const_nhds.div
    · exact (continuousAt_cpow_const hbslit).tendsto.comp hparam
    · exact cpow_ne_zero_iff.mpr (Or.inl hb0)
  have hr := hpow.mul hintegral
  have hright := hr.congr' (hre.mono (fun ε hε => (quadratic_gaussian_pairing f hε).symm))
  exact tendsto_nhds_unique hleft hright

lemma cpow_pos_mul {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((t : ℂ) * z) ^ w = (t : ℂ) ^ w * z ^ w := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ht.ne') hz),
    Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul ht hz,
    ← Complex.ofReal_log ht.le, add_mul, Complex.exp_add]

lemma quadratic_factor {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) / ((t : ℂ) * (-I)) ^ (1 / 2 : ℂ) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) := by
  have hs : (Real.sqrt t : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  rw [cpow_pos_mul ht (neg_ne_zero.mpr I_ne_zero), hs, div_mul_eq_div_div,
    div_self (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))),
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I,
    one_div, ← Complex.exp_neg]
  congr 1
  ring

lemma integral_fourierInv (f : 𝓢(ℝ, ℂ)) : (∫ x : ℝ, (𝓕⁻ f) x) = f 0 := by
  have he : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) 0 = f 0 := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  simpa [Real.fourier_eq] using he

lemma quadratic_stationary_identity (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) *
        (∫ ξ : ℝ, (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
  have hb : 0 ≤ ((t : ℂ) * (-I)).re := by simp
  have hslit : (t : ℂ) * (-I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using ht.ne'
  have he := quadratic_boundary_pairing f hb hslit
  have hleft : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) * ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (Real.pi * t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    ring
  have hright : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) / ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (-Real.pi / t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    field_simp
    simp [I_sq]
    ring
  simp only [hleft, hright] at he
  rw [he, ← mul_assoc, ← div_eq_mul_one_div, quadratic_factor ht]

lemma quadratic_stationary_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    ‖(Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
      Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0‖ ≤
        (Real.pi / t) * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
  rw [quadratic_stationary_identity f ht, ← mul_sub, norm_mul]
  have hnorm : ‖Complex.exp ((Real.pi : ℂ) / 4 * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm, one_mul, ← integral_fourierInv f]
  have hi : Integrable (fun ξ : ℝ => (𝓕⁻ f) ξ *
      Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
    apply ((𝓕⁻ f).integrable (μ := volume)).mul_bdd
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards [] with ξ
      have he : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))‖ = 1 := by
        rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
      exact he.le
  rw [← integral_sub hi (𝓕⁻ f).integrable]
  have hd : Integrable (fun ξ : ℝ => ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
    have hh := (𝓕⁻ f).integrable_pow_mul volume 2
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hd.const_mul (Real.pi / t))
  filter_upwards [] with ξ
  have heq : (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - (𝓕⁻ f) ξ =
      (𝓕⁻ f) ξ * (Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1) := by ring
  rw [heq, norm_mul]
  have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -Real.pi / t * ξ^2)
  have he' : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
      Real.pi / t * ξ^2 := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos ht, abs_of_nonneg (sq_nonneg ξ)]
  calc
    ‖(𝓕⁻ f) ξ‖ * ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
        ‖(𝓕⁻ f) ξ‖ * (Real.pi / t * ξ^2) :=
      mul_le_mul_of_nonneg_left he' (norm_nonneg _)
    _ = _ := by ring

lemma quadratic_stationary_limit (f : 𝓢(ℝ, ℂ)) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)) := by
  have hlim : Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
      (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact quadratic_stationary_error f ht
    · simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const
        (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖)
  simpa using hlim.add_const (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)

lemma quadratic_stationary_compact {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
        (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0)) :=
  quadratic_stationary_limit (hf.toSchwartzMap hsm)

lemma oscillatory_integral_parts {a b t : ℝ} (ht : t ≠ 0)
    {φ φ' : ℝ → ℝ} {B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hB' : IntervalIntegrable B' volume a b) :
    (∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) =
      (1 / (I * (t : ℂ))) *
        (B b * Complex.exp (I * (t * φ b : ℝ)) -
          B a * Complex.exp (I * (t * φ a : ℝ)) -
            ∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))) := by
  have hv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun x => Complex.exp (I * (t * φ x : ℝ)))
        (Complex.exp (I * (t * φ x : ℝ)) * (I * (t * φ' x : ℝ))) x := by
    exact (((hφ x hx).const_mul t).ofReal_comp.const_mul I).cexp
  have hφc : ContinuousOn φ (uIcc a b) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable
      (fun x => Complex.exp (I * (t * φ x : ℝ)) * (I * (t * φ' x : ℝ))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul hB hv hB' hvi
  have hj : (∫ x in a..b, B x * (Complex.exp (I * (t * φ x : ℝ)) *
      (I * (t * φ' x : ℝ)))) = (I * (t : ℂ)) *
        (∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    ring
  rw [hj] at he
  rw [← he]
  field_simp [ofReal_ne_zero.mpr ht]

lemma oscillatory_integral_bound {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0)
    {φ φ' : ℝ → ℝ} {B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b))
    (hB' : IntervalIntegrable B' volume a b) :
    ‖∫ x in a..b, B x * (φ' x : ℂ) * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (1 / |t|) * (‖B b‖ + ‖B a‖ + ∫ x in a..b, ‖B' x‖) := by
  rw [oscillatory_integral_parts ht hφ hB hφ' hB', norm_mul]
  have he (r : ℝ) : ‖Complex.exp (I * (r : ℂ))‖ = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
  have hc : ‖1 / (I * (t : ℂ))‖ = 1 / |t| := by simp
  rw [hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖B b * Complex.exp (I * (t * φ b : ℝ)) -
      B a * Complex.exp (I * (t * φ a : ℝ)) -
        ∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      ‖B b * Complex.exp (I * (t * φ b : ℝ)) -
        B a * Complex.exp (I * (t * φ a : ℝ))‖ +
          ‖∫ x in a..b, B' x * Complex.exp (I * (t * φ x : ℝ))‖ := norm_sub_le _ _
    _ ≤ (‖B b‖ + ‖B a‖) + ∫ x in a..b, ‖B' x‖ := by
      apply add_le_add
      · simpa only [norm_mul, he, mul_one] using
          norm_sub_le (B b * Complex.exp (I * (t * φ b : ℝ)))
            (B a * Complex.exp (I * (t * φ a : ℝ)))
      · simpa only [norm_mul, he, mul_one] using
          intervalIntegral.norm_integral_le_integral_norm hab
            (f := fun x => B' x * Complex.exp (I * (t * φ x : ℝ)))

lemma reciprocal_variation {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    {q q' : ℝ → ℝ}
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hqc : ContinuousOn q' (Icc a b))
    (hsep : ∀ x ∈ Icc a b, r ≤ |q x|) :
    (∫ x in a..b, q' x / q x ^ 2) = (q a)⁻¹ - (q b)⁻¹ ∧
      (∫ x in a..b, q' x / q x ^ 2) ≤ 2 / r := by
  have hne (x : ℝ) (hx : x ∈ Icc a b) : q x ≠ 0 := by
    intro hz
    have := hsep x hx
    simp only [hz, abs_zero] at this
    linarith
  have hc : ContinuousOn q (Icc a b) :=
    fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun x => q' x / q x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx))
  have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => -(q x)⁻¹) (q' x / q x ^ 2) x := by
    rw [uIcc_of_le hab]
    intro x hx
    simpa only [Pi.neg_apply, Pi.inv_apply, neg_div, neg_neg] using!
      ((hq x hx).inv (hne x hx)).neg
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [sub_neg_eq_add, neg_add_eq_sub] at he
  refine ⟨he, ?_⟩
  rw [he]
  have bound (x : ℝ) (hx : x ∈ Icc a b) : |(q x)⁻¹| ≤ 1 / r := by
    rw [abs_inv, one_div]
    exact inv_anti₀ hr (hsep x hx)
  calc
    (q a)⁻¹ - (q b)⁻¹ ≤ |(q a)⁻¹| + |(q b)⁻¹| := by
      linarith [le_abs_self ((q a)⁻¹), neg_le_abs ((q b)⁻¹)]
    _ ≤ 1 / r + 1 / r := add_le_add (bound a ⟨le_rfl, hab⟩) (bound b ⟨hab, le_rfl⟩)
    _ = 2 / r := by ring

lemma nonstationary_monotone_bound {a b t r C₀ C₁ : ℝ}
    (hab : a ≤ b) (ht : t ≠ 0) (hr : 0 < r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    {φ q q' : ℝ → ℝ} {A A' : ℝ → ℂ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (q x) x)
    (hq : ∀ x ∈ Icc a b, HasDerivAt q (q' x) x)
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hqc : ContinuousOn q' (Icc a b)) (hAc : ContinuousOn A' (Icc a b))
    (hqpos : ∀ x ∈ Icc a b, 0 ≤ q' x)
    (hsep : ∀ x ∈ Icc a b, r ≤ |q x|)
    (hAb : ∀ x ∈ Icc a b, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc a b, ‖A' x‖ ≤ C₁) :
    ‖∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (4 * C₀ + (b - a) * C₁) / (|t| * r) := by
  have hne (x : ℝ) (hx : x ∈ Icc a b) : q x ≠ 0 := by
    intro hz
    have := hsep x hx
    simp only [hz, abs_zero] at this
    linarith
  have hc : ContinuousOn q (Icc a b) :=
    fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hAf : ContinuousOn A (Icc a b) :=
    fun x hx => (hA x hx).continuousAt.continuousWithinAt
  let B := fun x => A x / (q x : ℂ)
  let B' := fun x => A' x / (q x : ℂ) - A x * (q' x / q x ^ 2 : ℝ)
  have hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x := by
    rw [uIcc_of_le hab]
    intro x hx
    have he : B' x = (A' x * (q x : ℂ) - A x * (q' x : ℂ)) / (q x : ℂ)^2 := by
      dsimp only [B']
      push_cast
      field_simp [ofReal_ne_zero.mpr (hne x hx)]
    rw [he]
    exact (hA x hx).div (hq x hx).ofReal_comp (ofReal_ne_zero.mpr (hne x hx))
  have hBc : ContinuousOn B' (Icc a b) := by
    dsimp [B']
    exact (hAc.div (Complex.continuous_ofReal.comp_continuousOn hc) (fun x hx => ofReal_ne_zero.mpr (hne x hx))).sub
      (hAf.mul (Complex.continuous_ofReal.comp_continuousOn
        (hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx)))))
  have hBi : IntervalIntegrable B' volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hBc
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : ‖B x‖ ≤ C₀ / r := by
    dsimp [B]
    rw [norm_div, norm_real, Real.norm_eq_abs]
    exact div_le_div₀ hC₀ (hAb x hx) hr (hsep x hx)
  have hbound' (x : ℝ) (hx : x ∈ Icc a b) :
      ‖B' x‖ ≤ C₁ / r + C₀ * (q' x / q x ^ 2) := by
    dsimp [B']
    calc
      ‖A' x / (q x : ℂ) - A x * (q' x / q x ^ 2 : ℝ)‖ ≤
        ‖A' x / (q x : ℂ)‖ + ‖A x * (q' x / q x ^ 2 : ℝ)‖ := norm_sub_le _ _
      _ ≤ C₁ / r + C₀ * (q' x / q x ^ 2) := by
        apply add_le_add
        · rw [norm_div, norm_real, Real.norm_eq_abs]
          exact div_le_div₀ hC₁ (hA'b x hx) hr (hsep x hx)
        · rw [norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (hqpos x hx) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (hAb x hx)
            (div_nonneg (hqpos x hx) (sq_nonneg _))
  have hiq : IntervalIntegrable (fun x => q' x / q x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hqc.div (hc.pow 2) (fun x hx => pow_ne_zero _ (hne x hx))
  have hint : (∫ x in a..b, ‖B' x‖) ≤ (b - a) * (C₁ / r) + C₀ * (2 / r) := by
    calc
      (∫ x in a..b, ‖B' x‖) ≤ (∫ x in a..b, C₁ / r + C₀ * (q' x / q x ^ 2)) :=
        intervalIntegral.integral_mono_on hab hBi.norm
          ((intervalIntegrable_const).add (hiq.const_mul C₀)) hbound'
      _ = (b - a) * (C₁ / r) + C₀ * (∫ x in a..b, q' x / q x ^ 2) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hiq.const_mul C₀),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left
        (reciprocal_variation hab hr hq hqc hsep).2 hC₀) _
  have heq : (∫ x in a..b, B x * (q x : ℂ) * Complex.exp (I * (t * φ x : ℝ))) =
      (∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro x hx
    simp only [B, div_mul_cancel₀ (A x) (ofReal_ne_zero.mpr (hne x hx))]
  have hh := oscillatory_integral_bound hab ht
    (φ := φ) (φ' := q) (B := B) (B' := B')
    (by simpa only [uIcc_of_le hab] using hφ) hB
    (by simpa only [uIcc_of_le hab] using hc) hBi
  rw [heq] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (1 / |t|) * (C₀ / r + C₀ / r + ((b-a) * (C₁/r) + C₀ * (2/r))) := by
      gcongr
      · exact hbound b ⟨hab, le_rfl⟩
      · exact hbound a ⟨le_rfl, hab⟩
    _ = _ := by ring

lemma cubic_taylor_estimate {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ)
    {v x M : ℝ} (hv : deriv φ v = 0)
    (hM : ∀ u ∈ uIcc v x, |iteratedDeriv 3 φ u| ≤ M) :
    |φ x - φ v - (iteratedDeriv 2 φ v) / 2 * (x - v)^2| ≤
      M * |x - v|^3 / 6 := by
  by_cases h : v = x
  · subst x
    simp
  have hu := uniqueDiffOn_uIcc h
  have ht : taylorWithinEval φ 2 (uIcc v x) v x =
      φ v + (iteratedDeriv 2 φ v) / 2 * (x - v)^2 := by
    rw [taylorWithinEval_succ φ 1, taylorWithinEval_succ φ 0, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hφ.of_le (by norm_num)).contDiffAt (left_mem_uIcc),
      iteratedDerivWithin_eq_iteratedDeriv hu (hφ.of_le (by norm_num)).contDiffAt (left_mem_uIcc)]
    simp only [iteratedDeriv_one, hv, zero_add, Nat.factorial_zero, Nat.factorial_one,
      Nat.cast_one, Nat.cast_zero, one_mul, pow_one, smul_eq_mul, mul_zero, add_zero]
    ring
  obtain ⟨u, hu', he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) h hφ.contDiffOn
  rw [ht] at he
  have hu'' : u ∈ uIcc v x := ⟨hu'.1.le, hu'.2.le⟩
  norm_num at he
  rw [show φ x - φ v - iteratedDeriv 2 φ v / 2 * (x-v)^2 =
    φ x - (φ v + iteratedDeriv 2 φ v / 2 * (x-v)^2) by ring, he,
      abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM u hu'') (by positivity)) (by norm_num)

lemma norm_exp_imag_sub_le (s t : ℝ) :
    ‖Complex.exp (I * (s : ℂ)) - Complex.exp (I * (t : ℂ))‖ ≤ |s - t| := by
  have he : Complex.exp (I * (s : ℂ)) - Complex.exp (I * (t : ℂ)) =
      Complex.exp (I * (t : ℂ)) * (Complex.exp (I * ((s - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := s-t)

lemma local_stationary_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 1 A)
    {r t C₀ C₁ M : ℝ} (hr : 0 ≤ r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0) (hsecond : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hM : ∀ x ∈ Icc (-r) r, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ‖A 0‖ ≤ C₀) (hA'b : ∀ x ∈ Icc (-r) r, ‖deriv A x‖ ≤ C₁) :
    ‖(∫ x in -r..r, A x * Complex.exp (I * (t * φ x : ℝ))) -
        A 0 * (∫ x in -r..r, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ ≤
      2 * r * (C₁ * r + C₀ * (|t| * M * r^3 / 6)) := by
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr⟩
  have ha (x : ℝ) (hx : x ∈ Icc (-r) r) : ‖A x - A 0‖ ≤ C₁ * r := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hA.differentiable (by norm_num) x) hA'b (convex_Icc (-r) r) h0 hx
    simp only [sub_zero, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr hx) hC₁)
  have hp (x : ℝ) (hx : x ∈ Icc (-r) r) : |φ x - Real.pi * x^2| ≤ M * r^3 / 6 := by
    have h := cubic_taylor_estimate hφ hcrit (fun u hu => hM u (uIcc_subset_Icc h0 hx hu))
    simp only [hzero, hsecond, sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h
    calc
      |φ x - Real.pi * x^2| ≤ M * |x|^3 / 6 := by convert h using 1
      _ ≤ _ := by gcongr; exact abs_le.mpr hx
  have hc₁ : IntervalIntegrable (fun x => A x * Complex.exp (I * (t * φ x : ℝ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    have := hA.continuous
    have := hφ.continuous
    fun_prop
  have hc₂ : IntervalIntegrable (fun x => A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) volume (-r) r := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hc₁ hc₂]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -r) (b := r) (C := C₁*r + C₀*(|t| *M*r^3/6))
    (f := fun x => A x * Complex.exp (I * (t * φ x : ℝ)) -
      A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ)))
  have hpoint (x : ℝ) (hx : x ∈ Icc (-r) r) :
      ‖A x * Complex.exp (I * (t * φ x : ℝ)) -
        A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ))‖ ≤
          C₁*r + C₀*(|t| *M*r^3/6) := by
    have heq : A x * Complex.exp (I * (t * φ x : ℝ)) -
        A 0 * Complex.exp (I * (Real.pi * t * x^2 : ℝ)) =
        (A x - A 0) * Complex.exp (I * (t * φ x : ℝ)) +
        A 0 * (Complex.exp (I * (t * φ x : ℝ)) -
          Complex.exp (I * (Real.pi * t * x^2 : ℝ))) := by ring
    rw [heq]
    calc
      _ ≤ ‖(A x - A 0) * Complex.exp (I * (t * φ x : ℝ))‖ +
        ‖A 0 * (Complex.exp (I * (t * φ x : ℝ)) -
          Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ := norm_add_le _ _
      _ ≤ C₁*r + C₀*(|t| *M*r^3/6) := by
        apply add_le_add
        · rw [norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact ha x hx
        · rw [norm_mul]
          apply mul_le_mul hAb _ (norm_nonneg _) hC₀
          calc
            _ ≤ |t * φ x - Real.pi * t * x^2| := norm_exp_imag_sub_le _ _
            _ = |t| * |φ x - Real.pi * x^2| := by rw [← abs_mul]; congr 1; ring
            _ ≤ |t| * (M*r^3/6) := mul_le_mul_of_nonneg_left (hp x hx) (abs_nonneg _)
            _ = _ := by ring
  specialize hh (fun x hx => hpoint x (by
    rw [uIoc_of_le (by linarith : -r ≤ r)] at hx
    exact ⟨hx.1.le, hx.2⟩))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_nonneg (by linarith : 0 ≤ r - -r)]
  ring

lemma derivative_coercive {q : ℝ → ℝ} {R c : ℝ}
    (hR : 0 ≤ R) (hq : Differentiable ℝ q) (hq0 : q 0 = 0)
    (hc : ∀ x ∈ Icc (-R) R, c ≤ deriv q x) :
    ∀ x ∈ Icc (-R) R, c * |x| ≤ |q x| := by
  intro x hx
  have h := (convex_Icc (-R) R).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => hc x (interior_subset hx))
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  rcases le_total 0 x with hp | hn
  · have hh := h 0 h0 x hx hp
    rw [hq0, sub_zero, sub_zero] at hh
    rw [abs_of_nonneg hp]
    exact hh.trans (le_abs_self _)
  · have hh := h x hx 0 h0 hn
    rw [hq0, zero_sub, zero_sub] at hh
    rw [abs_of_nonpos hn]
    exact hh.trans (neg_le_abs _)

lemma normalized_phase_tail {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {a b R c r t C₀ C₁ : ℝ}
    (hab : a ≤ b) (ha : -R ≤ a) (hb : b ≤ R) (ht : t ≠ 0) (hr : 0 < r)
    (hc : 0 < c) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hcrit : deriv φ 0 = 0)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hsep : ∀ x ∈ Icc a b, r ≤ |x|)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖∫ x in a..b, A x * Complex.exp (I * (t * φ x : ℝ))‖ ≤
      (4 * C₀ + 2 * R * C₁) / (|t| * (c * r)) := by
  have hR : 0 ≤ R := by linarith
  have hsub : Icc a b ⊆ Icc (-R) R := Icc_subset_Icc ha hb
  have hq : ContDiff ℝ 2 (deriv φ) := by simpa using (hφ.of_le (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).deriv'
  have hqa : Differentiable ℝ (deriv φ) := hq.differentiable (by norm_num)
  have hd : ∀ x, deriv (deriv φ) x = iteratedDeriv 2 φ x := by
    intro x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hco := derivative_coercive hR hqa hcrit (by simpa only [hd] using hsecond)
  have h := nonstationary_monotone_bound hab ht (mul_pos hc hr) hC₀ hC₁
    (φ := φ) (q := deriv φ) (q' := deriv (deriv φ)) (A := A) (A' := deriv A)
    (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hqa x).hasDerivAt)
    (fun x _ => (hA.differentiable (by norm_num) x).hasDerivAt)
    (hq.continuous_deriv (by norm_num)).continuousOn
    (hA.continuous_deriv (by norm_num)).continuousOn
    (fun x hx => hc.le.trans (by simpa only [hd] using hsecond x (hsub hx)))
    (fun x hx => (mul_le_mul_of_nonneg_left (hsep x hx) hc.le).trans (hco x (hsub hx)))
    (fun x hx => hAb x (hsub hx)) (fun x hx => hA'b x (hsub hx))
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr
  linarith

lemma quadratic_phase_deriv (x : ℝ) : deriv (fun x : ℝ => Real.pi*x^2) x = 2*Real.pi*x := by
  convert ((hasDerivAt_id x).pow 2).const_mul Real.pi |>.deriv using 1 <;>
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, mul_one]; ring

lemma quadratic_phase_second (x : ℝ) : iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) x = 2*Real.pi := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [show deriv (fun x : ℝ => Real.pi*x^2) = fun x => 2*Real.pi*x from funext quadratic_phase_deriv]
  exact ((hasDerivAt_id x).const_mul (2*Real.pi)).deriv.trans (mul_one _)

lemma interval_three_parts {F : ℝ → ℂ} (hF : Continuous F) (R r : ℝ) :
    (∫ x in -R..R, F x) = ((∫ x in -R..-r, F x) + (∫ x in -r..r, F x)) +
      (∫ x in r..R, F x) := by
  rw [intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]

lemma stationary_interval_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {R c r t C₀ C₁ M : ℝ} (hr : 0 < r) (hrR : r ≤ R) (ht : t ≠ 0)
    (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0)
    (hsecond0 : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hM : ∀ x ∈ Icc (-R) R, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖(∫ x in -R..R, A x * Complex.exp (I * (t * φ x : ℝ))) -
        A 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))‖ ≤
      2 * r * (C₁ * r + C₀ * (|t| * M * r^3 / 6)) +
        4 * ((4*C₀ + 2*R*C₁) / (|t| * (c*r))) := by
  have hR : 0 ≤ R := hr.le.trans hrR
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR⟩
  have hsub : Icc (-r) r ⊆ Icc (-R) R := Icc_subset_Icc (neg_le_neg hrR) hrR
  let F : ℝ → ℂ := fun x => A x * Complex.exp (I * (t * φ x : ℝ))
  let Q : ℝ → ℂ := fun x => A 0 * Complex.exp (I * (t * (Real.pi * x^2) : ℝ))
  let K := (4*C₀ + 2*R*C₁) / (|t| * (c*r))
  have hFc : Continuous F := by have := hA.continuous; have := hφ.continuous; fun_prop
  have hQc : Continuous Q := by fun_prop
  have hFL : ‖∫ x in -R..-r, F x‖ ≤ K :=
    normalized_phase_tail hφ hA (neg_le_neg hrR) le_rfl (by linarith) ht hr hc hC₀ hC₁
      hcrit hsecond (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]) hAb hA'b
  have hFR : ‖∫ x in r..R, F x‖ ≤ K :=
    normalized_phase_tail hφ hA hrR (by linarith) le_rfl ht hr hc hC₀ hC₁
      hcrit hsecond (fun x hx => (le_abs_self x).trans' hx.1) hAb hA'b
  have hqsm : ContDiff ℝ 3 (fun x : ℝ => Real.pi*x^2) := by fun_prop
  have hq0 : deriv (fun x : ℝ => Real.pi*x^2) 0 = 0 := by rw [quadratic_phase_deriv]; ring
  have hqsec : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) x := by
    intro x _; rwa [quadratic_phase_second]
  have hB : ContDiff ℝ 2 (fun _ : ℝ => A 0) := contDiff_const
  have hBb : ∀ x ∈ Icc (-R) R, ‖(fun _ : ℝ => A 0) x‖ ≤ C₀ := fun _ _ => hAb 0 h0
  have hB'b : ∀ x ∈ Icc (-R) R, ‖deriv (fun _ : ℝ => A 0) x‖ ≤ C₁ := by
    intro x _; simpa using hC₁
  have hQL : ‖∫ x in -R..-r, Q x‖ ≤ K :=
    normalized_phase_tail hqsm hB (neg_le_neg hrR) le_rfl (by linarith) ht hr hc hC₀ hC₁
      hq0 hqsec (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]) hBb hB'b
  have hQR : ‖∫ x in r..R, Q x‖ ≤ K :=
    normalized_phase_tail hqsm hB hrR (by linarith) le_rfl ht hr hc hC₀ hC₁
      hq0 hqsec (fun x hx => (le_abs_self x).trans' hx.1) hBb hB'b
  have hlocal := local_stationary_comparison hφ (hA.of_le (by norm_num))
    hr.le hC₀ hC₁ hM₀ hzero hcrit hsecond0
    (fun x hx => hM x (hsub hx)) (hAb 0 h0) (fun x hx => hA'b x (hsub hx)) (t := t)
  have heQ (a b : ℝ) : (∫ x in a..b, Q x) =
      A 0 * (∫ x in a..b, Complex.exp (I * (Real.pi * t * x^2 : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _; dsimp [Q]; congr 3; ring_nf
  rw [← heQ, interval_three_parts hFc R r, interval_three_parts hQc R r]
  rw [← heQ (-r) r] at hlocal
  have he : ((∫ x in -R..-r, F x) + (∫ x in -r..r, F x) + (∫ x in r..R, F x)) -
      ((∫ x in -R..-r, Q x) + (∫ x in -r..r, Q x) + (∫ x in r..R, Q x)) =
      ((∫ x in -r..r, F x) - (∫ x in -r..r, Q x)) +
        ((∫ x in -R..-r, F x) - (∫ x in -R..-r, Q x)) +
        ((∫ x in r..R, F x) - (∫ x in r..R, Q x)) := by ring
  rw [he]
  calc
    _ ≤ (‖(∫ x in -r..r, F x) - (∫ x in -r..r, Q x)‖ +
      ‖(∫ x in -R..-r, F x) - (∫ x in -R..-r, Q x)‖) +
      ‖(∫ x in r..R, F x) - (∫ x in r..R, Q x)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2*r*(C₁*r+C₀*(|t| *M*r^3/6)) + (K+K)) + (K+K) := by
      exact add_le_add (add_le_add hlocal ((norm_sub_le _ _).trans (add_le_add hFL hQL)))
        ((norm_sub_le _ _).trans (add_le_add hFR hQR))
    _ = _ := by dsimp [K]; ring

lemma stationary_interval_scaled_comparison {φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hφ : ContDiff ℝ 3 φ) (hA : ContDiff ℝ 2 A)
    {R c s C₀ C₁ M : ℝ} (hs : 0 < s) (hrR : 1/s^4 ≤ R)
    (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : φ 0 = 0) (hcrit : deriv φ 0 = 0)
    (hsecond0 : iteratedDeriv 2 φ 0 = 2 * Real.pi)
    (hsecond : ∀ x ∈ Icc (-R) R, c ≤ iteratedDeriv 2 φ x)
    (hM : ∀ x ∈ Icc (-R) R, |iteratedDeriv 3 φ x| ≤ M)
    (hAb : ∀ x ∈ Icc (-R) R, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc (-R) R, ‖deriv A x‖ ≤ C₁) :
    ‖(Real.sqrt (s^10) : ℂ) * ((∫ x in -R..R, A x * Complex.exp (I * (s^10 * φ x : ℝ))) -
        A 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * s^10 * x^2 : ℝ))))‖ ≤
      2*C₁/s^3 + C₀*M/(3*s) + 4*(4*C₀+2*R*C₁)/(c*s) := by
  have he : Real.sqrt (s^10) = s^5 := by
    rw [show s^10 = (s^5)^2 by ring, Real.sqrt_sq (by positivity)]
  rw [norm_mul, norm_real, Real.norm_eq_abs, he, abs_of_pos (pow_pos hs 5)]
  have h := stationary_interval_comparison hφ hA (by positivity : 0 < 1/s^4) hrR
    (pow_ne_zero 10 hs.ne') hc hπ hC₀ hC₁ hM₀ hzero hcrit hsecond0 hsecond hM hAb hA'b
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ s^5)
  refine hh.trans_eq ?_
  rw [abs_of_pos (pow_pos hs 10)]
  field_simp
  ring

lemma stationary_interval_comparison_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      ((∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
        A a 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))))
      (fun _ => 0) atTop := by
  let s : ℝ → ℝ := fun t => t ^ ((10 : ℝ)⁻¹)
  have hst : Tendsto s atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hr : Tendsto (fun t : ℝ => 1/(s t)^4) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp hst)
  have hlim : Tendsto (fun t : ℝ =>
      2*C₁/(s t)^3 + C₀*M/(3*(s t)) + 4*(4*C₀+2*R*C₁)/(c*(s t))) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun t => 2*C₁/(s t)^3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hst)
    have h₂ : Tendsto (fun t => C₀*M/(3*(s t))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3) hst)
    have h₃ : Tendsto (fun t => 4*(4*C₀+2*R*C₁)/(c*(s t))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hc hst)
    simpa only [add_zero] using Tendsto.add (Tendsto.add h₁ h₂) h₃
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), hr.eventually (gt_mem_nhds hR),
    hlim.eventually (gt_mem_nhds hε)] with t ht htR htε
  intro a
  have hs : 0 < s t := Real.rpow_pos_of_pos ht _
  have he : (s t)^10 = t := Real.rpow_inv_natCast_pow ht.le (by norm_num)
  rw [dist_comm, dist_zero_right]
  have hh := stationary_interval_scaled_comparison (hφ a) (hA a) hs htR.le hc hπ hC₀ hC₁ hM₀
    (hzero a) (hcrit a) (hsecond0 a) (hsecond a) (hM a) (hAb a) (hA'b a)
  rw [he] at hh
  exact hh.trans_lt htε

lemma quadratic_phase_third (x : ℝ) : iteratedDeriv 3 (fun x : ℝ => Real.pi*x^2) x = 0 := by
  rw [iteratedDeriv_succ,
    show iteratedDeriv 2 (fun x : ℝ => Real.pi*x^2) = fun _ => 2*Real.pi from funext quadratic_phase_second]
  exact deriv_const x (2*Real.pi)

lemma quadratic_interval_limit {R : ℝ} (hR : 0 < R) :
    Tendsto (fun t : ℝ => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, Complex.exp (I * (Real.pi * t * x^2 : ℝ)))) atTop
      (𝓝 (Complex.exp ((Real.pi : ℂ) / 4 * I))) := by
  let b : ContDiffBump (0 : ℝ) := ⟨R/4, R/2, by positivity, by linarith⟩
  let B : ℝ → ℂ := fun x => (b x : ℂ)
  have hBsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  have hB0 : B 0 = 1 := by
    dsimp [B]
    rw [b.one_of_mem_closedBall (by simp [b]; positivity)]
    exact ofReal_one
  have hBb (x : ℝ) : ‖B x‖ ≤ 1 := by
    simp only [B, norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hBsm.continuous_deriv (by norm_num)).continuousOn (s := Icc (-R) R)
  have hC₁pos : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 h0)
  have hQsm : ContDiff ℝ 3 (fun x : ℝ => Real.pi*x^2) := by fun_prop
  have hQ0 : deriv (fun x : ℝ => Real.pi*x^2) 0 = 0 := by rw [quadratic_phase_deriv]; ring
  have hu := stationary_interval_comparison_uniform
    (α := Unit) (φ := fun _ x => Real.pi*x^2) (A := fun _ => B)
    (fun _ => hQsm) (fun _ => hBsm.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hR
    (c := 2*Real.pi) (by positivity) le_rfl (C₀ := 1) (by norm_num) hC₁pos
    (M := 0) (by norm_num) (fun _ => by simp) (fun _ => hQ0)
    (fun _ => quadratic_phase_second 0)
    (fun _ x _ => by rw [quadratic_phase_second])
    (fun _ x _ => by rw [quadratic_phase_third]; simp)
    (fun _ x _ => hBb x) (fun _ x hx => hC₁ x hx)
  have hdiff := hu.tendsto_at ()
  simp only [hB0, one_mul] at hdiff
  have hsupport : Function.support B ⊆ Ioc (-R) R := by
    intro x hx
    have hbx : x ∈ Function.support (b : ℝ → ℝ) := by
      simpa only [Function.mem_support, B, ofReal_ne_zero] using hx
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hbx
    dsimp [b] at hbx
    exact ⟨by linarith [hbx.1], by linarith [hbx.2]⟩
  have hint (t : ℝ) : (∫ x in -R..R, B x * Complex.exp (I * (Real.pi*t*x^2 : ℝ))) =
      (∫ x : ℝ, B x * Complex.exp (I * (Real.pi*t*x^2 : ℝ))) :=
    intervalIntegral.integral_eq_integral_of_support_subset
      ((Function.support_mul_subset_left _ _).trans hsupport)
  have hbcomp : HasCompactSupport B := b.hasCompactSupport.comp_left ofReal_zero
  have hBlim := quadratic_stationary_compact hbcomp hBsm
  simp only [hB0, mul_one] at hBlim
  simp_rw [← hint] at hBlim
  have he (t x : ℝ) : t*(Real.pi*x^2) = Real.pi*t*x^2 := by ring
  simp only [he] at hdiff
  have hh := hBlim.sub hdiff
  simp only [sub_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  ring

lemma stationary_normalized_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun a => A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I)) atTop := by
  have hu := stationary_interval_comparison_uniform hφ hA hR hc hπ hC₀ hC₁ hM₀
    hzero hcrit hsecond0 hsecond hM hAb hA'b
  have hQ := quadratic_interval_limit hR
  have h0 : (0 : ℝ) ∈ Icc (-R) R := ⟨by linarith, hR.le⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hε' : 0 < ε / (2 * (C₀ + 1)) := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.mp hu (ε/2) (by positivity),
    (tendsto_def.mp hQ) _ (Metric.ball_mem_nhds _ hε')] with t ht hQt
  intro a
  change dist _ _ < _ at hQt
  rw [dist_eq_norm] at hQt
  have hh := ht a
  rw [dist_comm, dist_zero_right] at hh
  rw [dist_comm, dist_eq_norm]
  have he : (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      A a 0 * Complex.exp ((Real.pi : ℂ)/4*I) =
    (Real.sqrt t : ℂ) * ((∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      A a 0 * (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ)))) +
      A a 0 * ((Real.sqrt t : ℂ) * (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ)/4*I)) := by ring
  rw [he]
  refine (norm_add_le _ _).trans_lt ?_
  have hprod : ‖A a 0 * ((Real.sqrt t : ℂ) *
      (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ)/4*I))‖ < ε/2 := by
    rw [norm_mul]
    calc
      _ ≤ C₀ * ‖(Real.sqrt t : ℂ) *
        (∫ x in -R..R, Complex.exp (I * (Real.pi*t*x^2 : ℝ))) -
          Complex.exp ((Real.pi : ℂ)/4*I)‖ := mul_le_mul_of_nonneg_right (hAb a 0 h0) (norm_nonneg _)
      _ < (C₀+1) * (ε/(2*(C₀+1))) := by
        exact (mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ C₀+1) (norm_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_left hQt (by positivity))
      _ = ε/2 := by field_simp
  linarith

lemma uniform_rescale {α : Type*} {F : ℝ → α → ℂ} {f b : α → ℂ} {k : α → ℝ}
    (hF : TendstoUniformly F f atTop) {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    (hk : ∀ a, κ ≤ k a) (hb : ∀ a, ‖b a‖ ≤ C) :
    TendstoUniformly (fun t : ℝ => fun a => b a * F (t*k a) a)
      (fun a => b a * f a) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : 0 < ε/(C+1) := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp hF (ε/(C+1)) he)
  filter_upwards [eventually_ge_atTop (max 0 (T/κ))] with t ht
  intro a
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have htk : T ≤ t*k a := by
    calc
      T = (T/κ)*κ := by field_simp
      _ ≤ t*κ := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans ht) hκ.le
      _ ≤ t*k a := mul_le_mul_of_nonneg_left (hk a) ht0
  have h := hT (t*k a) htk a
  rw [dist_eq_norm, ← mul_sub, norm_mul]
  rw [dist_eq_norm] at h
  calc
    _ ≤ (C+1) * ‖f a - F (t*k a) a‖ :=
      mul_le_mul_of_nonneg_right ((hb a).trans (by linarith)) (norm_nonneg _)
    _ < (C+1) * (ε/(C+1)) := mul_lt_mul_of_pos_left h (by positivity)
    _ = ε := by field_simp

lemma stationary_positive_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hzero : ∀ a, φ a 0 = 0) (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun a => (Real.sqrt (k a) : ℂ)⁻¹ * (A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I))) atTop := by
  have hkpos (a : α) : 0 < k a := hκ.trans_le (hk a)
  let ψ : α → ℝ → ℝ := fun a x => (k a)⁻¹ * φ a x
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := contDiff_const.mul (hφ a)
  have hψ0 (a : α) : ψ a 0 = 0 := by simp [ψ, hzero]
  have hψcrit (a : α) : deriv (ψ a) 0 = 0 := by
    simp only [ψ, deriv_const_mul_field, hcrit, mul_zero]
  have hψsecond0 (a : α) : iteratedDeriv 2 (ψ a) 0 = 2 * Real.pi := by
    simp only [ψ, iteratedDeriv_const_mul_field, hsecond0]
    field_simp [(hkpos a).ne']
  have hψsecond (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : c ≤ iteratedDeriv 2 (ψ a) x := by
    dsimp only [ψ]
    rw [iteratedDeriv_const_mul_field, inv_mul_eq_div]
    exact (le_div_iff₀ (hkpos a)).mpr (hsecond a x hx)
  have hψM (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : |iteratedDeriv 3 (ψ a) x| ≤ M := by
    dsimp only [ψ]
    rw [iteratedDeriv_const_mul_field, inv_mul_eq_div, abs_div, abs_of_pos (hkpos a)]
    exact (div_le_iff₀ (hkpos a)).mpr (hM a x hx)
  have hu := stationary_normalized_uniform hψ hA hR hc hπ hC₀ hC₁ hM₀
    hψ0 hψcrit hψsecond0 hψsecond hψM hAb hA'b
  have hb (a : α) : ‖(Real.sqrt (k a) : ℂ)⁻¹‖ ≤ (Real.sqrt κ)⁻¹ := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_anti₀ (Real.sqrt_pos.mpr hκ) (Real.sqrt_le_sqrt (hk a))
  have hv := uniform_rescale hu hκ (by positivity : 0 ≤ (Real.sqrt κ)⁻¹) hk hb
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hv ε hε, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro a
  have he (x : ℝ) : (t*k a) * ψ a x = t * φ a x := by
    dsimp [ψ]
    field_simp [(hkpos a).ne']
  have hs : (Real.sqrt (k a) : ℂ)⁻¹ * (Real.sqrt (t*k a) : ℂ) = (Real.sqrt t : ℂ) := by
    rw [Real.sqrt_mul ht0, ofReal_mul]
    field_simp [ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hkpos a)).ne']
  have hh := ht a
  simp_rw [he] at hh
  simpa only [← mul_assoc, hs] using hh

lemma stationary_positive_error_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hcrit : ∀ a, deriv (φ a) 0 = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) 0 = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc (-R) R → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc (-R) R → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc (-R) R → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (-R) R → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => φ a x - φ a 0
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).sub contDiff_const
  have hψD (a : α) : deriv (ψ a) 0 = 0 := by
    dsimp only [ψ]; rw [deriv_sub_const, hcrit]
  have hψDD (a : α) (n : ℕ) (hn : 0 < n) (x : ℝ) :
      iteratedDeriv n (ψ a) x = iteratedDeriv n (φ a) x := by
    simpa only [ψ, sub_eq_add_neg, add_comm] using
      (iteratedDeriv_const_add (f := φ a) (x := x) hn (-φ a 0))
  have hu := stationary_positive_uniform hψ hA hR hc hπ hκ hk hC₀ hC₁ hM₀
    (fun a => sub_self _) hψD (by simpa only [hψDD _ 2 (by norm_num)] using hsecond0)
    (by simpa only [hψDD _ 2 (by norm_num)] using hsecond)
    (by simpa only [hψDD _ 3 (by norm_num)] using hM) hAb hA'b
  have hi (a : α) (t : ℝ) :
      (∫ x in -R..R, A a x * Complex.exp (I * (t * φ a x : ℝ))) =
      Complex.exp (I * (t * φ a 0 : ℝ)) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [show Complex.exp (I * (t * φ a 0 : ℝ)) *
      (A a x * Complex.exp (I * (t * ψ a x : ℝ))) = A a x *
        (Complex.exp (I * (t * φ a 0 : ℝ)) * Complex.exp (I * (t * ψ a x : ℝ))) by ring,
      ← Complex.exp_add]
    congr 2
    dsimp [ψ]
    push_cast
    ring
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hu ε hε] with t ht
  intro a
  rw [dist_comm, dist_zero_right, hi]
  have he : (Real.sqrt t : ℂ) * (Complex.exp (I * (t * φ a 0 : ℝ)) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ)))) -
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a 0 * Complex.exp ((Real.pi : ℂ)/4*I))) =
      Complex.exp (I * (t * φ a 0 : ℝ)) * ((Real.sqrt t : ℂ) *
        (∫ x in -R..R, A a x * Complex.exp (I * (t * ψ a x : ℝ))) -
        (Real.sqrt (k a) : ℂ)⁻¹ * (A a 0 * Complex.exp ((Real.pi : ℂ)/4*I))) := by ring
  rw [he, norm_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [dist_eq_norm, norm_sub_rev] using ht a

lemma nonstationary_scaled_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u : α → ℝ} {r C₀ C₁ D : ℝ} (hr : 0 < r) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hlu : ∀ a, l a ≤ u a) (hD : ∀ a, u a - l a ≤ D)
    (hsecond : ∀ a x, x ∈ Icc (l a) (u a) → 0 ≤ iteratedDeriv 2 (φ a) x)
    (hsep : ∀ a x, x ∈ Icc (l a) (u a) → r ≤ |deriv (φ a) x|)
    (hAb : ∀ a x, x ∈ Icc (l a) (u a) → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l a) (u a) → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l a..u a, A a x * Complex.exp (I * (t * φ a x : ℝ))))
      (fun _ => 0) atTop := by
  have hbound (a : α) {t : ℝ} (ht : 0 < t) :
      ‖(Real.sqrt t : ℂ) * (∫ x in l a..u a, A a x * Complex.exp (I * (t * φ a x : ℝ)))‖ ≤
        ((4*C₀+D*C₁)/r) / Real.sqrt t := by
    have hq : ContDiff ℝ 2 (deriv (φ a)) := by
      simpa using ((hφ a).of_le (by norm_num : (2 : WithTop ℕ∞)+1 ≤ 3)).deriv'
    have hh := nonstationary_monotone_bound (hlu a) ht.ne' hr hC₀ hC₁
      (φ := φ a) (q := deriv (φ a)) (q' := deriv (deriv (φ a))) (A := A a) (A' := deriv (A a))
      (fun x _ => ((hφ a).differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
      (fun x _ => ((hA a).differentiable (by norm_num) x).hasDerivAt)
      (hq.continuous_deriv (by norm_num)).continuousOn
      ((hA a).continuous_deriv (by norm_num)).continuousOn
      (by simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hsecond a)
      (hsep a) (hAb a) (hA'b a)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    calc
      _ ≤ Real.sqrt t * ((4*C₀+(u a-l a)*C₁)/(|t| * r)) :=
        mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg t)
      _ ≤ Real.sqrt t * ((4*C₀+D*C₁)/(t*r)) := by
        rw [abs_of_pos ht]
        gcongr
        exact hD a
      _ = _ := by
        have hs := Real.sq_sqrt ht.le
        have hs0 := (Real.sqrt_pos.mpr ht).ne'
        field_simp
        rw [hs]
        ring
  have hlim := Real.tendsto_sqrt_atTop.const_div_atTop ((4*C₀+D*C₁)/r)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro a
  rw [dist_zero_left]
  exact (hbound a ht0).trans_lt ht

lemma derivative_coercive_center {q : ℝ → ℝ} {l u v c : ℝ}
    (hq : Differentiable ℝ q) (hv : v ∈ Icc l u) (hqv : q v = 0)
    (hc : ∀ x ∈ Icc l u, c ≤ deriv q x) :
    ∀ x ∈ Icc l u, c * |x-v| ≤ |q x| := by
  intro x hx
  have h := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => hc x (interior_subset hx))
  rcases le_total v x with hp | hn
  · have hh := h v hv x hx hp
    rw [hqv, sub_zero] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr hp)]
    exact hh.trans (le_abs_self _)
  · have hh := h x hx v hv hn
    rw [hqv, zero_sub, ← neg_sub x v, mul_neg] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr hn)]
    simpa only [mul_neg] using hh.trans (neg_le_abs _)

lemma stationary_positive_moving_uniform {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {k v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R c κ C₀ C₁ M : ℝ} (hR : 0 < R) (hc : 0 < c) (hπ : c ≤ 2 * Real.pi)
    (hκ : 0 < κ) (hk : ∀ a, κ ≤ k a)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond0 : ∀ a, iteratedDeriv 2 (φ a) (v a) = 2 * Real.pi * k a)
    (hsecond : ∀ a x, x ∈ Icc l u → c*k a ≤ iteratedDeriv 2 (φ a) x)
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M*k a)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) * ((Real.sqrt (k a) : ℂ)⁻¹ *
        (A a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  let ψ : α → ℝ → ℝ := fun a x => φ a (x+v a)
  let B : α → ℝ → ℂ := fun a x => A a (x+v a)
  have hψ (a : α) : ContDiff ℝ 3 (ψ a) := (hφ a).comp (contDiff_id.add contDiff_const)
  have hB (a : α) : ContDiff ℝ 2 (B a) := (hA a).comp (contDiff_id.add contDiff_const)
  have hi (a : α) (x : ℝ) (hx : x ∈ Icc (-R) R) : x+v a ∈ Icc l u := by
    constructor <;> have := hv a <;> rcases hx with ⟨hx₁,hx₂⟩ <;> linarith
  have hcenter := stationary_positive_error_uniform hψ hB hR hc hπ hκ hk hC₀ hC₁ hM₀
    (by intro a; simpa only [ψ, deriv_comp_add_const, zero_add] using hcrit a)
    (by intro a; simpa only [ψ, iteratedDeriv_comp_add_const, zero_add] using hsecond0 a)
    (by intro a x hx; simpa only [ψ, iteratedDeriv_comp_add_const] using hsecond a (x+v a) (hi a x hx))
    (by intro a x hx; simpa only [ψ, iteratedDeriv_comp_add_const] using hM a (x+v a) (hi a x hx))
    (by intro a x hx; exact hAb a (x+v a) (hi a x hx))
    (by intro a x hx; simpa only [B, deriv_comp_add_const] using hA'b a (x+v a) (hi a x hx))
  have htt (a : α) (t : ℝ) : (∫ x in -R..R, B a x * Complex.exp (I * (t * ψ a x : ℝ))) =
      ∫ x in v a-R..v a+R, A a x * Complex.exp (I * (t * φ a x : ℝ)) := by
    simpa only [B, ψ, neg_add_eq_sub, add_comm R (v a)] using
      intervalIntegral.integral_comp_add_right (a := -R) (b := R)
        (fun x => A a x * Complex.exp (I * (t * φ a x : ℝ))) (v a)
  simp_rw [htt] at hcenter
  have hpos (a : α) (x : ℝ) (hx : x ∈ Icc l u) : 0 ≤ iteratedDeriv 2 (φ a) x :=
    (mul_pos hc (hκ.trans_le (hk a))).le.trans (hsecond a x hx)
  have hco (a : α) (x : ℝ) (hx : x ∈ Icc l u) : c*κ*|x-v a| ≤ |deriv (φ a) x| := by
    apply derivative_coercive_center
      (((hφ a).deriv' : ContDiff ℝ 2 (deriv (φ a))).differentiable (by norm_num))
      (c := c*κ) (v := v a) (by constructor <;> have := hv a <;> linarith) (hcrit a) _ x hx
    intro y hy
    have := (mul_le_mul_of_nonneg_left (hk a) hc.le).trans (hsecond a y hy)
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using this
  have hleftsub (a : α) : Icc l (v a-R) ⊆ Icc l u :=
    Icc_subset_Icc le_rfl (by have := hv a; linarith)
  have hrightsub (a : α) : Icc (v a+R) u ⊆ Icc l u :=
    Icc_subset_Icc (by have := hv a; linarith) le_rfl
  have hleft := nonstationary_scaled_uniform hφ hA (mul_pos (mul_pos hc hκ) hR) hC₀ hC₁
    (l := fun _ => l) (u := fun a => v a-R) (D := u-l)
    (by intro a; have := hv a; linarith) (by intro a; have := hv a; linarith)
    (fun a x hx => hpos a x (hleftsub a hx))
    (by intro a x hx
        apply le_trans _ (hco a x (hleftsub a hx))
        apply mul_le_mul_of_nonneg_left _ (mul_pos hc hκ).le
        rw [abs_of_nonpos (by rcases hx with ⟨h₁,h₂⟩; linarith)]
        rcases hx with ⟨h₁,h₂⟩; linarith)
    (fun a x hx => hAb a x (hleftsub a hx)) (fun a x hx => hA'b a x (hleftsub a hx))
  have hright := nonstationary_scaled_uniform hφ hA (mul_pos (mul_pos hc hκ) hR) hC₀ hC₁
    (l := fun a => v a+R) (u := fun _ => u) (D := u-l)
    (by intro a; have := hv a; linarith) (by intro a; have := hv a; linarith)
    (fun a x hx => hpos a x (hrightsub a hx))
    (by intro a x hx
        apply le_trans _ (hco a x (hrightsub a hx))
        apply mul_le_mul_of_nonneg_left _ (mul_pos hc hκ).le
        rw [abs_of_nonneg (by rcases hx with ⟨h₁,h₂⟩; linarith)]
        rcases hx with ⟨h₁,h₂⟩; linarith)
    (fun a x hx => hAb a x (hrightsub a hx)) (fun a x hx => hA'b a x (hrightsub a hx))
  convert (hleft.add hcenter).add hright using 1
  · ext t a
    dsimp only [Pi.add_apply, B, ψ, zero_add]
    have hF : Continuous (fun x => A a x * Complex.exp (I * (t * φ a x : ℝ))) := by fun_prop
    have hs := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (a := l) (b := v a-R))
      (hF.intervalIntegrable (μ := volume) (a := v a-R) (b := v a+R))
    have hs' := intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (μ := volume) (a := l) (b := v a+R))
      (hF.intervalIntegrable (μ := volume) (a := v a+R) (b := u))
    rw [← hs', ← hs]
    ring_nf
  · ext a; simp

/-- Uniform stationary phase with ordinary lower and upper curvature bounds. -/
lemma stationary_positive_moving_of_bounds {α : Type*} {φ : α → ℝ → ℝ} {A : α → ℝ → ℂ}
    {v : α → ℝ} (hφ : ∀ a, ContDiff ℝ 3 (φ a)) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {l u R d D C₀ C₁ M : ℝ} (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hv : ∀ a, l+R ≤ v a ∧ v a ≤ u-R)
    (hcrit : ∀ a, deriv (φ a) (v a) = 0)
    (hsecond : ∀ a x, x ∈ Icc l u → d ≤ iteratedDeriv 2 (φ a) x)
    (hupper : ∀ a x, x ∈ Icc l u → iteratedDeriv 2 (φ a) x ≤ D)
    (hM : ∀ a x, x ∈ Icc l u → |iteratedDeriv 3 (φ a) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc l u → ‖A a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc l u → ‖deriv (A a) x‖ ≤ C₁) :
    TendstoUniformly (fun t : ℝ => fun a => (Real.sqrt t : ℂ) *
      (∫ x in l..u, A a x * Complex.exp (I * (t * φ a x : ℝ))) -
      Complex.exp (I * (t * φ a (v a) : ℝ)) *
        ((Real.sqrt (iteratedDeriv 2 (φ a) (v a) / (2*Real.pi)) : ℂ)⁻¹ *
          (A a (v a) * Complex.exp ((Real.pi : ℂ) / 4 * I))))
      (fun _ => 0) atTop := by
  have hπ : 0 < 2*Real.pi := by positivity
  have hD : 0 < D := hd.trans_le hdD
  have hv' (a : α) : v a ∈ Icc l u := by
    constructor <;> have := hv a <;> linarith
  let k : α → ℝ := fun a => iteratedDeriv 2 (φ a) (v a)/(2*Real.pi)
  have hk (a : α) : d/(2*Real.pi) ≤ k a :=
    div_le_div_of_nonneg_right (hsecond a (v a) (hv' a)) hπ.le
  have hk' (a : α) : k a ≤ D/(2*Real.pi) :=
    div_le_div_of_nonneg_right (hupper a (v a) (hv' a)) hπ.le
  refine stationary_positive_moving_uniform hφ hA hR (c := d*(2*Real.pi)/D)
    (div_pos (mul_pos hd hπ) hD) ?_ (div_pos hd hπ) hk hC₀ hC₁
    (M := M/(d/(2*Real.pi))) (div_nonneg hM₀ (div_pos hd hπ).le) hv hcrit ?_ ?_ ?_ hAb hA'b
  · exact (div_le_iff₀ hD).mpr (by nlinarith)
  · intro a
    field_simp
  · intro a x hx
    calc
      d*(2*Real.pi)/D*k a ≤ d*(2*Real.pi)/D*(D/(2*Real.pi)) :=
        mul_le_mul_of_nonneg_left (hk' a) (by positivity)
      _ = d := by field_simp
      _ ≤ _ := hsecond a x hx
  · intro a x hx
    apply (hM a x hx).trans
    calc
      M = (M/(d/(2*Real.pi)))*(d/(2*Real.pi)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hk a) (by positivity)

lemma deriv_sub_linear_phase {Φ : ℝ → ℝ} (hΦ : Differentiable ℝ Φ) (s x : ℝ) :
    deriv (fun x => Φ x-s*x) x = deriv Φ x-s := by
  rw [deriv_fun_sub (f := Φ) (g := fun x => s*x) (hΦ x) (by fun_prop)]
  simp

lemma iteratedDeriv_sub_linear_phase {Φ : ℝ → ℝ} {n : ℕ}
    (hΦ : ContDiff ℝ n Φ) (hn : 2 ≤ n) (s x : ℝ) :
    iteratedDeriv n (fun x => Φ x-s*x) x = iteratedDeriv n Φ x := by
  rw [iteratedDeriv_fun_sub (f := Φ) (g := fun x => s*x) hΦ.contDiffAt (by fun_prop)]
  have hl : iteratedDeriv n (fun x : ℝ => s*x) x = 0 := by
    calc
      _ = s * iteratedDeriv n (id : ℝ → ℝ) x := iteratedDeriv_const_mul_field s id
      _ = 0 := by simp [iteratedDeriv_id, show n ≠ 0 by omega, show n ≠ 1 by omega]
  rw [hl, sub_zero]

lemma stationary_branch_center {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    {a b : ℝ} (hab : a ≤ b) {s : ℝ} (hs : s ∈ Icc (deriv Φ a) (deriv Φ b)) :
    Function.invFunOn (deriv Φ) (Icc a b) s ∈ Icc a b ∧
      deriv Φ (Function.invFunOn (deriv Φ) (Icc a b) s) = s := by
  have hh := intermediate_value_Icc hab (hΦ.continuous_deriv (by norm_num)).continuousOn hs
  exact Function.invFunOn_pos hh

lemma intervalIntegral_phase_of_support {A : ℝ → ℂ} {a b : ℝ}
    (hA : Function.support A ⊆ Ioc a b) (Φ : ℝ → ℝ) (t : ℝ) :
    (∫ x in a..b, A x * Complex.exp (I * (t*Φ x : ℝ))) =
      ∫ x, A x * Complex.exp (I * (t*Φ x : ℝ)) := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  apply hA
  exact (mul_ne_zero_iff.mp hx).1

lemma phase_nonstationary_off_branch {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d C₀ C₁ : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α ×
      {s : ℝ // s ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R))} =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2.val*x) : ℝ))))
        (fun _ => 0) atTop := by
  let β := α × {s : ℝ // s ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R))}
  let φ : β → ℝ → ℝ := fun p x => Φ x-p.2.val*x
  let B : β → ℝ → ℂ := fun p => A p.1
  have hφ (p : β) : ContDiff ℝ 3 (φ p) := hΦ.sub (contDiff_const.mul contDiff_id)
  have hB (p : β) : ContDiff ℝ 2 (B p) := hA p.1
  have hi : Icc a b ⊆ Icc (a-2*R) (b+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hq : Differentiable ℝ (deriv Φ) :=
    (hΦ.deriv' : ContDiff ℝ 2 (deriv Φ)).differentiable (by norm_num)
  have hmv := (convex_Icc (a-2*R) (b+2*R)).mul_sub_le_image_sub_of_le_deriv
    hq.continuous.continuousOn hq.differentiableOn
    (fun x hx => show d ≤ deriv (deriv Φ) x from by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        hsecond x (interior_subset hx))
  have hlo : a-R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hhi : b+R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hsep (p : β) (x : ℝ) (hx : x ∈ Icc a b) : d*R ≤ |deriv (φ p) x| := by
    rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num))]
    have hp := p.2.property
    simp only [mem_Icc, not_and_or, not_le] at hp
    rcases hp with hp | hp
    · have hm := hmv (a-R) hlo x (hi hx) (by rcases hx with ⟨h₁,h₂⟩; linarith)
      have hd' : d*R ≤ deriv Φ x-p.2.val := by
        have hxx : R ≤ x-(a-R) := by rcases hx with ⟨h₁,h₂⟩; linarith
        have := mul_le_mul_of_nonneg_left hxx hd.le
        linarith
      exact hd'.trans (le_abs_self _)
    · have hm := hmv x (hi hx) (b+R) hhi (by rcases hx with ⟨h₁,h₂⟩; linarith)
      have hd' : d*R ≤ -(deriv Φ x-p.2.val) := by
        have hxx : R ≤ b+R-x := by rcases hx with ⟨h₁,h₂⟩; linarith
        have := mul_le_mul_of_nonneg_left hxx hd.le
        linarith
      exact hd'.trans (neg_le_abs _)
  have hu := nonstationary_scaled_uniform hφ hB (mul_pos hd hR) hC₀ hC₁
    (l := fun _ => a) (u := fun _ => b) (D := b-a)
    (fun _ => hab) (fun _ => le_rfl)
    (by intro p x hx
        rw [iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num)]
        exact hd.le.trans (hsecond x (hi hx))) hsep
    (fun p x hx => hAb p.1 x (hi hx)) (fun p x hx => hA'b p.1 x (hi hx))
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  ext t p
  rw [intervalIntegral_phase_of_support (hsupp p.1)]

lemma phase_stationary_on_branch {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α ×
      {s : ℝ // s ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))} =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2.val*x) : ℝ))) -
        stationaryLeading Φ (A p.1) (a-R) (b+R) p.2.val t)
        (fun _ => 0) atTop := by
  let β := α × {s : ℝ // s ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))}
  let φ : β → ℝ → ℝ := fun p x => Φ x-p.2.val*x
  let B : β → ℝ → ℂ := fun p => A p.1
  let v : β → ℝ := fun p => Function.invFunOn (deriv Φ) (Icc (a-R) (b+R)) p.2.val
  have hv (p : β) : v p ∈ Icc (a-R) (b+R) ∧ deriv Φ (v p) = p.2.val :=
    stationary_branch_center (hΦ.of_le (by norm_num)) (by linarith) p.2.property
  have hφ (p : β) : ContDiff ℝ 3 (φ p) := hΦ.sub (contDiff_const.mul contDiff_id)
  have hB (p : β) : ContDiff ℝ 2 (B p) := hA p.1
  have h2 (p : β) (x : ℝ) : iteratedDeriv 2 (φ p) x = iteratedDeriv 2 Φ x :=
    iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num) p.2.val x
  have h3 (p : β) (x : ℝ) : iteratedDeriv 3 (φ p) x = iteratedDeriv 3 Φ x :=
    iteratedDeriv_sub_linear_phase hΦ (by norm_num) p.2.val x
  have hu := stationary_positive_moving_of_bounds hφ hB hR hd hdD hC₀ hC₁ hM₀
    (l := a-2*R) (u := b+2*R) (v := v)
    (by intro p; constructor <;> have := (hv p).1 <;> rcases this with ⟨h₁,h₂⟩ <;> linarith)
    (by intro p; rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num)), (hv p).2, sub_self])
    (by intro p x hx; rw [h2]; exact hsecond x hx)
    (by intro p x hx; rw [h2]; exact hupper x hx)
    (by intro p x hx; rw [h3]; exact hM x hx)
    (fun p x hx => hAb p.1 x hx) (fun p x hx => hA'b p.1 x hx)
  have hs (p : β) : Function.support (B p) ⊆ Ioc (a-2*R) (b+2*R) := by
    intro x hx
    have hh := hsupp p.1 hx
    constructor <;> rcases hh with ⟨h₁,h₂⟩ <;> linarith
  simp_rw [intervalIntegral_phase_of_support (hs _), h2] at hu
  convert hu using 1
  all_goals try with_reducible_and_instances rfl
  ext t p
  simp only [stationaryLeading, ite_eq_left p.2.property]
  rfl

/-- Compactly supported, parameter-uniform stationary phase, including the
noncritical region and zero amplitudes. No weak-convergence replacement is used. -/
lemma compact_support_stationary_uniform {α : Type*} {Φ : ℝ → ℝ} {A : α → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ a, ContDiff ℝ 2 (A a))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) :
    TendstoUniformly (fun t : ℝ => fun p : α × ℝ =>
      (Real.sqrt t : ℂ) * (∫ x, A p.1 x * Complex.exp (I * (t*(Φ x-p.2*x) : ℝ))) -
        stationaryLeading Φ (A p.1) (a-R) (b+R) p.2 t)
        (fun _ => 0) atTop := by
  have hin := phase_stationary_on_branch hΦ hA hab hR hd hdD hC₀ hC₁ hM₀
    hsecond hupper hM hAb hA'b hsupp
  have hout := phase_nonstationary_off_branch hΦ hA hab hR hd hC₀ hC₁ hsecond hAb hA'b hsupp
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hin ε hε,
    Metric.tendstoUniformly_iff.mp hout ε hε] with t ht₁ ht₂
  intro p
  by_cases hp : p.2 ∈ Icc (deriv Φ (a-R)) (deriv Φ (b+R))
  · exact ht₁ (p.1, ⟨p.2,hp⟩)
  · simpa only [stationaryLeading, ite_eq_right hp, sub_zero] using ht₂ (p.1, ⟨p.2,hp⟩)

lemma norm_stationaryLeading {Φ : ℝ → ℝ} {A : ℝ → ℂ} {l u s t : ℝ}
    (hs : s ∈ Icc (deriv Φ l) (deriv Φ u)) :
    ‖stationaryLeading Φ A l u s t‖ =
      (Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s) /
        (2*Real.pi)))⁻¹ * ‖A (Function.invFunOn (deriv Φ) (Icc l u) s)‖ := by
  simp only [stationaryLeading, ite_eq_left hs, norm_mul, norm_inv]
  simp [Complex.norm_exp, mul_re, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

lemma stationaryLeading_bound {Φ : ℝ → ℝ} {A : ℝ → ℂ} {l u s t d C : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hlu : l ≤ u) (hd : 0 < d) (hC : 0 ≤ C)
    (hsecond : ∀ x ∈ Icc l u, d ≤ iteratedDeriv 2 Φ x)
    (hA : ∀ x ∈ Icc l u, ‖A x‖ ≤ C) :
    ‖stationaryLeading Φ A l u s t‖ ≤ C / Real.sqrt (d/(2*Real.pi)) := by
  by_cases hs : s ∈ Icc (deriv Φ l) (deriv Φ u)
  · rw [norm_stationaryLeading hs]
    have hv := (stationary_branch_center hΦ hlu hs).1
    have hd' : 0 < d/(2*Real.pi) := by positivity
    have hroot : Real.sqrt (d/(2*Real.pi)) ≤
        Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s)/(2*Real.pi)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hsecond _ hv) (by positivity))
    calc
      _ ≤ (Real.sqrt (iteratedDeriv 2 Φ (Function.invFunOn (deriv Φ) (Icc l u) s)/(2*Real.pi)))⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hA _ hv) (by positivity)
      _ ≤ (Real.sqrt (d/(2*Real.pi)))⁻¹ * C := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hd') hroot) hC
      _ = _ := by ring
  · simp only [stationaryLeading, ite_eq_right hs, norm_zero]
    positivity

lemma compact_phase_tail_bound {Φ : ℝ → ℝ} {A : ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ContDiff ℝ 2 A)
    {a b t s M C₀ C₁ : ℝ} (hab : a ≤ b) (ht : 0 < t) (hs : s ≠ 0)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsM : 2*M ≤ |s|)
    (hfirst : ∀ x ∈ Icc a b, |deriv Φ x| ≤ M)
    (hsecond : ∀ x ∈ Icc a b, 0 ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ x ∈ Icc a b, ‖A x‖ ≤ C₀)
    (hA'b : ∀ x ∈ Icc a b, ‖deriv A x‖ ≤ C₁)
    (hsupp : Function.support A ⊆ Ioc a b) :
    ‖∫ x, A x * Complex.exp (I * (t*(Φ x-s*x) : ℝ))‖ ≤
      2*(4*C₀+(b-a)*C₁)/(t*|s|) := by
  let φ : ℝ → ℝ := fun x => Φ x-s*x
  have hφ : ContDiff ℝ 3 φ := hΦ.sub (contDiff_const.mul contDiff_id)
  have hq : ContDiff ℝ 2 (deriv φ) := hφ.deriv'
  have hsep (x : ℝ) (hx : x ∈ Icc a b) : |s|/2 ≤ |deriv φ x| := by
    rw [deriv_sub_linear_phase (hΦ.differentiable (by norm_num))]
    have htri : |s| ≤ |deriv Φ x-s|+|deriv Φ x| := by
      calc
        _ = |deriv Φ x-(deriv Φ x-s)| := by congr 1; ring
        _ ≤ |deriv Φ x|+|deriv Φ x-s| := by simpa only [Real.norm_eq_abs] using norm_sub_le (deriv Φ x) (deriv Φ x-s)
        _ = _ := by ring
    have hh := hfirst x hx
    linarith
  have hh := nonstationary_monotone_bound hab ht.ne' (half_pos (abs_pos.mpr hs)) hC₀ hC₁
    (φ := φ) (q := deriv φ) (q' := deriv (deriv φ)) (A := A) (A' := deriv A)
    (fun x _ => (hφ.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hq.differentiable (by norm_num) x).hasDerivAt)
    (fun x _ => (hA.differentiable (by norm_num) x).hasDerivAt)
    (hq.continuous_deriv (by norm_num)).continuousOn
    (hA.continuous_deriv (by norm_num)).continuousOn
    (by intro x hx
        have hh := hsecond x hx
        have he := iteratedDeriv_sub_linear_phase (hΦ.of_le (by norm_num)) (by norm_num : 2 ≤ 2) s x
        simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hh.trans he.ge)
    hsep hAb hA'b
  rw [intervalIntegral_phase_of_support hsupp] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_of_pos ht]
  field_simp

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
namespace ThreeTorus

lemma norm_sq_difference_bound (z w : ℂ) {ε L : ℝ} (hε : 0 ≤ ε) (_hL : 0 ≤ L)
    (he : ‖z-w‖ ≤ ε) (hw : ‖w‖ ≤ L) :
    |‖z‖^2-‖w‖^2| ≤ ε*(ε+2*L) := by
  have hz : ‖z‖ ≤ ε+L := by
    calc
      ‖z‖ ≤ ‖z-w‖+‖w‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert w z
      _ ≤ _ := add_le_add he hw
  calc
    _ = |‖z‖-‖w‖| *(‖z‖+‖w‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖z‖+‖w‖)]
      ring
    _ ≤ ε*(ε+2*L) := mul_le_mul ((abs_norm_sub_norm_le z w).trans he)
      (by linarith) (by positivity) hε

lemma stationary_pointwise_mass_bound (z w : ℂ) {N ε L : ℝ} (hN : 0 < N)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (he : ‖(Real.sqrt N : ℂ)*z-w‖ ≤ ε) (hw : ‖w‖ ≤ L) :
    |‖z‖^2-N⁻¹*‖w‖^2| ≤ (ε*(ε+2*L))/N := by
  have h := norm_sq_difference_bound ((Real.sqrt N : ℂ)*z) w hε hL he hw
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hN.le] at h
  apply (le_div_iff₀ hN).mpr
  calc
    _ = |N*‖z‖^2-‖w‖^2| := by
      calc
        _ = |(‖z‖^2-N⁻¹*‖w‖^2)*N| := by rw [abs_mul, abs_of_pos hN]
        _ = _ := by congr 1; field_simp
    _ ≤ _ := h

lemma stationary_integrated_mass_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : Ω → ℂ} {N ε L : ℝ}
    (hN : 0 < N) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hi : Integrable (fun x => |‖C x‖^2-N⁻¹*‖Ld x‖^2|) μ)
    (he : ∀ x, ‖(Real.sqrt N : ℂ)*C x-Ld x‖ ≤ ε) (hw : ∀ x, ‖Ld x‖ ≤ L) :
    (∫ x, |‖C x‖^2-N⁻¹*‖Ld x‖^2| ∂μ) ≤ ε*(ε+2*L)/N := by
  calc
    _ ≤ ∫ _ : Ω, ε*(ε+2*L)/N ∂μ := integral_mono hi (integrable_const _)
      (fun x => stationary_pointwise_mass_bound (C x) (Ld x) hN hε hL (he x) (hw x))
    _ = _ := by simp

lemma integer_band_card_bound (K n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc (-(K*n : ℤ)) (K*n)).card : ℝ) ≤ (2*(K:ℝ)+1)*(n:ℝ) := by
  rw [Int.card_Icc]
  have he : ((K*n : ℤ)+1-(-(K*n : ℤ))).toNat = 2*K*n+1 := by
    have he' : (K*n : ℤ)+1-(-(K*n : ℤ)) = ((2*K*n+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he']
    exact Int.toNat_natCast _
  rw [he]
  push_cast
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma stationary_band_mass_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℤ → Ω → ℂ} {ε L : ℝ}
    (K n : ℕ) (hn : 1 ≤ n) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hi : ∀ j, Integrable (fun x => |‖C j x‖^2-(n:ℝ)⁻¹*‖Ld j x‖^2|) μ)
    (he : ∀ j x, ‖(Real.sqrt n : ℂ)*C j x-Ld j x‖ ≤ ε)
    (hw : ∀ j x, ‖Ld j x‖ ≤ L) :
    (∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), ∫ x, |‖C j x‖^2-(n:ℝ)⁻¹*‖Ld j x‖^2| ∂μ)
      ≤ (2*(K:ℝ)+1)*(ε*(ε+2*L)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  calc
    _ ≤ ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), ε*(ε+2*L)/(n:ℝ) :=
      Finset.sum_le_sum (fun j _ => stationary_integrated_mass_bound hn' hε hL (hi j) (he j) (hw j))
    _ = ((Finset.Icc (-(K*n : ℤ)) (K*n)).card : ℝ)*(ε*(ε+2*L)/(n:ℝ)) := by simp
    _ ≤ ((2*(K:ℝ)+1)*(n:ℝ))*(ε*(ε+2*L)/(n:ℝ)) :=
      mul_le_mul_of_nonneg_right (integer_band_card_bound K n hn) (by positivity)
    _ = _ := by field_simp

lemma integer_band_exhausts (K : ℕ) (hK : 1 ≤ K) (j : ℤ) :
    ∀ᶠ n : ℕ in atTop, j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) := by
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  have hab : |j| ≤ (n : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  have hkn : (n : ℤ) ≤ (K : ℤ)*n := by
    have hKn : n ≤ K*n := by nlinarith
    exact_mod_cast hKn
  simpa only [Finset.mem_Icc] using abs_le.mp (hab.trans hkn)

lemma stationary_tail_mass_tendsto {E : ℕ → ℤ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    {B : ℤ → ℝ} (hB : Summable B)
    (hE0 : ∀ n j, 0 ≤ E n j)
    (hEB : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) → E n j ≤ B j) :
    Tendsto (fun n : ℕ => ∑' j : ℤ,
      if j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) then 0 else E n j) atTop (𝓝 0) := by
  classical
  have hB' : Summable (fun j => |B j|) := hB.abs
  have hh := tendsto_tsum_of_dominated_convergence (bound := fun j => |B j|) hB'
    (f := fun n : ℕ => fun j : ℤ => if j ∈ Finset.Icc (-(K*n : ℤ)) (K*n) then 0 else E n j)
    (g := fun _ : ℤ => (0 : ℝ))
    (fun j => tendsto_const_nhds.congr' (by
      filter_upwards [integer_band_exhausts K hK j] with n hn
      simp only [ite_eq_left hn]))
    (by filter_upwards [hEB] with n hn
        intro j
        split_ifs with hj
        · simp only [norm_zero]; exact abs_nonneg _
        · rw [Real.norm_eq_abs, abs_of_nonneg (hE0 n j)]
          exact (hn j hj).trans (le_abs_self _))
  simpa only [tsum_zero] using hh

lemma stationary_tail_square_bound_summable (D : ℝ) :
    Summable (fun j : ℤ => D^2/(j:ℝ)^2) := by
  simpa only [mul_one_div] using
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left (D^2))

lemma stationary_band_mass_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℕ → ℤ → Ω → ℂ} {L : ℝ}
    (K : ℕ) (hL : 0 ≤ L)
    (hi : ∀ n j, Integrable (fun x => |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2|) μ)
    (he : TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*C n p.1 p.2-Ld n p.1 p.2) (fun _ => 0) atTop)
    (hw : ∀ n j x, ‖Ld n j x‖ ≤ L) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n),
      ∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c : ℝ := 2*(K:ℝ)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let δ : ℝ := min 1 (ε/(2*c*(1+2*L)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε/(2*c*(1+2*L)) := min_le_right _ _
  have hbound : c*(δ*(δ+2*L)) < ε := by
    calc
      _ ≤ c*(δ*(1+2*L)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith : δ+2*L ≤ 1+2*L) hδ.le) hc.le
      _ ≤ c*((ε/(2*c*(1+2*L)))*(1+2*L)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hδ2 (by positivity)) hc.le
      _ = ε/2 := by field_simp
      _ < ε := by linarith
  filter_upwards [Metric.tendstoUniformly_iff.mp he δ hδ,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hb := stationary_band_mass_bound K n hn1 hδ.le hL (hi n)
    (fun j x => by simpa only [dist_zero_left] using (hn (j,x)).le) (hw n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact hb.trans_lt hbound

lemma tsum_band_tail_decomposition {E B : ℤ → ℝ} (S : Finset ℤ)
    (hE : ∀ j, 0 ≤ E j) (hB : Summable B) (hEB : ∀ j ∉ S, E j ≤ B j) :
    (∑' j, E j) = (∑ j ∈ S, E j) + ∑' j, if j ∈ S then 0 else E j := by
  classical
  have hs : HasSum (fun j => if j ∈ S then E j else 0) (∑ j ∈ S, E j) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (s := S)
      (fun j hj => show (if j ∈ S then E j else 0) = 0 by simp [hj]) using 1
    all_goals try with_reducible_and_instances rfl
    exact Finset.sum_congr rfl (fun j hj => by simp [hj])
  have ht : Summable (fun j => if j ∈ S then 0 else E j) := by
    apply hB.abs.of_norm_bounded
    intro j
    split_ifs with hj
    · simp
    · rw [Real.norm_eq_abs, abs_of_nonneg (hE j)]
      exact (hEB j hj).trans (le_abs_self _)
  have hh := hs.add ht.hasSum
  have he (j : ℤ) : (if j ∈ S then E j else 0) + (if j ∈ S then 0 else E j) = E j := by
    split_ifs <;> simp
  exact (hh.congr_fun (fun j => (he j).symm)).tsum_eq

lemma tsum_tendsto_zero_of_band_and_tail {E : ℕ → ℤ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    {B : ℤ → ℝ} (hB : Summable B) (hE0 : ∀ n j, 0 ≤ E n j)
    (hEB : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) → E n j ≤ B j)
    (hc : Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(K*n : ℤ)) (K*n), E n j) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, E n j) atTop (𝓝 0) := by
  have ht := stationary_tail_mass_tendsto hK hB hE0 hEB
  have hh := hc.add ht
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hEB] with n hn
  exact (tsum_band_tail_decomposition _ (hE0 n) hB hn).symm

/-- Summed L¹ coefficient-mass conclusion; unlike weak convergence this controls
all retained index subarrays and their pushforwards. -/
lemma summed_stationary_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {C Ld : ℕ → ℤ → Ω → ℂ} {L D : ℝ}
    (K : ℕ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hi : ∀ n j, Integrable (fun x => |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2|) μ)
    (he : TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*C n p.1 p.2-Ld n p.1 p.2) (fun _ => 0) atTop)
    (hw : ∀ n j x, ‖Ld n j x‖ ≤ L)
    (ht : ∀ᶠ n : ℕ in atTop, ∀ j, j ∉ Finset.Icc (-(K*n : ℤ)) (K*n) →
      (∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) ≤ D^2/(j:ℝ)^2) :
    Tendsto (fun n : ℕ => ∑' j : ℤ,
      ∫ x, |‖C n j x‖^2-(n:ℝ)⁻¹*‖Ld n j x‖^2| ∂μ) atTop (𝓝 0) := by
  exact tsum_tendsto_zero_of_band_and_tail hK (stationary_tail_square_bound_summable D)
    (by intros; positivity) ht (stationary_band_mass_tendsto K hL hi he hw)

end ThreeTorus

namespace ThreeTorus

lemma passage_uniform_error {Ω : Type*} {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d D C₀ C₁ M : ℝ} (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b) (κ : ℝ) (α : ℕ → ℝ) :
    TendstoUniformly (fun n : ℕ => fun p : ℤ × Ω =>
      (Real.sqrt n : ℂ)*passageCoefficient Φ A κ α n p.1 p.2 -
        passageLeading Φ A a b R κ α n p.1 p.2) (fun _ => 0) atTop := by
  have hh := compact_support_stationary_uniform hΦ hA hab hR hd hdD hC₀ hC₁ hM₀
    hsecond hupper hM hAb hA'b hsupp
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ))
    (Metric.tendstoUniformly_iff.mp hh ε hε)] with n hn
  intro p
  exact hn (p.2, passageSlope κ α n p.1)

lemma passageSlope_large {κ C M : ℝ} {α : ℕ → ℝ} {K n : ℕ} {j : ℤ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hK : 2*(C+M+1) ≤ κ*K)
    (hn : 1 ≤ n) (hα : |α n| ≤ C) (hj : j ∉ Finset.Icc (-(K*n : ℤ)) (K*n)) :
    2*M < |passageSlope κ α n j| ∧
      κ*|(j:ℝ)|/(2*(n:ℝ)) ≤ |passageSlope κ α n j| ∧ j ≠ 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hj' : (K:ℝ)*n < |(j:ℝ)| := by
    have hji : (K:ℤ)*n < |j| := by
      simpa only [Finset.mem_Icc, ← abs_le, not_le] using hj
    exact_mod_cast hji
  have hv : κ*K < κ*|(j:ℝ)|/(n:ℝ) := by
    apply (lt_div_iff₀ hn').mpr
    nlinarith
  have htri : κ*|(j:ℝ)|/(n:ℝ)-C ≤ |passageSlope κ α n j| := by
    have ht := abs_sub_abs_le_abs_sub (κ*(j:ℝ)/(n:ℝ)) (α n)
    rw [abs_div, abs_mul, abs_of_pos hκ, abs_of_pos hn'] at ht
    dsimp [passageSlope]
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [show κ*|(j:ℝ)|/(2*(n:ℝ)) = (κ*|(j:ℝ)|/(n:ℝ))/2 by ring]
    linarith
  · intro he
    subst j
    simp only [Int.cast_zero, abs_zero] at hj'
    have : 0 ≤ (K:ℝ)*n := by positivity
    linarith

lemma passage_arrays_tail {Ω : Type*} {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d C₀ C₁ M C κ : ℝ} {α : ℕ → ℝ} {K n : ℕ} {j : ℤ}
    (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hκ : 0 < κ) (hK : 2*(C+M+1) ≤ κ*K)
    (hn : 1 ≤ n) (hα : |α n| ≤ C)
    (hfirst : ∀ x ∈ Icc (a-2*R) (b+2*R), |deriv Φ x| ≤ M)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b)
    (hj : j ∉ Finset.Icc (-(K*n:ℤ)) (K*n)) (z : Ω) :
    passageLeading Φ A a b R κ α n j z = 0 ∧
      ‖passageCoefficient Φ A κ α n j z‖ ≤ (4*(4*C₀+(b-a)*C₁)/κ)/|(j:ℝ)| := by
  obtain ⟨hlarge,hlower,hj0⟩ := passageSlope_large hκ hC hM hK hn hα hj
  have hn' : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsub : Icc a b ⊆ Icc (a-2*R) (b+2*R) := by intro x hx; constructor <;> linarith [hx.1,hx.2]
  have hleft : a-R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hright : b+R ∈ Icc (a-2*R) (b+2*R) := by constructor <;> linarith
  have hnot : passageSlope κ α n j ∉ Icc (deriv Φ (a-R)) (deriv Φ (b+R)) := by
    intro hh
    have hl := abs_le.mp (hfirst _ hleft)
    have hr := abs_le.mp (hfirst _ hright)
    have hh' : |passageSlope κ α n j| ≤ M := abs_le.mpr ⟨hl.1.trans hh.1,hh.2.trans hr.2⟩
    linarith
  refine ⟨by simp only [passageLeading, stationaryLeading, ite_eq_right hnot], ?_⟩
  have hs : passageSlope κ α n j ≠ 0 := abs_pos.mp (lt_of_le_of_lt (by positivity : 0 ≤ 2*M) hlarge)
  have hb := compact_phase_tail_bound hΦ (hA z) hab hn' hs hC₀ hC₁ hlarge.le
    (fun x hx => hfirst x (hsub hx)) (fun x hx => hd.le.trans (hsecond x (hsub hx)))
    (fun x hx => hAb z x (hsub hx)) (fun x hx => hA'b z x (hsub hx)) (hsupp z)
  apply hb.trans
  have hjpos : 0 < |(j:ℝ)| := abs_pos.mpr (by exact_mod_cast hj0)
  have hnum : 0 ≤ 2*(4*C₀+(b-a)*C₁) := by positivity
  calc
    _ ≤ (2*(4*C₀+(b-a)*C₁))/((n:ℝ)*(κ*|(j:ℝ)|/(2*(n:ℝ)))) :=
      div_le_div_of_nonneg_left hnum (by positivity) (mul_le_mul_of_nonneg_left hlower hn'.le)
    _ = _ := by field_simp; ring

/-- The strong summed mass estimate used in the passage lemma. -/
lemma passage_summed_mass {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Φ : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hΦ : ContDiff ℝ 3 Φ) (hA : ∀ z, ContDiff ℝ 2 (A z))
    {a b R d D C₀ C₁ M M₁ C κ : ℝ} {α : ℕ → ℝ}
    (hab : a ≤ b) (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hα : ∀ n, |α n| ≤ C)
    (hfirst : ∀ x ∈ Icc (a-2*R) (b+2*R), |deriv Φ x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (a-2*R) (b+2*R), d ≤ iteratedDeriv 2 Φ x)
    (hupper : ∀ x ∈ Icc (a-2*R) (b+2*R), iteratedDeriv 2 Φ x ≤ D)
    (hM : ∀ x ∈ Icc (a-2*R) (b+2*R), |iteratedDeriv 3 Φ x| ≤ M)
    (hAb : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖A z x‖ ≤ C₀)
    (hA'b : ∀ z x, x ∈ Icc (a-2*R) (b+2*R) → ‖deriv (A z) x‖ ≤ C₁)
    (hsupp : ∀ z, Function.support (A z) ⊆ Ioc a b)
    (hi : ∀ n j, Integrable (fun z => |‖passageCoefficient Φ A κ α n j z‖^2 -
      (n:ℝ)⁻¹*‖passageLeading Φ A a b R κ α n j z‖^2|) μ) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ z,
      |‖passageCoefficient Φ A κ α n j z‖^2 -
        (n:ℝ)⁻¹*‖passageLeading Φ A a b R κ α n j z‖^2| ∂μ) atTop (𝓝 0) := by
  obtain ⟨K₀,hK₀⟩ := exists_nat_ge (2*(C+M₁+1)/κ)
  let K := max K₀ 1
  have hK : 2*(C+M₁+1) ≤ κ*K := by
    have hh : (K₀:ℝ) ≤ K := by exact_mod_cast (le_max_left K₀ 1)
    have hh' := (div_le_iff₀ hκ).mp (hK₀.trans hh)
    nlinarith
  have hK1 : 1 ≤ K := le_max_right _ _
  have hsub : Icc (a-R) (b+R) ⊆ Icc (a-2*R) (b+2*R) := by
    intro x hx; constructor <;> linarith [hx.1,hx.2]
  apply summed_stationary_mass K hK1 (L := C₀ / Real.sqrt (d/(2*Real.pi)))
    (D := 4*(4*C₀+(b-a)*C₁)/κ) (by positivity) hi
    (passage_uniform_error hΦ hA hab hR hd hdD hC₀ hC₁ hM₀ hsecond hupper hM hAb hA'b hsupp κ α)
  · intro n j z
    exact stationaryLeading_bound (hΦ.of_le (by norm_num)) (by linarith) hd hC₀
      (fun x hx => hsecond x (hsub hx)) (fun x hx => hAb z x (hsub hx))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    intro j hj
    have hb := passage_arrays_tail hΦ hA hab hR hd hC₀ hC₁ hM₁ hC hκ hK hn (hα n)
      hfirst hsecond hAb hA'b hsupp hj
    calc
      _ ≤ ∫ _ : Ω, (4*(4*C₀+(b-a)*C₁)/κ)^2/(j:ℝ)^2 ∂μ :=
        integral_mono (hi n j) (integrable_const _) (by
          intro z
          dsimp only
          rw [(hb z).1, norm_zero, zero_pow (by omega), mul_zero, sub_zero,
            abs_of_nonneg (sq_nonneg _)]
          have hh := sq_le_sq₀ (norm_nonneg (passageCoefficient Φ A κ α n j z)) (by positivity : 0 ≤ (4*(4*C₀+(b-a)*C₁)/κ)/|(j:ℝ)|)
          have hh' := hh.mpr (hb z).2
          simpa only [div_pow, sq_abs] using hh')
      _ = _ := by simp

end ThreeTorus

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Twists
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product torus, exact angular packets, all integer twist iterates, and measure-preserving passage charts. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma packet_twistIter (φ : UnitAddCircle → UnitAddCircle) (n m : ℤ)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A (twistIter φ n x) = fourier n (m • φ x.2.1) * packet m A x := by
  change A x.2 * fourier m (x.1+n • φ x.2.1) =
    fourier n (m • φ x.2.1)*(A x.2*fourier m x.1)
  simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul,smul_smul]
  rw [mul_comm n m]
  ring

lemma continuous_packet {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) : Continuous (packet m A) :=
  (hA.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma integral_fourier_pair (m k : ℤ) :
    (∫ θ : UnitAddCircle, starRingEnd ℂ (fourier m θ)*fourier k θ
      ∂AddCircle.haarAddCircle) = if m = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1:ℝ)))) m k
  rw [ContinuousMap.inner_toLp] at hh
  simpa only [RCLike.inner_apply,mul_comm] using hh

/-- Exact packet orthogonality, before stationary phase or any passage limit. -/
lemma integral_packet_pair {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    ((Complex.continuous_conj.comp (continuous_packet hA)).mul
      (continuous_packet hB)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma normSq_complex (z : ℂ) : starRingEnd ℂ z*z = (‖z‖^2 : ℝ) := by
  simp only [Complex.conj_mul',Complex.ofReal_pow]

/-- Exact correlation formula for a packet under every positive or negative power. -/
lemma packet_correlation {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : Continuous B := ((fourier n).continuous.comp
    ((hφ.comp continuous_fst).const_smul m)).mul hA
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

lemma packet_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : Continuous A) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.measurable.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hA.norm.pow 2).measurable.ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Pi.pow_apply,Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

lemma continuous_fourier_parseval {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    ∑' j : ℤ, ‖fourierCoeff f j‖^2 =
      ∫ θ : UnitAddCircle, ‖f θ‖^2 ∂AddCircle.haarAddCircle := by
  let F : C(UnitAddCircle,ℂ) := ⟨f,hf⟩
  have hh := tsum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F)
  simp_rw [fourierCoeff_toLp] at hh
  erw [hh]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) AddCircle.haarAddCircle F] with θ hθ
  rw [hθ]
  rfl

/-- Exact Parseval identity for arbitrary finite smooth coefficient cutoffs. -/
lemma Fourier_cutoff_error {f : UnitAddCircle → ℂ} (hf : Continuous f)
    (S : Finset ℤ) (χ : ℤ → ℂ) :
    (∫ θ : UnitAddCircle,
      ‖f θ-∑ j ∈ S, χ j*fourierCoeff f j*fourier j θ‖^2 ∂AddCircle.haarAddCircle) =
    ∑' j : ℤ, ‖(1-(if j ∈ S then χ j else 0))*fourierCoeff f j‖^2 := by
  classical
  let g : UnitAddCircle → ℂ := fun θ =>
    f θ-∑ j ∈ S, χ j*fourierCoeff f j*fourier j θ
  have hg : Continuous g := hf.sub (continuous_finsetSum _
    (fun j _hj => continuous_const.mul (fourier j).continuous))
  rw [← continuous_fourier_parseval hg]
  congr 1
  funext j
  congr 1
  have hcoeff : fourierCoeff g j =
      fourierCoeff f j - (if j ∈ S then χ j else 0)*fourierCoeff f j := by
    change (∫ θ : UnitAddCircle, fourier (-j) θ*(f θ-
      ∑ k ∈ S, χ k*fourierCoeff f k*fourier k θ) ∂AddCircle.haarAddCircle) =
      (∫ θ : UnitAddCircle, fourier (-j) θ*f θ ∂AddCircle.haarAddCircle) -
        (if j ∈ S then χ j else 0)*fourierCoeff f j
    simp only [mul_sub,Finset.mul_sum]
    have hif : Integrable (fun θ : UnitAddCircle => fourier (-j) θ*f θ)
        AddCircle.haarAddCircle :=
      ((fourier (-j)).continuous.mul hf).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have his : Integrable (fun θ : UnitAddCircle => ∑ k ∈ S,
        fourier (-j) θ*(χ k*fourierCoeff f k*fourier k θ)) AddCircle.haarAddCircle :=
      (continuous_finsetSum _ (fun k _ => (fourier (-j)).continuous.mul
        (continuous_const.mul (fourier k).continuous))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hif his]
    rw [integral_finsetSum]
    · congr 1
      have he (k : ℤ) :
          (∫ θ : UnitAddCircle, fourier (-j) θ*(χ k*fourierCoeff f k*fourier k θ)
            ∂AddCircle.haarAddCircle) = (χ k*fourierCoeff f k)*(if j = k then 1 else 0) := by
        simp_rw [show ∀ θ : UnitAddCircle,
          fourier (-j) θ*(χ k*fourierCoeff f k*fourier k θ) =
          (χ k*fourierCoeff f k)*(starRingEnd ℂ (fourier j θ)*fourier k θ) by
            intro θ; rw [fourier_neg]; ring]
        rw [integral_const_mul,integral_fourier_pair]
      simp_rw [he]
      by_cases hj : j ∈ S
      · rw [ite_eq_left hj,Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [Ne.symm hk]
        · exact fun hh => (hh hj).elim
      · rw [ite_eq_right hj,zero_mul]
        apply Finset.sum_eq_zero
        intro k hk
        have hh : j ≠ k := by intro he; subst k; exact hj hk
        simp [hh]
    · intro k _
      exact ((fourier (-j)).continuous.mul (continuous_const.mul
        (fourier k).continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  rw [hcoeff]
  ring_nf

/-- The exact cutoff energy is bounded by coefficient-mass error; the model
mass need not be a Fourier coefficient of any function. -/
lemma cutoff_normSq_le_mass_error {c : ℂ} {χ w : ℝ}
    (hχ : 0 ≤ χ ∧ χ ≤ 1) (hw : w ≠ 0 → χ = 1) :
    ‖(1-(χ:ℂ))*c‖^2 ≤ |‖c‖^2-w| := by
  by_cases hc : χ = 1
  · simp only [hc,Complex.ofReal_one,sub_self,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact abs_nonneg _
  have hw0 : w = 0 := by_contra fun hh => hc (hw hh)
  have hnorm : ‖(1-(χ:ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith [hχ.1,hχ.2]
  rw [hw0,sub_zero,abs_of_nonneg (sq_nonneg _),norm_mul,mul_pow]
  have hs : ‖(1-(χ:ℂ))‖^2 ≤ 1 := by nlinarith [norm_nonneg (1-(χ:ℂ))]
  nlinarith [sq_nonneg ‖c‖]

lemma Fourier_cutoff_le_mass_error {f : UnitAddCircle → ℂ} (hf : Continuous f)
    (S : Finset ℤ) (χ W : ℤ → ℝ) (hχ : ∀ j, 0 ≤ χ j ∧ χ j ≤ 1)
    (hW : ∀ j, W j ≠ 0 → j ∈ S ∧ χ j = 1)
    (hE : Summable (fun j => |‖fourierCoeff f j‖^2-W j|)) :
    (∫ θ : UnitAddCircle,
      ‖f θ-∑ j ∈ S, (χ j:ℂ)*fourierCoeff f j*fourier j θ‖^2
        ∂AddCircle.haarAddCircle) ≤ ∑' j : ℤ, |‖fourierCoeff f j‖^2-W j| := by
  classical
  rw [Fourier_cutoff_error hf]
  have hb (j : ℤ) :
      ‖(1-(if j ∈ S then (χ j:ℂ) else 0))*fourierCoeff f j‖^2 ≤
        |‖fourierCoeff f j‖^2-W j| := by
    by_cases hj : j ∈ S
    · rw [ite_eq_left hj]
      exact cutoff_normSq_le_mass_error (hχ j) (fun hw => (hW j hw).2)
    · rw [ite_eq_right hj]
      have hw : W j = 0 := by_contra fun hh => hj (hW j hh).1
      simp only [sub_zero,one_mul,hw]
      exact le_abs_self _
  exact Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hE) hE

/-- Tonelli in real form for a summable nonnegative array. -/
lemma integrable_nonneg_tsum {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} {E : ι → Ω → ℝ} (hE : ∀ j, Integrable (E j) μ)
    (h0 : ∀ j a, 0 ≤ E j a) (hp : ∀ᵐ a ∂μ, Summable (fun j => E j a))
    (hs : Summable (fun j => ∫ a, E j a ∂μ)) :
    Integrable (fun a => ∑' j, E j a) μ := by
  refine ⟨(AEMeasurable.tsum (fun j => (hE j).aemeasurable)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun a => tsum_nonneg (fun j => h0 j a)))]
  calc
    (∫⁻ a, ENNReal.ofReal (∑' j, E j a) ∂μ) =
        ∫⁻ a, ∑' j, ENNReal.ofReal (E j a) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with a ha
      exact ENNReal.ofReal_tsum_of_nonneg (fun j => h0 j a) ha
    _ = ∑' j, ∫⁻ a, ENNReal.ofReal (E j a) ∂μ :=
      lintegral_tsum (fun j => (hE j).aemeasurable.ennreal_ofReal)
    _ = ∑' j, ENNReal.ofReal (∫ a, E j a ∂μ) := by
      congr 1; funext j
      exact (ofReal_integral_eq_lintegral_ofReal (hE j)
        (Filter.Eventually.of_forall (h0 j))).symm
    _ = ENNReal.ofReal (∑' j, ∫ a, E j a ∂μ) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (h0 j)) hs).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Integrating the genuine Fourier reconstruction error preserves the summed
stationary mass bound from (2.14), with no assertion of an L² leading phase. -/
lemma integrated_Fourier_cutoff_le_mass_error {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → UnitAddCircle → ℂ} (hf : ∀ a, Continuous (f a))
    (S : Finset ℤ) (χ W : ℤ → Ω → ℝ)
    (hχ : ∀ j a, 0 ≤ χ j a ∧ χ j a ≤ 1)
    (hW : ∀ j a, W j a ≠ 0 → j ∈ S ∧ χ j a = 1)
    (hE : ∀ j, Integrable (fun a => |‖fourierCoeff (f a) j‖^2-W j a|) μ)
    (hp : ∀ᵐ a ∂μ, Summable (fun j => |‖fourierCoeff (f a) j‖^2-W j a|))
    (hs : Summable (fun j => ∫ a, |‖fourierCoeff (f a) j‖^2-W j a| ∂μ)) :
    (∫ a, ∫ θ : UnitAddCircle,
      ‖f a θ-∑ j ∈ S, (χ j a:ℂ)*fourierCoeff (f a) j*fourier j θ‖^2
        ∂AddCircle.haarAddCircle ∂μ) ≤
      ∑' j : ℤ, ∫ a, |‖fourierCoeff (f a) j‖^2-W j a| ∂μ := by
  have hsum := integrable_nonneg_tsum hE (fun _ _ => abs_nonneg _) hp hs
  have hs' : Summable (fun j => ∫ a, ‖|‖fourierCoeff (f a) j‖^2-W j a|‖ ∂μ) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hs
  rw [integral_tsum_of_summable_integral_norm hE hs']
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) hsum
  filter_upwards [hp] with a ha
  exact Fourier_cutoff_le_mass_error (hf a) S (fun j => χ j a) (fun j => W j a)
    (fun j => hχ j a) (fun j => hW j a) ha

end ThreeTorus

namespace ThreeTorus

lemma measurePreserving_circleCycle :
    MeasurePreserving circleCycle tripleVolume tripleVolume := by
  exact (measurePreserving_prodAssoc AddCircle.haarAddCircle AddCircle.haarAddCircle
    AddCircle.haarAddCircle).comp Measure.measurePreserving_swap

lemma measurePreserving_fiberTranslate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {g : Ω → UnitAddCircle} (hg : Measurable g) :
    MeasurePreserving (fun p : Ω × UnitAddCircle => (p.1,p.2+g p.1))
      (μ.prod AddCircle.haarAddCircle) (μ.prod AddCircle.haarAddCircle) := by
  exact (MeasurePreserving.id μ).skew_product (measurable_snd.add (hg.comp measurable_fst))
    (Filter.Eventually.of_forall (fun x => (measurePreserving_add_right AddCircle.haarAddCircle (g x)).map_eq))

lemma measurePreserving_circleThetaShear {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (circleThetaShear H) tripleVolume tripleVolume := by
  exact Measure.measurePreserving_swap.comp
    ((measurePreserving_fiberTranslate (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle)
      (hH.comp measurable_fst)).comp Measure.measurePreserving_swap)

lemma measurePreserving_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    MeasurePreserving (passageChart H) tripleVolume tripleVolume :=
  measurePreserving_circleCycle.comp (measurePreserving_circleThetaShear hH.neg)

lemma passageChart_inverse_measurable {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H) :
    Measurable (passageChart H).symm := by
  change Measurable (fun x : TripleTorus => (x.2.2-(-H x.1),x.1,x.2.1))
  exact (measurable_snd.snd.sub (hH.comp measurable_fst).neg).prodMk
    (measurable_fst.prodMk measurable_snd.fst)

end ThreeTorus

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

lemma packet_in_passage_chart (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet m A ((passageChart H).symm x) =
      passageFourierInput m H A x.2.1 x.1*fourier m x.2.2 := by
  change A (x.1,x.2.1)*fourier m (x.2.2-(-H x.1)) =
    (A (x.1,x.2.1)*fourier m (H x.1))*fourier m x.2.2
  simp only [sub_neg_eq_add,fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul]
  ring

lemma retainedPassage_error_norm (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ) (x : TripleTorus) :
    ‖(ψ x.2.1:ℂ)*packet m A ((passageChart H).symm x)-
      retainedPassage m H A S χ ψ x‖^2 =
    ψ x.2.1^2*‖passageFourierInput m H A x.2.1 x.1-
      ∑ j ∈ S, (χ j x.2.1:ℂ)*exactPassageCoeff m H A j x.2.1*fourier j x.1‖^2 := by
  rw [packet_in_passage_chart]
  have he : (ψ x.2.1:ℂ)*
      (passageFourierInput m H A x.2.1 x.1*fourier m x.2.2)-
      retainedPassage m H A S χ ψ x =
      (ψ x.2.1:ℂ)*fourier m x.2.2*(passageFourierInput m H A x.2.1 x.1-
        ∑ j ∈ S, (χ j x.2.1:ℂ)*exactPassageCoeff m H A j x.2.1*fourier j x.1) := by
    unfold retainedPassage
    rw [mul_sub,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _; ring
  rw [he,norm_mul,norm_mul,show ‖fourier m x.2.2‖ = 1 from Circle.norm_coe _,mul_one,
    mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma integrated_retainedPassage_error {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A)
    (S : Finset ℤ) (χ : ℤ → UnitAddCircle → ℝ) (hχ : ∀ j, Continuous (χ j))
    (ψ : UnitAddCircle → ℝ) (hψ : Continuous ψ) :
    (∫ x : TripleTorus,
      ‖(ψ x.2.1:ℂ)*packet m A ((passageChart H).symm x)-
        retainedPassage m H A S χ ψ x‖^2 ∂tripleVolume) =
    ∫ a : UnitAddCircle, ψ a^2*(∫ θ : UnitAddCircle,
      ‖passageFourierInput m H A a θ-
        ∑ j ∈ S, (χ j a:ℂ)*exactPassageCoeff m H A j a*fourier j θ‖^2
          ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle := by
  let E : UnitAddCircle → UnitAddCircle → ℝ := fun a θ => ψ a^2*
    ‖passageFourierInput m H A a θ-
      ∑ j ∈ S, (χ j a:ℂ)*exactPassageCoeff m H A j a*fourier j θ‖^2
  have hE : Continuous E.uncurry := by
    apply ((hψ.comp continuous_fst).pow 2).mul
    apply Continuous.pow
    apply Continuous.norm
    apply (continuous_passageFourierInput hH hA).sub
    apply continuous_finsetSum
    intro j _hj
    exact (((Complex.continuous_ofReal.comp (hχ j)).comp continuous_fst).mul
      ((continuous_exactPassageCoeff hH hA j).comp continuous_fst)).mul
      ((fourier j).continuous.comp continuous_snd)
  simp_rw [retainedPassage_error_norm]
  change (∫ x : TripleTorus, E x.2.1 x.1 ∂tripleVolume) = _
  have hit : Integrable (fun x : TripleTorus => E x.2.1 x.1) tripleVolume :=
    (hE.comp (continuous_snd.fst.prodMk continuous_fst)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_prod _ hit]
  have hinner (θ : UnitAddCircle) :
      (∫ p : UnitAddCircle × UnitAddCircle, E p.1 θ ∂slowVolume) =
        ∫ a : UnitAddCircle, E a θ ∂AddCircle.haarAddCircle := by
    rw [integral_prod]
    · simp
    · exact (hE.comp (continuous_fst.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp_rw [hinner]
  rw [integral_integral_swap]
  · congr 1; funext a
    exact integral_const_mul _ _
  · exact (hE.comp continuous_swap).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end ThreeTorus

namespace ThreeTorus

/-- The exact torus coefficient as a compactly supported real oscillatory integral.
The support hypothesis is the lifted good-arc support, not a Fourier approximation. -/
lemma exactPassageCoeff_real_integral {m j : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {a : UnitAddCircle} {o : ℝ}
    {H₀ : ℝ → ℝ} {A₀ : ℝ → ℂ}
    (hH : ∀ x : ℝ, H (x : UnitAddCircle) = (H₀ x : UnitAddCircle))
    (hA : ∀ x ∈ Ioc o (o+1), A ((x : UnitAddCircle),a) = A₀ x)
    (hAs : Function.support A₀ ⊆ Ioc o (o+1)) :
    exactPassageCoeff m H A j a =
      ∫ x : ℝ, A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
  unfold exactPassageCoeff
  rw [fourierCoeff_eq_intervalIntegral _ _ o]
  simp only [one_div,inv_one,one_smul]
  have he (x : ℝ) (hx : x ∈ Ioc o (o+1)) :
      fourier (-j) (x : UnitAddCircle) • passageFourierInput m H A a (x : UnitAddCircle) =
        A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
    simp only [passageFourierInput,hA x hx,hH x,smul_eq_mul,fourier_coe_apply]
    simp only [Complex.ofReal_one,div_one,Int.cast_neg]
    rw [show Complex.exp (2*Real.pi*Complex.I*(-(j:ℂ))*(x:ℂ))*
        (A₀ x*Complex.exp (2*Real.pi*Complex.I*(m:ℂ)*(H₀ x:ℂ))) =
        A₀ x*(Complex.exp (2*Real.pi*Complex.I*(-(j:ℂ))*(x:ℂ))*
          Complex.exp (2*Real.pi*Complex.I*(m:ℂ)*(H₀ x:ℂ))) by ring,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc
    _ = ∫ x in o..o+1, A₀ x*Complex.exp (Complex.I*((2*Real.pi*((m:ℝ)*H₀ x-j*x)):ℝ)) := by
      rw [intervalIntegral.integral_of_le (by linarith : o ≤ o+1),
        intervalIntegral.integral_of_le (by linarith : o ≤ o+1)]
      exact setIntegral_congr_fun measurableSet_Ioc he
    _ = _ := intervalIntegral.integral_eq_integral_of_support_subset (by
      intro x hx
      exact hAs (mul_ne_zero_iff.mp hx).1)

/-- No approximation occurs when the rounded primitive is inserted in the phase.
This is the normalization needed by the compact-support stationary-phase proof. -/
lemma rounded_phase_normalization (m j : ℤ) {n : ℕ} (hn : n ≠ 0)
    (P : ℝ → ℝ) (δ : ℕ → ℝ) (x : ℝ) :
    2*Real.pi*((m:ℝ)*((n:ℝ)*(P x+δ n*x))-(j:ℝ)*x) =
      (n:ℝ)*((2*Real.pi*(m:ℝ)*P x)-
        ((2*Real.pi)*(j:ℝ)/(n:ℝ)-(2*Real.pi*(m:ℝ)*δ n))*x) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  ring

end ThreeTorus

namespace ThreeTorus

lemma continuous_compact_phase_integral {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {A : Ω → ℝ → ℂ} {Φ : ℝ → ℝ} {l u : ℝ}
    (hA : Continuous A.uncurry) (hΦ : Continuous Φ) (hlu : l ≤ u)
    (hs : ∀ a, Function.support (A a) ⊆ Ioc l u) (t : ℝ) :
    Continuous (fun a => ∫ x, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ))) := by
  have hf : Continuous (fun p : Ω × ℝ => A p.1 p.2*Complex.exp (Complex.I*((t*Φ p.2):ℝ))) := by
    fun_prop
  have hh := continuous_parametric_integral_of_continuous
    (μ := (volume : Measure ℝ)) (f := fun a x => A a x*Complex.exp (Complex.I*((t*Φ x):ℝ)))
    hf (isCompact_Icc (a := l) (b := u))
  have he (a : Ω) : (∫ x in Icc l u, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ))) =
      ∫ x, A a x*Complex.exp (Complex.I*((t*Φ x):ℝ)) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hlu]
    exact intervalIntegral_phase_of_support (hs a) Φ t
  simpa only [he] using hh

lemma continuous_passageCoefficient {A : UnitAddCircle → ℝ → ℂ} {Φ : ℝ → ℝ}
    {l u : ℝ} (hA : Continuous A.uncurry) (hΦ : Continuous Φ) (hlu : l ≤ u)
    (hs : ∀ a, Function.support (A a) ⊆ Ioc l u)
    (κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    Continuous (passageCoefficient Φ A κ α n j) :=
  continuous_compact_phase_integral hA (hΦ.sub (continuous_const.mul continuous_id)) hlu hs n

lemma continuous_passageLeading {A : UnitAddCircle → ℝ → ℂ} {Φ : ℝ → ℝ}
    (hA : Continuous A.uncurry) (l u R κ : ℝ) (α : ℕ → ℝ) (n : ℕ) (j : ℤ) :
    Continuous (passageLeading Φ A l u R κ α n j) := by
  unfold passageLeading stationaryLeading
  split_ifs
  · fun_prop
  · exact continuous_const

/-- Strong summed stationary mass for the actual torus passage coefficients.
All integrability in the slow parameter is derived from compact smooth data. -/
lemma exactPassageCoeff_summed_mass
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*‖passageLeading (fun x => 2*Real.pi*(m:ℝ)*P x) A₀ l u R (2*Real.pi)
          (fun n => 2*Real.pi*(m:ℝ)*δ n) n j a‖^2| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  let Φ : ℝ → ℝ := fun x => 2*Real.pi*(m:ℝ)*P x
  let α : ℕ → ℝ := fun n => 2*Real.pi*(m:ℝ)*δ n
  have hi (n : ℕ) (j : ℤ) : Integrable (fun a =>
      |‖passageCoefficient Φ A₀ (2*Real.pi) α n j a‖^2-
        (n:ℝ)⁻¹*‖passageLeading Φ A₀ l u R (2*Real.pi) α n j a‖^2|)
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (((continuous_passageCoefficient hAc hΦ.continuous hlu hsupp _ _ n j).norm.pow 2).sub
      ((continuous_const.mul ((continuous_passageLeading hAc l u R _ α n j).norm.pow 2)))).abs
  have ht := passage_summed_mass (μ := AddCircle.haarAddCircle) hΦ hA₀ hlu hR hd hdD
    hC₀ hC₁ hM₀ hM₁ hC (by positivity : 0 < 2*Real.pi) hδ
    hfirst hsecond hupper hM hAb hA'b hsupp hi
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  congr 1; funext j
  apply integral_congr_ae
  filter_upwards [] with a
  have hs : Function.support (A₀ a) ⊆ Ioc o (o+1) :=
    (hsupp a).trans (Ioc_subset_Ioc hlo huo)
  have he := exactPassageCoeff_real_integral (m := m) (j := j) (H := H n) (A := A)
    (a := a) (hH n) (hA a) hs
  rw [he]
  congr 3
  unfold passageCoefficient passageSlope
  apply congrArg norm
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rounded_phase_normalization m j (by omega : n ≠ 0) P δ x]

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma stationaryLeading_norm_sq_weight {Φ J : ℝ → ℝ} {A : ℝ → ℂ} {l u : ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (hJ : Continuous J) (hlu : l ≤ u)
    (hfirst : ∀ x, deriv Φ x = 2*Real.pi*J x)
    (hsecond : ∀ x, iteratedDeriv 2 Φ x = 2*Real.pi*deriv J x)
    (hpos : ∀ x ∈ Icc l u, 0 < deriv J x) (s t : ℝ) :
    ‖stationaryLeading Φ A l u (2*Real.pi*s) t‖^2 = stationaryWeight (Icc l u) J A s := by
  have hk : 0 < 2*Real.pi := by positivity
  have hmono : StrictMonoOn J (Icc l u) := strictMonoOn_of_deriv_pos (convex_Icc _ _)
    hJ.continuousOn (fun x hx => hpos x (interior_subset hx))
  have himage : J '' Icc l u = Icc (J l) (J u) :=
    hJ.continuousOn.image_Icc_of_monotoneOn hlu hmono.monotoneOn
  have hsiff : 2*Real.pi*s ∈ Icc (deriv Φ l) (deriv Φ u) ↔ s ∈ J '' Icc l u := by
    rw [hfirst l,hfirst u,himage]
    simp only [mem_Icc,mul_le_mul_iff_right₀ hk]
  by_cases hs : s ∈ J '' Icc l u
  · have hsΦ := hsiff.mpr hs
    let v := invFunOn J (Icc l u) s
    have hv : v ∈ Icc l u := (invFunOn_pos hs).1
    have hvJ : J v = s := (invFunOn_pos hs).2
    have hw := stationary_branch_center hΦ hlu hsΦ
    have hinv : invFunOn (deriv Φ) (Icc l u) (2*Real.pi*s) = v := by
      apply hmono.injOn hw.1 hv
      rw [hfirst] at hw
      exact (mul_left_cancel₀ hk.ne' hw.2).trans hvJ.symm
    have hp := hpos v hv
    have hb : iteratedDeriv 2 Φ v/(2*Real.pi) = deriv J v := by
      rw [hsecond]
      field_simp
    rw [norm_stationaryLeading hsΦ,hinv,hb,mul_pow,inv_pow,Real.sq_sqrt hp.le]
    simp only [stationaryWeight,branchDensity,indicator_of_mem hs,abs_of_pos hp,v]
    ring
  · have hsΦ := mt hsiff.mp hs
    simp only [stationaryLeading,ite_eq_right hsΦ,norm_zero,zero_pow (by norm_num : 2 ≠ 0),
      stationaryWeight,branchDensity,indicator_of_notMem hs]

/-- Normalization of the phase derivative agrees exactly with the old speed.
This computes the manuscript's W under the ordinary derivative identity P'=V. -/
lemma phase_speed_derivatives {P V : ℝ → ℝ} {m : ℝ}
    (hP : Differentiable ℝ P) (hV : Differentiable ℝ V) (hPV : deriv P = V) :
    (∀ x, deriv (fun x => 2*Real.pi*m*P x) x = 2*Real.pi*(m*V x)) ∧
    (∀ x, iteratedDeriv 2 (fun x => 2*Real.pi*m*P x) x =
      2*Real.pi*deriv (fun x => m*V x) x) := by
  have hd : deriv (fun x => 2*Real.pi*m*P x) = fun x => 2*Real.pi*m*V x := by
    funext x
    rw [deriv_const_mul (2*Real.pi*m) (hP x),hPV]
  refine ⟨fun x => by rw [hd]; ring,?_⟩
  intro x
  simp only [iteratedDeriv_succ,iteratedDeriv_zero,hd]
  rw [deriv_const_mul (2*Real.pi*m) (hV x),deriv_const_mul m (hV x)]
  ring

/-- Summed stationary mass in the manuscript's actual normalization W, without
an auxiliary complex leading array remaining in the conclusion. -/
lemma exactPassageCoeff_summed_weight
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) 
    (hP : Differentiable ℝ P) (hV : Differentiable ℝ V) (hPV : deriv P = V) :

    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n-(m:ℝ)*δ n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  have he := phase_speed_derivatives (m := (m:ℝ)) hP hV hPV
  have hi : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hpos (x : ℝ) (hx : x ∈ Icc (l-R) (u+R)) :
      0 < deriv (fun x => (m:ℝ)*V x) x := by
    have hh := hsecond x (hi hx)
    rw [he.2 x] at hh
    have hk : 0 < 2*Real.pi := by positivity
    nlinarith
  have hweight (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
      ‖passageLeading (fun x => 2*Real.pi*(m:ℝ)*P x) A₀ l u R (2*Real.pi)
        (fun n => 2*Real.pi*(m:ℝ)*δ n) n j a‖^2 =
      stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a)
        ((j:ℝ)/n-(m:ℝ)*δ n) := by
    unfold passageLeading passageSlope
    have hs : 2*Real.pi*(j:ℝ)/(n:ℝ)-2*Real.pi*(m:ℝ)*δ n =
        2*Real.pi*((j:ℝ)/n-(m:ℝ)*δ n) := by ring
    rw [hs]
    exact stationaryLeading_norm_sq_weight (hΦ.of_le (by norm_num))
      (continuous_const.mul hV.continuous) (by linarith) he.1 he.2 hpos _ _
  have hh := exactPassageCoeff_summed_mass hH hA hA₀ hAc hsupp hlo huo hlu
    hΦ hR hd hdD hC₀ hC₁ hM₀ hM₁ hC hδ hfirst hsecond hupper hM hAb hA'b
  simp_rw [hweight] at hh
  exact hh

lemma continuous_fourier_summable {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Summable (fun j : ℤ => ‖fourierCoeff f j‖^2) := by
  let F : C(UnitAddCircle,ℂ) := ⟨f,hf⟩
  have hh := (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F)).summable
  simpa only [fourierCoeff_toLp, F, ContinuousMap.coe_mk] using hh

/-- The integrated Fourier masses really are summable, so no use of a default
zero value of a divergent tsum is possible in the passage estimates. -/
lemma continuous_family_fourier_summable {f : UnitAddCircle → UnitAddCircle → ℂ}
    (hf : Continuous f.uncurry) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖fourierCoeff (f a) j‖^2
      ∂AddCircle.haarAddCircle) := by
  have hfi (a : UnitAddCircle) : Continuous (f a) := hf.comp (continuous_const.prodMk continuous_id)
  have hj (j : ℤ) : Integrable (fun a => ‖fourierCoeff (f a) j‖^2) AddCircle.haarAddCircle :=
    ((continuous_fourierCoeff_param hf j).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hec : Continuous (fun a : UnitAddCircle => ∫ θ : UnitAddCircle, ‖f a θ‖^2
      ∂AddCircle.haarAddCircle) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
        (f := fun a θ => ‖f a θ‖^2) (by exact hf.norm.pow 2) isCompact_univ)
  have hei := hec.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  apply summable_of_sum_le (c := ∫ a : UnitAddCircle,
    (∫ θ : UnitAddCircle, ‖f a θ‖^2 ∂AddCircle.haarAddCircle) ∂AddCircle.haarAddCircle)
  · intro j
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro S
    rw [← integral_finsetSum _ (fun j _ => hj j)]
    apply integral_mono (integrable_finsetSum S (fun j _ => hj j)) hei
    intro a
    dsimp only
    rw [← continuous_fourier_parseval (hfi a)]
    exact (continuous_fourier_summable (hfi a)).sum_le_tsum S (fun _ _ => sq_nonneg _)

lemma exactPassageCoeff_summable {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖exactPassageCoeff m H A j a‖^2
      ∂AddCircle.haarAddCircle) := by
  exact continuous_family_fourier_summable (continuous_passageFourierInput hH hA)

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma support_branchFamily_subset {Ω : Type*} [TopologicalSpace Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ} :
    support (branchFamily I J F) ⊆ (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchFamily,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchFamily,hs,hz])
  · simp only [hp.2]

lemma branchFamily_compact {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchFamily I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × Ω => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchFamily_subset hn)

lemma branchFamily_continuous {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω]
    {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × Ω → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : tsupport F ⊆ I ×ˢ univ) :
    Continuous (branchFamily I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × Ω => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × Ω} (hp : p ∉ M) : branchFamily I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchFamily_subset hn))
  have hD : Continuous (deriv J) := hJ.continuous_deriv (by simp)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)).continuousAt
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hgi' : ContinuousAt (fun p : ℝ × Ω => g p.1) (J x,a) :=
      hgi.comp_of_eq continuousAt_fst rfl
    have hin : ContinuousAt (fun p : ℝ × Ω => (g p.1,p.2)) (J x,a) :=
      hgi'.prodMk continuousAt_snd
    have hDen : ContinuousAt (fun p : ℝ × Ω => |deriv J (g p.1)|) (J x,a) :=
      (hD.continuousAt.comp hgi').abs
    have hquot : ContinuousAt (fun p : ℝ × Ω => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.continuousAt.comp hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × Ω in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchFamily,ite_eq_left hp,g]
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

lemma stationaryWeight_family_eq (C : Set ℝ) (J : ℝ → ℝ)
    (A : UnitAddCircle → ℝ → ℂ) :
    (fun p : ℝ × UnitAddCircle => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × UnitAddCircle => ‖A p.2 p.1‖^2) := by
  classical
  funext p
  by_cases hp : p.1 ∈ J '' C <;> simp [stationaryWeight,branchDensity,branchFamily,hp]

/-- Joint compact continuity of the exact density used in stationary phase.
The enlarged stationary branch creates no boundary discontinuity because the
original packet is supported in the strictly smaller closed interval. -/
lemma stationaryWeight_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hd : ∀ x ∈ Icc (l-R) (u+R), 0 < deriv J x) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    by_contra hn
    have hz : A p.2 p.1 = 0 := notMem_support.mp hn
    exact hp (by simp [F,hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  let C := Icc (l-R) (u+R)
  let I := Ioo (l-R) (u+R)
  have hIC : I ⊆ C := Ioo_subset_Icc_self
  have hinj : InjOn J C := (strictMonoOn_of_deriv_pos (convex_Icc _ _)
    hJ.continuous.continuousOn (fun x hx => hd x (interior_subset hx))).injOn
  have hsub : Icc l u ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hFtI : tsupport F ⊆ I ×ˢ (univ : Set UnitAddCircle) :=
    fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩
  have he := branchFamily_congr_branch hIC hinj (subset_trans subset_closure hFtI)
  rw [stationaryWeight_family_eq]
  change Continuous (branchFamily C J F) ∧ HasCompactSupport (branchFamily C J F)
  refine ⟨?_,branchFamily_compact hJ.continuous hc⟩
  rw [he]
  exact branchFamily_continuous hJ isOpen_Ioo (hinj.mono hIC)
    (fun x hx => (hd x (hIC hx)).ne') hF hc hFtI

open scoped NNReal

lemma roundingMass_uniform_bound {W : ℝ → UnitAddCircle → ℝ} {A C e η : ℝ} {K n : ℕ}
    (hW : Continuous W.uncurry) (hη : 0 ≤ η)
    (hclose : ∀ s a, |W (s-e) a-W s a| ≤ η)
    (hs : ∀ s a, A < |s| → W s a = 0)
    (he : |e| ≤ C) (hK : A+C ≤ K) (hn : 0 < n) :
    roundingMass W n e ≤ (2*(K:ℝ)+1)*η := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hC : 0 ≤ C := (abs_nonneg e).trans he
  let S : Finset ℤ := Finset.Icc (-(K*n:ℤ)) (K*n)
  have hz (j : ℤ) (hj : j ∉ S) (a : UnitAddCircle) :
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| = 0 := by
    have hj' : (K:ℝ)*n < |(j:ℝ)| := by
      have hh : (K*n:ℤ) < |j| := by
        simpa only [S,Finset.mem_Icc,← abs_le,not_le] using hj
      exact_mod_cast hh
    have hjn : (K:ℝ) < |(j:ℝ)/n| := by
      rw [abs_div,abs_of_pos hn']
      exact (lt_div_iff₀ hn').mpr hj'
    have hje : A < |(j:ℝ)/n-e| := by
      have hb := abs_add_le ((j:ℝ)/n-e) e
      rw [sub_add_cancel] at hb
      linarith
    have hja : A < |(j:ℝ)/n| := by linarith
    rw [hs _ _ hje,hs _ _ hja,sub_self,abs_zero]
  have heq : (∑' j : ℤ, ∫ a : UnitAddCircle,
      |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
      ∑ j ∈ S, ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle := by
    apply tsum_eq_sum
    intro j hj
    simp only [hz j hj,integral_zero]
  have hb (j : ℤ) : (∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|
      ∂AddCircle.haarAddCircle) ≤ η := by
    have hc : Continuous (fun a : UnitAddCircle => |W ((j:ℝ)/n-e) a-W ((j:ℝ)/n) a|) := by
      fun_prop
    calc
      _ ≤ ∫ _ : UnitAddCircle, η ∂AddCircle.haarAddCircle :=
        integral_mono (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (integrable_const _) (fun a => hclose _ a)
      _ = _ := by simp
  have hcard : (S.card:ℝ) = 2*(K:ℝ)*n+1 := by
    have hc : S.card = 2*(K*n)+1 := by
      dsimp only [S]
      rw [Int.card_Icc]
      have hz : (K:ℤ)*n + 1 - -((K:ℤ)*n) = ((2*(K*n)+1:ℕ):ℤ) := by
        push_cast
        ring
      rw [hz, Int.toNat_natCast]
    rw [hc]
    push_cast
    ring
  unfold roundingMass
  rw [heq]
  calc
    _ ≤ (n:ℝ)⁻¹ * (S.card*(η)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn'.le)
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun j _ => hb j)
    _ = (2*(K:ℝ)+(n:ℝ)⁻¹)*η := by rw [hcard]; field_simp
    _ ≤ _ := by
      have hi : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
      exact mul_le_mul_of_nonneg_right (by linarith) hη

/-- Compact continuity is sufficient for removal of rounding; no quantitative
Lipschitz hypothesis has to be added to the old spectral density. -/
lemma tendsto_roundingMass_of_compact {W : ℝ → UnitAddCircle → ℝ} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hc : HasCompactSupport W.uncurry)
    (ht : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => roundingMass W n (e n)) atTop (𝓝 0) := by
  have hUC := hc.uniformContinuous_of_continuous hW
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  let A := max R 0
  have hs (s a) (hs : A < |s|) : W s a = 0 := by
    by_contra hn
    have hh := hR ⟨(s,a),subset_tsupport _ hn,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
    exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hs
  obtain ⟨K,hK⟩ := exists_nat_ge (A+1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := 2*(K:ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := ε/(2*C)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hUC η hη
  have he : ∀ᶠ n in atTop, |e n| < min δ 1 := by
    simpa only [Real.dist_eq,sub_zero] using Metric.tendsto_nhds.mp ht (min δ 1) (lt_min hδ zero_lt_one)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hb := roundingMass_uniform_bound (K := K) hW hη.le
    (fun s a => le_of_lt (hclose (a := (s-e n,a)) (b := (s,a)) (by
      simpa only [Prod.dist_eq,dist_self,Real.dist_eq,sub_sub_cancel_left,abs_neg,max_eq_left (abs_nonneg (e n))] using
        (lt_of_lt_of_le hn (min_le_left _ _))))) hs
    (show |e n| ≤ 1 from le_of_lt (lt_of_lt_of_le hn (min_le_right _ _))) hK hn0
  have hnonneg : 0 ≤ roundingMass W n (e n) := by
    unfold roundingMass
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (tsum_nonneg (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hnonneg]
  have heq : (2*(K:ℝ)+1)*η = ε/2 := by dsimp [η,C]; field_simp
  exact (hb.trans_eq heq).trans_lt (by linarith)

lemma compact_lattice_support {W : ℝ → UnitAddCircle → ℝ} (hc : HasCompactSupport W.uncurry)
    {n : ℕ} (hn : 0 < n) (e : ℝ) :
    ∃ S : Finset ℤ, ∀ j ∉ S, ∀ a, W ((j:ℝ)/n-e) a = 0 := by
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨K,hK⟩ := exists_nat_ge (R+|e|)
  refine ⟨Finset.Icc (-(K*n:ℤ)) (K*n),?_⟩
  intro j hj a
  by_contra hz
  have hh := hR ⟨((j:ℝ)/n-e,a),subset_tsupport _ hz,rfl⟩
  rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hh
  have hjn : (K:ℝ) < |(j:ℝ)/n| := by
    have hk : (K*n:ℤ) < |j| := by
      simpa only [Finset.mem_Icc,← abs_le,not_le] using hj
    have hk' : (K:ℝ)*n < |(j:ℝ)| := by exact_mod_cast hk
    rw [abs_div,abs_of_pos (show (0:ℝ) < n by exact_mod_cast hn)]
    exact (lt_div_iff₀ (by exact_mod_cast hn)).mpr hk'
  have ht := abs_add_le ((j:ℝ)/n-e) e
  rw [sub_add_cancel] at ht
  linarith

lemma compact_lattice_summable_integral {W : ℝ → UnitAddCircle → ℝ}
    (hc : HasCompactSupport W.uncurry) {n : ℕ} (hn : 0 < n) (e : ℝ) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a|
      ∂AddCircle.haarAddCircle) := by
  obtain ⟨S,hS⟩ := compact_lattice_support hc hn e
  apply summable_of_ne_finset_zero (s := S)
  intro j hj
  simp only [hS j hj,abs_zero,integral_zero]

lemma integrated_array_mass_error_summable {c : ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} (hW : Continuous W.uncurry)
    (hc : HasCompactSupport W.uncurry) (hcc : ∀ j, Continuous (c j))
    (hcs : Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖c j a‖^2 ∂AddCircle.haarAddCircle))
    {n : ℕ} (hn : 0 < n) (e : ℝ) :
    Summable (fun j : ℤ => ∫ a : UnitAddCircle,
      |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a| ∂AddCircle.haarAddCircle) := by
  have hp (j : ℤ) : Continuous (fun a => W ((j:ℝ)/n-e) a) :=
    hW.comp (continuous_const.prodMk continuous_id)
  have he (j : ℤ) : Integrable (fun a => |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a|)
      AddCircle.haarAddCircle :=
    (((hcc j).norm.pow 2).sub (continuous_const.mul (hp j))).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi (j : ℤ) : Integrable (fun a => ‖c j a‖^2+(n:ℝ)⁻¹*|W ((j:ℝ)/n-e) a|)
      AddCircle.haarAddCircle :=
    (((hcc j).norm.pow 2).add (continuous_const.mul (hp j).abs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun a => abs_nonneg _))
    (f := fun j => (∫ a : UnitAddCircle, ‖c j a‖^2 ∂AddCircle.haarAddCircle)+
      (n:ℝ)⁻¹*(∫ a : UnitAddCircle, |W ((j:ℝ)/n-e) a| ∂AddCircle.haarAddCircle))
  · intro j
    rw [← integral_const_mul,← integral_add]
    · exact integral_mono (he j) (hi j) (fun a => by
        calc
          _ ≤ |‖c j a‖^2|+|(n:ℝ)⁻¹*W ((j:ℝ)/n-e) a| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))])
    · exact ((hcc j).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (continuous_const.mul (hp j).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hcs.add ((compact_lattice_summable_integral hc hn e).mul_left _)

/-- Removal of rounding for actual coefficient masses, with all summability
proved from compact support and true squared Fourier mass. -/
lemma remove_array_rounding {c : ℕ → ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} {e : ℕ → ℝ}
    (hW : Continuous W.uncurry) (hc : HasCompactSupport W.uncurry)
    (hcc : ∀ n j, Continuous (c n j))
    (hcs : ∀ n, Summable (fun j : ℤ => ∫ a : UnitAddCircle, ‖c n j a‖^2 ∂AddCircle.haarAddCircle))
    (he : Tendsto e atTop (𝓝 0))
    (ht : Tendsto (fun n => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) atTop (𝓝 0) := by
  have hr := tendsto_roundingMass_of_compact hW hc he
  have hbound : ∀ᶠ n in atTop,
      (∑' j : ℤ, ∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) ≤
      (∑' j : ℤ, ∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle)+
        roundingMass W n (e n) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hinv : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hs₀ := integrated_array_mass_error_summable hW hc (hcc n) (hcs n) hn 0
    simp only [sub_zero] at hs₀
    have hs₁ := integrated_array_mass_error_summable hW hc (hcc n) (hcs n) hn (e n)
    have hs₂ : Summable (fun j : ℤ => ∫ a : UnitAddCircle,
        |W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
      obtain ⟨S,hS⟩ := compact_lattice_support hc hn (e n)
      obtain ⟨T,hT⟩ := compact_lattice_support hc hn 0
      apply summable_of_ne_finset_zero (s := S ∪ T)
      intro j hj
      have hjS : j ∉ S := fun h => hj (Finset.mem_union_left T h)
      have hjT : j ∉ T := fun h => hj (Finset.mem_union_right S h)
      have hz (a) : W ((j:ℝ)/n) a = 0 := by simpa only [sub_zero] using hT j hjT a
      simp only [hS j hjS,hz,sub_self,abs_zero,integral_zero]
    have hi (j : ℤ) :
        (∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) ≤
        (∫ a : UnitAddCircle, |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a| ∂AddCircle.haarAddCircle)+
          (n:ℝ)⁻¹*(∫ a : UnitAddCircle, |W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
      have h₀ : Continuous (fun a => W ((j:ℝ)/n) a) := hW.comp (continuous_const.prodMk continuous_id)
      have h₁ : Continuous (fun a => W ((j:ℝ)/n-e n) a) := hW.comp (continuous_const.prodMk continuous_id)
      have hcj := ((hcc n j).norm.pow 2)
      rw [← integral_const_mul,← integral_add]
      · apply integral_mono
        · exact (hcj.sub (continuous_const.mul h₀)).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · exact ((hcj.sub (continuous_const.mul h₁)).abs.add
            (continuous_const.mul (h₁.sub h₀).abs)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · intro a
          calc
            _ ≤ |‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a|+
                |(n:ℝ)⁻¹*(W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a)| := by
              convert abs_add_le (‖c n j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n-e n) a)
                ((n:ℝ)⁻¹*(W ((j:ℝ)/n-e n) a-W ((j:ℝ)/n) a)) using 1
              all_goals try with_reducible_and_instances rfl
              ring_nf
            _ = _ := by rw [abs_mul,abs_of_nonneg hinv]
      · exact (hcj.sub (continuous_const.mul h₁)).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul (h₁.sub h₀).abs).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hh := Summable.tsum_le_tsum hi hs₀ (hs₁.add (hs₂.mul_left _))
    rw [hs₁.tsum_add (hs₂.mul_left _),tsum_mul_left] at hh
    exact hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => tsum_nonneg (fun j => integral_nonneg (fun a => abs_nonneg _)))) hbound
  simpa only [add_zero] using ht.add hr

lemma exactPassageCoeff_summed_unrounded
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R d D C₀ C₁ M M₁ C : ℝ}
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u)
    (hΦ : ContDiff ℝ 3 (fun x => 2*Real.pi*(m:ℝ)*P x))
    (hR : 0 < R) (hd : 0 < d) (hdD : d ≤ D)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hM₀ : 0 ≤ M) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C)
    (hδ : ∀ n, |2*Real.pi*(m:ℝ)*δ n| ≤ C)
    (hfirst : ∀ x ∈ Icc (l-2*R) (u+2*R), |deriv (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M₁)
    (hsecond : ∀ x ∈ Icc (l-2*R) (u+2*R), d ≤ iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x)
    (hupper : ∀ x ∈ Icc (l-2*R) (u+2*R), iteratedDeriv 2 (fun x => 2*Real.pi*(m:ℝ)*P x) x ≤ D)
    (hM : ∀ x ∈ Icc (l-2*R) (u+2*R), |iteratedDeriv 3 (fun x => 2*Real.pi*(m:ℝ)*P x) x| ≤ M)
    (hAb : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖A₀ a x‖ ≤ C₀)
    (hA'b : ∀ a x, x ∈ Icc (l-2*R) (u+2*R) → ‖deriv (A₀ a) x‖ ≤ C₁) 
    (hP : Differentiable ℝ P) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :

    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  have hVr := hV.differentiable (by simp)
  have ht := exactPassageCoeff_summed_weight hH hA hA₀ hAc hsupp hlo huo hlu
    hΦ hR hd hdD hC₀ hC₁ hM₀ hM₁ hC hδ hfirst hsecond hupper hM hAb hA'b hP hVr hPV
  let W : ℝ → UnitAddCircle → ℝ := fun s a =>
    stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s
  have he := phase_speed_derivatives (m := (m:ℝ)) hP hVr hPV
  have hi : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    apply Icc_subset_Icc <;> linarith
  have hp (x : ℝ) (hx : x ∈ Icc (l-R) (u+R)) :
      0 < deriv (fun x => (m:ℝ)*V x) x := by
    have hh := hsecond x (hi hx)
    rw [he.2 x] at hh
    have hk : 0 < 2*Real.pi := by positivity
    nlinarith
  have hW := stationaryWeight_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hp
  simpa only [W] using remove_array_rounding (c := fun n j => exactPassageCoeff m (H n) A j)
    (W := W) hW.1 hW.2 (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
    (fun n => exactPassageCoeff_summable (hHc n) hAcont)
    (show Tendsto (fun n => (m:ℝ)*δ n) atTop (𝓝 0) from by simpa using hδt.const_mul (m:ℝ)) ht

end ThreeTorus

namespace ThreeTorus

/-- A compact positive second derivative supplies every numerical constant used
by the uniform stationary-phase estimate.  None of those constants are extra
hypotheses of the passage. -/
lemma exactPassageCoeff_summed_positive
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : 0 < m)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  let Φ : ℝ → ℝ := fun x => 2*Real.pi*(m:ℝ)*P x
  let K : Set ℝ := Icc (l-2*R) (u+2*R)
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := nonempty_Icc.mpr (by linarith)
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := contDiff_const.mul hP
  have he := phase_speed_derivatives (m := (m:ℝ)) (hP.differentiable (by simp))
    (hV.differentiable (by simp)) hPV
  have hpos (x : ℝ) (hx : x ∈ K) : 0 < iteratedDeriv 2 Φ x := by
    rw [he.2 x,deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_pos (by positivity) (mul_pos (by exact_mod_cast hm) (hd x hx))
  obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hKne
    (hΦ.continuous_iteratedDeriv 2 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  let d := iteratedDeriv 2 Φ x₀
  have hd0 : 0 < d := hpos x₀ hx₀
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_iteratedDeriv 2 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  obtain ⟨M₁,hM₁⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_deriv (by simp)).continuousOn
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn
    (hΦ.continuous_iteratedDeriv 3 (by exact WithTop.coe_le_coe.mpr le_top)).continuousOn
  obtain ⟨C₀,hC₀⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hAc.continuousOn
  obtain ⟨C₁,hC₁⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn hAd.continuousOn
  have hδb : BddAbove (range (fun n => |2*Real.pi*(m:ℝ)*δ n|)) :=
    ((hδt.const_mul (2*Real.pi*(m:ℝ))).abs).bddAbove_range
  obtain ⟨C,hC⟩ := hδb
  apply exactPassageCoeff_summed_unrounded hH hA hA₀ hAc hsupp hlo huo hlu
    (hΦ.of_le (by exact WithTop.coe_le_coe.mpr le_top)) hR hd0
    (d := d) (D := max 0 D) (C₀ := max 0 C₀) (C₁ := max 0 C₁)
    (M := max 0 M) (M₁ := max 0 M₁) (C := max 0 C)
  · exact (le_abs_self _).trans ((hD x₀ hx₀).trans (le_max_right _ _))
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · exact le_max_left _ _
  · intro n
    exact (hC (mem_range_self n)).trans (le_max_right _ _)
  · intro x hx
    exact (hM₁ x hx).trans (le_max_right _ _)
  · intro x hx
    exact hmin hx
  · intro x hx
    exact (le_abs_self _).trans ((hD x hx).trans (le_max_right _ _))
  · intro x hx
    exact (hM x hx).trans (le_max_right _ _)
  · intro a x hx
    exact (hC₀ (a,x) ⟨mem_univ _,hx⟩).trans (le_max_right _ _)
  · intro a x hx
    exact (hC₁ (a,x) ⟨mem_univ _,hx⟩).trans (le_max_right _ _)
  · exact hP.differentiable (by simp)
  · exact hV
  · exact hPV
  · exact hHc
  · exact hAcont
  · exact hδt

end ThreeTorus

namespace ThreeTorus
open Function
open scoped ComplexConjugate

lemma exactPassageCoeff_neg (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    exactPassageCoeff (-m) H (fun x => conj (A x)) j a =
      conj (exactPassageCoeff m H A (-j) a) := by
  unfold exactPassageCoeff fourierCoeff passageFourierInput
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [smul_eq_mul, neg_neg, map_mul, fourier_neg]

lemma exactPassageCoeff_neg_norm (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (a : UnitAddCircle) :
    ‖exactPassageCoeff (-m) H (fun x => conj (A x)) j a‖ =
      ‖exactPassageCoeff m H A (-j) a‖ := by
  rw [exactPassageCoeff_neg,Complex.norm_conj]

lemma summed_mass_reflect (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (W : ℝ → UnitAddCircle → ℝ) (n : ℕ) :
    (∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff (-m) H (fun x => conj (A x)) j a‖^2-
        (n:ℝ)⁻¹*W (-(j:ℝ)/n) a| ∂AddCircle.haarAddCircle) =
    (∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m H A j a‖^2-
        (n:ℝ)⁻¹*W ((j:ℝ)/n) a| ∂AddCircle.haarAddCircle) := by
  simp_rw [exactPassageCoeff_neg_norm]
  simpa only [Int.cast_neg] using
    tsum_comp_neg (fun j : ℤ => ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m H A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle)

lemma stationaryWeight_reflect {I : Set ℝ} {J : ℝ → ℝ}
    (hinj : InjOn J I) (A : ℝ → ℂ) (s : ℝ) :
    stationaryWeight I (fun x => -J x) (fun x => conj (A x)) s =
      stationaryWeight I J A (-s) := by
  classical
  have hi : InjOn (fun x => -J x) I := fun x hx y hy he => hinj hx hy (neg_injective he)
  by_cases hs : -s ∈ J '' I
  · obtain ⟨x,hx,hxs⟩ := hs
    have hneg : -J x = s := by linarith
    have hm : s ∈ (fun x => -J x) '' I := ⟨x,hx,hneg⟩
    have h₁ : invFunOn (fun x => -J x) I s = x := by
      rw [← hneg]; exact hi.leftInvOn_invFunOn hx
    have h₂ : invFunOn J I (-s) = x := by
      rw [← hxs]; exact hinj.leftInvOn_invFunOn hx
    simp only [stationaryWeight,branchDensity,indicator_of_mem hm,
      indicator_of_mem (show -s ∈ J '' I from ⟨x,hx,hxs⟩),h₁,h₂,
      Complex.norm_conj]
    change ‖A x‖^2/|deriv (-J) x| = ‖A x‖^2/|deriv J x|
    rw [deriv.neg,abs_neg]
  · have hm : s ∉ (fun x => -J x) '' I := by
      rintro ⟨x,hx,he⟩
      exact hs ⟨x,hx,by linarith⟩
    simp only [stationaryWeight,branchDensity,indicator_of_notMem hm,indicator_of_notMem hs]

/-- The source passage mass theorem at every nonzero angular index. -/
lemma exactPassageCoeff_summed
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-
        (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
          (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hm with hm | hm
  · have hm' : 0 < -m := neg_pos.mpr hm
    have hconjA₀ (a : UnitAddCircle) : ContDiff ℝ 2 (fun x => conj (A₀ a x)) :=
      Complex.conjCLE.contDiff.comp (hA₀ a)
    have hconjAc : Continuous (fun p : UnitAddCircle × ℝ => conj (A₀ p.1 p.2)) :=
      Complex.continuous_conj.comp hAc
    have hconjAd : Continuous (fun p : UnitAddCircle × ℝ =>
        deriv (fun x => conj (A₀ p.1 x)) p.2) := by
      simpa only [show ∀ z : ℂ, conj z = star z from fun _ => rfl, deriv.star]
        using hAd.star
    have hs := exactPassageCoeff_summed_positive (A := fun x => conj (A x))
      (A₀ := fun a x => conj (A₀ a x)) hm' hH
      (fun a x hx => congrArg (conj : ℂ → ℂ) (hA a x hx))
      hconjA₀ hconjAc hconjAd
      (fun a x hx => hsupp a (by simpa using hx))
      hlo huo hlu hR hP hV hPV hd hHc (Complex.continuous_conj.comp hAcont) hδt
    have hJ : InjOn (fun x => (-m:ℝ)*V x) (Icc (l-R) (u+R)) := by
      apply StrictMonoOn.injOn
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        ((contDiff_const.mul hV).continuous.continuousOn)
      intro x hx
      rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
      exact mul_pos (by exact_mod_cast hm') (hd x (by
        have hx' := interior_subset hx
        constructor <;> linarith [hx'.1,hx'.2]))
    have href (a : UnitAddCircle) (s : ℝ) :
        stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s =
        stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
          (fun x => conj (A₀ a x)) (-s) := by
      simpa only [neg_mul, neg_neg, starRingEnd_self_apply] using
        stationaryWeight_reflect hJ (fun x => conj (A₀ a x)) s
    have he (n : ℕ) :
        (∑' j : ℤ, ∫ a : UnitAddCircle,
          |‖exactPassageCoeff m (H n) A j a‖^2-
            (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
              (A₀ a) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle) =
        (∑' j : ℤ, ∫ a : UnitAddCircle,
          |‖exactPassageCoeff (-m) (H n) (fun x => conj (A x)) j a‖^2-
            (n:ℝ)⁻¹*stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
              (fun x => conj (A₀ a x)) ((j:ℝ)/n)| ∂AddCircle.haarAddCircle) := by
      simp_rw [href]
      simpa only [neg_neg,starRingEnd_self_apply, Int.cast_neg, neg_div] using
        summed_mass_reflect (-m) (H n) (fun x => conj (A x))
          (fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (-m:ℝ)*V x)
            (fun x => conj (A₀ a x)) s) n
    simpa only [he,Int.cast_neg] using hs
  · exact exactPassageCoeff_summed_positive hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
      hP hV hPV hd hHc hAcont hδt

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma circle_integral_lift (o : ℝ) (q : UnitAddCircle → ℝ) :
    (∫ x, circleDensityLift o q x) = ∫ a, q a ∂AddCircle.haarAddCircle := by
  rw [circleDensityLift,integral_indicator measurableSet_Ioc]
  have h := AddCircle.integral_preimage 1 o q
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using h

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

/-- Lifting a circle density on one period commutes with every measurable
spectral pushforward. This includes the actual jitter, not just polynomial tests. -/
lemma circleDensityLift_pushforward {Y : Type*} [MeasurableSpace Y]
    {q : UnitAddCircle → ℝ} (hq : Integrable q AddCircle.haarAddCircle)
    {T : UnitAddCircle → Y} (hT : Measurable T) (o : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (circleDensityLift o q)).map
      (fun x : ℝ => T (x : UnitAddCircle)) =
    (AddCircle.haarAddCircle.withDensityᵥ q).map T := by
  have hTm : Measurable (fun x : ℝ => T (x : UnitAddCircle)) := hT.comp AddCircle.measurable_mk'
  ext s hs
  rw [VectorMeasure.map_apply _ hTm hs,VectorMeasure.map_apply _ hT hs,
    withDensityᵥ_apply (integrable_circleDensityLift hq o) (hTm hs),
    withDensityᵥ_apply hq (hT hs)]
  rw [← integral_indicator (hTm hs),← integral_indicator (hT hs)]
  rw [← circle_integral_lift o ((T ⁻¹' s).indicator q)]
  congr 1
  funext x
  by_cases hx : x ∈ Ioc o (o+1) <;> by_cases hxs : T (x : UnitAddCircle) ∈ s <;>
    simp [circleDensityLift,hx,hxs]

lemma circleDensityLift_eq {q : UnitAddCircle → ℝ} {q₀ : ℝ → ℝ} {o : ℝ}
    (he : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hs : Function.support q₀ ⊆ Ioc o (o+1)) : circleDensityLift o q = q₀ := by
  funext x
  by_cases hx : x ∈ Ioc o (o+1)
  · simp [circleDensityLift,hx,he x hx]
  · have hzero : q₀ x = 0 := by by_contra hn; exact hx (hs hn)
    simp [circleDensityLift,hx,hzero]

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Exact pushforward of the old squared coefficient on a branch. The only
inverse assumptions are the ordinary left-inverse identities on that branch. -/
lemma branchDensity_pushforward {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I)) (hJm : Measurable J)
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q) (hqs : Function.support q ⊆ I) :
    ((volume : Measure ℝ).withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J g D q) := by
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hq.integrableOn
  ext s hs
  rw [VectorMeasure.map_apply _ hJm hs,withDensityᵥ_apply hq (hJm hs),withDensityᵥ_apply hK hs]
  rw [← integral_indicator (hJm hs),← integral_indicator hs]
  have hleft : (∫ x, (J ⁻¹' s).indicator q x) = ∫ x in I, (J ⁻¹' s).indicator q x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hqx : q x = 0 := by
      by_contra hh
      exact hx (hqs hh)
    by_cases hxs : x ∈ J ⁻¹' s <;> simp [hxs,hqx]
  have hright : (∫ y, s.indicator (branchDensity I J g D q) y) =
      ∫ y in J '' I, s.indicator (branchDensity I J g D q) y := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_cases hys : y ∈ s <;> simp [hys,branchDensity,hy]
  rw [hleft,hright,integral_image_eq_integral_abs_deriv_smul hI hJ hinj]
  apply setIntegral_congr_fun hI
  intro x hx
  dsimp only
  rw [smul_eq_mul]
  by_cases hxs : J x ∈ s
  · rw [indicator_of_mem (show x ∈ J ⁻¹' s from hxs),indicator_of_mem hxs,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  · rw [indicator_of_notMem (show x ∉ J ⁻¹' s from hxs),indicator_of_notMem hxs,mul_zero]

lemma density_map_congr_support {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {f : X → ℝ} (hf : Integrable f μ)
    {T₁ T₂ : X → Y} (h₁ : Measurable T₁) (h₂ : Measurable T₂)
    (he : ∀ x, f x ≠ 0 → T₁ x = T₂ x) :
    (μ.withDensityᵥ f).map T₁ = (μ.withDensityᵥ f).map T₂ := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply _ h₁ hs,VectorMeasure.map_apply _ h₂ hs,
    withDensityᵥ_apply hf (h₁ hs),withDensityᵥ_apply hf (h₂ hs),
    ← integral_indicator (h₁ hs),← integral_indicator (h₂ hs)]
  congr 1
  funext x
  change (if T₁ x ∈ s then f x else 0) = (if T₂ x ∈ s then f x else 0)
  by_cases hx : f x = 0
  · simp [hx]
  · rw [he x hx]

/-- The branch-Jacobian formula on the actual circle. The global periodic
jitter need not be injective; only the good arc bearing the weight is used. -/
lemma circle_branch_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map J =
      (volume : Measure ℝ).withDensityᵥ (branchDensity I J₀ g D q₀) := by
  have hlift := circleDensityLift_eq hq₀ hq₀s
  have hi : Integrable q₀ := by rw [← hlift]; exact integrable_circleDensityLift hq o
  rw [← circleDensityLift_pushforward hq hj o,hlift]
  rw [density_map_congr_support (T₁ := fun x : ℝ => J (x : UnitAddCircle)) hi (hj.comp AddCircle.measurable_mk') hj₀
    (fun x hx => hJe x (hqs hx))]
  exact branchDensity_pushforward hI himage hj₀ hJ hinj hg hD hi hqs

/-- Exact Jacobian cancellation in the unfolded output frequency t=(j+y)/N. -/
lemma temporalFrequency_pushforward {q : ℝ → ℝ} (hq : Integrable q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    ((volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y)).map (fun y => (j+y)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have hmap : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hq' : Integrable (fun t => q (n*t-j)) := by
    simpa only [sub_eq_add_neg] using
      (integrable_comp_mul_left_iff (fun x => q (x+ -j)) hn.ne').2 (hq.comp_add_right (-j))
  ext s hs
  rw [VectorMeasure.map_apply _ hmap hs,withDensityᵥ_apply (hq.const_mul n⁻¹) (hmap hs),
    withDensityᵥ_apply hq' hs,integral_const_mul]
  let F : ℝ → ℝ := ((fun y : ℝ => (j+y)/n) ⁻¹' s).indicator q
  have he : (fun t => F (n*t-j)) = s.indicator (fun t => q (n*t-j)) := by
    funext t
    by_cases ht : t ∈ s <;> simp [F,ht,hn.ne']
  rw [← integral_indicator (hmap hs),← integral_indicator hs,← he]
  change n⁻¹*(∫ y, F y) = ∫ t, F (n*t-j)
  rw [Measure.integral_comp_mul_left (fun x => F (x-j)) n,integral_sub_right_eq_self]
  simp only [smul_eq_mul,abs_of_pos (inv_pos.mpr hn)]

/-- Pushforward through a fixed smooth jitter followed by the output affine frequency.
This is the exact (not weak or asymptotic) density appearing in the passage. -/
lemma temporalFrequency_pushforward_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {W : X → ℝ} {q : ℝ → ℝ} {J : X → ℝ}
    (hW : Integrable W μ) (hq : Integrable q) (hJ : Measurable J)
    (hpush : (μ.withDensityᵥ W).map J = (volume : Measure ℝ).withDensityᵥ q)
    {n : ℝ} (hn : 0 < n) (j : ℝ) :
    (μ.withDensityᵥ (fun a => n⁻¹*W a)).map (fun a => (j+J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (fun t => q (n*t-j)) := by
  have haf : Measurable (fun y : ℝ => (j+y)/n) := by fun_prop
  have hcomp (v : VectorMeasure X ℝ) :
      v.map (fun a => (j+J a)/n) = (v.map J).map (fun y : ℝ => (j+y)/n) := by
    ext s hs
    have hcompm : Measurable (fun a => (j+J a)/n) := haf.comp hJ
    rw [VectorMeasure.map_apply _ hcompm hs,
      VectorMeasure.map_apply _ haf hs,VectorMeasure.map_apply _ hJ (haf hs)]
    rfl
  rw [hcomp]
  have he : μ.withDensityᵥ (fun a => n⁻¹*W a) = n⁻¹ • μ.withDensityᵥ W := by
    ext s hs
    rw [withDensityᵥ_apply (hW.const_mul _) hs,smul_apply,withDensityᵥ_apply hW hs,
      integral_const_mul,smul_eq_mul]
  have heq : (volume : Measure ℝ).withDensityᵥ (fun y => n⁻¹*q y) =
      n⁻¹ • (volume : Measure ℝ).withDensityᵥ q := by
    ext s hs
    rw [withDensityᵥ_apply (hq.const_mul _) hs,smul_apply,withDensityᵥ_apply hq hs,
      integral_const_mul,smul_eq_mul]
  rw [he,VectorMeasure.map_smul,hpush,← heq]
  exact temporalFrequency_pushforward hq hn j

lemma scaledBranchKernel_eq {I : Set ℝ} (J g D q : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (y : ℝ) :
    branchDensity I (fun x => s*J x) (fun y => g (y/s)) (fun x => s*D x) q y =
      scaledBranchKernel I J g D q s y := by
  classical
  have he : y ∈ (fun x => s*J x) '' I ↔ y/s ∈ J '' I := by
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by rw [← hxy]; field_simp⟩
    · rintro ⟨x,hx,hxy⟩
      exact ⟨x,hx,by change s*J x = y; rw [hxy]; field_simp⟩
  by_cases hy : y/s ∈ J '' I
  · simp only [branchDensity,scaledBranchKernel,indicator_of_mem hy,
      indicator_of_mem (he.mpr hy),abs_mul]
    ring
  · simp only [branchDensity,scaledBranchKernel,indicator_of_notMem hy,
      indicator_of_notMem (fun h => hy (he.mp h)),mul_zero]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

/-- The exact branch kernel in the new temporal coordinate, on the torus.
Only the good arc need be injective, as in the geometric passage. -/
lemma circle_mode_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {s n : ℝ} (hs : s ≠ 0) (hn : 0 < n) (j : ℝ) :
    (AddCircle.haarAddCircle.withDensityᵥ (fun a => n⁻¹*q a)).map
        (fun a => (j+s*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ
        (fun t => scaledBranchKernel I J₀ g D q₀ s (n*t-j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hK := integrable_branchDensity hI himage hJ hinj hg hD hqi.integrableOn
  have hsim : MeasurableSet ((fun x => s*J₀ x) '' I) := by
    have he : (fun x => s*J₀ x) '' I = (fun y : ℝ => s*y) '' (J₀ '' I) := by
      rw [image_image]
    rw [he]
    exact (Homeomorph.mulLeft₀ s hs).measurableEmbedding.measurableSet_image.mpr himage
  have hp := circle_branch_pushforward (g := fun y => g (y/s)) hq hq₀ hq₀s hqs
    (measurable_const.mul hj) (measurable_const.mul hj₀)
    (fun x hx => congrArg (fun y => s*y) (hJe x hx)) hI hsim
    (fun x hx => (hJ x hx).const_mul s)
    (fun x hx y hy he => hinj hx hy (mul_left_cancel₀ hs he))
    (fun x hx => show g (s*J₀ x/s) = x by simpa [hs] using hg x hx)
    (fun x hx => mul_ne_zero hs (hD x hx))
  have he : branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀ =
      scaledBranchKernel I J₀ g D q₀ s := funext (scaledBranchKernel_eq _ _ _ _ hs)
  change (AddCircle.haarAddCircle.withDensityᵥ q).map (fun a => s*J a) =
    (volume : Measure ℝ).withDensityᵥ
      (branchDensity I (fun x => s*J₀ x) (fun y => g (y/s)) (fun x => s*D x) q₀) at hp
  rw [he] at hp
  exact temporalFrequency_pushforward_comp hq (integrable_scaledBranchKernel hK hs)
    (measurable_const.mul hj) hp hn j

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

/-- Exact density of an actual circle mode before any stationary approximation. -/
lemma unfoldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ g D : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : Function.support q₀ ⊆ Ioc o (o+1)) (hqs : Function.support q₀ ⊆ I)
    (hj : Measurable J) (hj₀ : Measurable J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hI : MeasurableSet I) (himage : MeasurableSet (J₀ '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J₀ (D x) I x) (hinj : InjOn J₀ I)
    (hg : ∀ x ∈ I, g (J₀ x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (j+(j/n)*J a)/n) =
      (volume : Measure ℝ).withDensityᵥ (unfoldedModeDensity I J₀ g D q₀ n j) := by
  have hsupp (L : Set ℝ) (hh : Function.support q₀ ⊆ L) :
      Function.support (fun a => n*q₀ a) ⊆ L := by
    intro x hx
    apply hh
    intro hz
    exact hx (by simp only [hz,mul_zero])
  have hp := circle_mode_pushforward (q := fun a => n*q a) (q₀ := fun a => n*q₀ a)
    (s := j/n) (hq.const_mul n) (fun x hx => congrArg (fun y => n*y) (hq₀ x hx))
    (hsupp _ hq₀s) (hsupp _ hqs) hj hj₀ hJe hI himage hJ hinj hg hD
    (div_ne_zero hjn hn.ne') hn j
  change _ = (volume : Measure ℝ).withDensityᵥ
    (fun t => scaledBranchKernel I J₀ g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul] using hp

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

lemma stationaryWeight_signed_compact_continuous {J : ℝ → ℝ}
    {A : UnitAddCircle → ℝ → ℂ} {l u R : ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hA : Continuous A.uncurry) (hs : ∀ a, support (A a) ⊆ Icc l u)
    (hR : 0 < R) (hi : InjOn J (Icc (l-R) (u+R)))
    (hd : ∀ x ∈ Ioo (l-R) (u+R), deriv J x ≠ 0) :
    Continuous (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) ∧
    HasCompactSupport (fun p : ℝ × UnitAddCircle => stationaryWeight (Icc (l-R) (u+R)) J (A p.2) p.1) := by
  let F : ℝ × UnitAddCircle → ℝ := fun p => ‖A p.2 p.1‖^2
  have hF : Continuous F := (hA.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hFs : support F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) := by
    intro p hp
    refine ⟨hs p.2 ?_,mem_univ _⟩
    intro hz
    exact hp (by simp [F,show A p.2 p.1 = 0 from hz])
  have hFt : tsupport F ⊆ Icc l u ×ˢ (univ : Set UnitAddCircle) :=
    closure_minimal hFs (isClosed_Icc.prod isClosed_univ)
  have hc : HasCompactSupport F :=
    (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport F) hFt
  have hsub : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [stationaryWeight_family_of_branch Ioo_subset_Icc_self hi (fun a => (hs a).trans hsub)]
  exact ⟨branchFamily_continuous hJ isOpen_Ioo (hi.mono Ioo_subset_Icc_self) hd hF hc
    (fun p hp => ⟨hsub (hFt hp).1,mem_univ _⟩),branchFamily_compact hJ.continuous hc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma periodizedReal_add_int (q : ℝ → ℝ) (x : ℝ) (j : ℤ) :
    periodizedReal q (x+j) = periodizedReal q x := by
  have h := (Equiv.addLeft j).tsum_eq (fun k : ℤ => q (x+k))
  change (∑' k : ℤ, q (x+(j:ℝ)+(k:ℝ))) = ∑' k : ℤ, q (x+(k:ℝ))
  rw [← h]
  apply tsum_congr
  intro k
  congr 1
  change x+(j:ℝ)+(k:ℝ) = x+((j+k:ℤ):ℝ)
  simp only [Int.cast_add,add_assoc]

/-- The displayed lattice formula holds for every real representative. -/
lemma foldCircleDensity_coe_all (q : ℝ → ℝ) (x : ℝ) :
    foldCircleDensity q (x:UnitAddCircle) = ∑' k : ℤ, q (x+k) := by
  let y : ℝ := (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).1
  have hy : y ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 (x:UnitAddCircle)).2
  have hxy : (y:UnitAddCircle) = (x:UnitAddCircle) :=
    (AddCircle.equivIoc 1 0).symm_apply_apply (x:UnitAddCircle)
  have hz : ((y-x:ℝ):UnitAddCircle) = 0 := by rw [AddCircle.coe_sub,hxy,sub_self]
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).1 hz
  have he : y = x+(k:ℝ) := by simpa only [zsmul_eq_mul,mul_one] using eq_add_of_sub_eq' hk.symm
  rw [← hxy,foldCircleDensity_coe hy,he,periodizedReal_add_int]
  rfl

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma retained_unfolded_regular {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {n : ℕ} (hn : 0 < n) {j : ℤ} (hj : j ≠ 0) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) ∧
    Integrable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) := by
  have hq : Continuous (retainedCircleWeight ψ χ c n j) :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hc n j).norm.pow 2)
  exact ⟨measurable_unfoldedModeDensity hJ hIo hinj hd
      (measurable_circleDensityLift hq.measurable o) n j,
    integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
      (fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt) hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
      (integrable_circleDensityLift (retainedCircleWeight_integrable hψ hχ hc n j) o)
      (by exact_mod_cast hn) (by exact_mod_cast hj)⟩

lemma vectorMeasure_map_comp {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [AddCommMonoid E] [TopologicalSpace E]
    (ν : VectorMeasure X E) {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

/-- The folded expression is the density of the actual mode spectral map
j(1+J/n)/n modulo one. Thus the circle limit is a spectral-density statement. -/
lemma foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensityᵥ q).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hp := unfoldedModeDensity_pushforward hq hq₀ hq₀s hqs hj hJ.continuous.measurable hJe
    hIo.measurableSet (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hn hjn
  have h := congrArg (fun ν : VectorMeasure ℝ ℝ => ν.map (fun t : ℝ => (t:UnitAddCircle))) hp
  have hf : Measurable (fun a => (j+(j/n)*J a)/n) :=
    (measurable_const.add (hj.const_mul _)).div_const n
  have hg : Measurable (fun t : ℝ => (t:UnitAddCircle)) := AddCircle.measurable_mk'
  rw [vectorMeasure_map_comp _ hf hg] at h
  rw [foldCircleDensity_pushforward
    (measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j)
    (integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn)] at h
  exact h

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Transmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma lawJitter_injOn {ρ : ℝ → ℝ} {δ : ℝ} (c : LawCutoffs δ)
    (hρ : Continuous ρ) (hi : Integrable ρ) (hp : ∀ y, 0 < ρ y)
    (hm : ∫ y, ρ y = 1) (hδ : 0 < δ) : InjOn (lawJitter ρ c) (Ioo δ (1-δ)) := by
  intro a ha b hb he
  rw [lawJitter_eq_quantile c hδ ⟨ha.1.le,ha.2.le⟩,
    lawJitter_eq_quantile c hδ ⟨hb.1.le,hb.2.le⟩] at he
  have he' := congrArg (cumulative ρ) he
  rwa [cumulative_quantile hρ hi hp hm ⟨by linarith [ha.1],by linarith [ha.2]⟩,
    cumulative_quantile hρ hi hp hm ⟨by linarith [hb.1],by linarith [hb.2]⟩] at he'

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma quantileCircleJitter_coe {δ : ℝ} (ρ : ℝ → ℝ) (c : LawCutoffs δ) (a : ℝ) :
    quantileCircleJitter ρ c (a:UnitAddCircle) = lawJitter ρ c a := rfl

lemma continuous_quantileCircleJitter {δ : ℝ} {ρ : ℝ → ℝ} (c : LawCutoffs δ)
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hm : ∫ y, ρ y = 1) : Continuous (quantileCircleJitter ρ c) := by
  apply Continuous.quotient_lift
  exact (lawJitter_smooth c hρ hi hp hm).continuous

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_RetainedPackets
attribute [-instance] _root_.OAI.ThreeTorus.tripleVolume_regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained passage vectors, spectral identities, regularity, old marginals, and quantitative cutoff losses. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma integral_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Measurable H)
    (f : TripleTorus → ℝ) :
    (∫ x, f (passageChart H x) ∂tripleVolume) = ∫ x, f x ∂tripleVolume := by
  let e : TripleTorus ≃ᵐ TripleTorus :=
    { toEquiv := passageChart H
      measurable_toFun := (measurePreserving_passageChart hH).measurable
      measurable_invFun := passageChart_inverse_measurable hH }
  exact (measurePreserving_passageChart hH).integral_comp e.measurableEmbedding f

/-- A complete quantitative form of the physical transport estimate (2.9).
The sole right-hand quantity is the actual summed Fourier-mass error. -/
lemma physical_retainedPassage_error_le {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A)
    (S : Finset ℤ) (χ W : ℤ → UnitAddCircle → ℝ) (hχc : ∀ j, Continuous (χ j))
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hχ : ∀ j a, 0 ≤ χ j a ∧ χ j a ≤ 1)
    (hW : ∀ j a, W j a ≠ 0 → j ∈ S ∧ χ j a = 1)
    (hE : ∀ j, Integrable (fun a => |‖exactPassageCoeff m H A j a‖^2-W j a|)
      AddCircle.haarAddCircle)
    (hp : ∀ᵐ a ∂AddCircle.haarAddCircle,
      Summable (fun j => |‖exactPassageCoeff m H A j a‖^2-W j a|))
    (hs : Summable (fun j => ∫ a, |‖exactPassageCoeff m H A j a‖^2-W j a|
      ∂AddCircle.haarAddCircle)) :
    (∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-retainedPassage m H A S χ ψ (passageChart H x)‖^2
        ∂tripleVolume) ≤
      ∑' j : ℤ, ∫ a, |‖exactPassageCoeff m H A j a‖^2-W j a| ∂AddCircle.haarAddCircle := by
  have he := integral_passageChart hH.measurable (fun x : TripleTorus =>
    ‖(ψ x.2.1:ℂ)*packet m A ((passageChart H).symm x)-retainedPassage m H A S χ ψ x‖^2)
  simp only [Equiv.symm_apply_apply] at he
  change (∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-retainedPassage m H A S χ ψ (passageChart H x)‖^2
        ∂tripleVolume) = _ at he
  rw [he,integrated_retainedPassage_error hH hA S χ hχc ψ hψc]
  let E : UnitAddCircle → UnitAddCircle → ℝ := fun a θ =>
    ‖passageFourierInput m H A a θ-
      ∑ j ∈ S, (χ j a:ℂ)*exactPassageCoeff m H A j a*fourier j θ‖^2
  have hEc : Continuous E.uncurry := by
    apply Continuous.pow
    apply Continuous.norm
    apply (continuous_passageFourierInput hH hA).sub
    apply continuous_finsetSum
    intro j _hj
    exact (((Complex.continuous_ofReal.comp (hχc j)).comp continuous_fst).mul
      ((continuous_exactPassageCoeff hH hA j).comp continuous_fst)).mul
      ((fourier j).continuous.comp continuous_snd)
  have hIc : Continuous (fun a => ∫ θ, E a θ ∂AddCircle.haarAddCircle) := by
    simpa only [setIntegral_univ] using
      continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle) hEc isCompact_univ
  have hIi : Integrable (fun a => ∫ θ, E a θ ∂AddCircle.haarAddCircle) AddCircle.haarAddCircle :=
    hIc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ a, ∫ θ, E a θ ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun a => mul_nonneg (sq_nonneg _)
          (integral_nonneg (fun _ => sq_nonneg _)))
      · exact hIi
      · filter_upwards [] with a
        exact mul_le_of_le_one_left (integral_nonneg (fun _ => sq_nonneg _))
          (by nlinarith [(hψ a).1,(hψ a).2])
    _ ≤ _ := integrated_Fourier_cutoff_le_mass_error
      (fun a => (continuous_passageFourierInput hH hA).comp (continuous_const.prodMk continuous_id)) S χ W hχ hW hE hp hs

lemma pointwise_array_mass_error_summable {c : ℤ → UnitAddCircle → ℂ}
    {W : ℝ → UnitAddCircle → ℝ} (hc : HasCompactSupport W.uncurry)
    (hcs : ∀ a, Summable (fun j => ‖c j a‖^2)) {n : ℕ} (hn : 0 < n) (a : UnitAddCircle) :
    Summable (fun j : ℤ => |‖c j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|) := by
  obtain ⟨S,hS⟩ := compact_lattice_support hc hn 0
  have hw : Summable (fun j : ℤ => |(n:ℝ)⁻¹*W ((j:ℝ)/n) a|) := by
    apply summable_of_ne_finset_zero (s := S)
    intro j hj
    have hz : W ((j:ℝ)/n) a = 0 := by simpa using hS j hj a
    simp [hz]
  refine Summable.of_nonneg_of_le (f := fun j => ‖c j a‖^2+|(n:ℝ)⁻¹*W ((j:ℝ)/n) a|)
    (fun _ => abs_nonneg _) (fun j => ?_) ((hcs a).add hw)
  have hh := abs_sub_le (‖c j a‖^2) 0 ((n:ℝ)⁻¹*W ((j:ℝ)/n) a)
  have he : |‖c j a‖^2| = ‖c j a‖^2 := abs_of_nonneg (sq_nonneg _)
  simpa only [sub_zero,zero_sub,abs_neg,he] using hh

/-- The actual physical packet cutoff error tends to zero once the unrounded
stationary mass theorem is applied. All summability hypotheses are derived. -/
lemma physical_retainedPassage_tendsto
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {W : ℝ → UnitAddCircle → ℝ}
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hWc : Continuous W.uncurry) (hWk : HasCompactSupport W.uncurry)
    (S : ℕ → Finset ℤ) (χ : ℕ → ℤ → UnitAddCircle → ℝ)
    (hχc : ∀ n j, Continuous (χ n j)) (hχ : ∀ n j a, 0 ≤ χ n j a ∧ χ n j a ≤ 1)
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hW : ∀ (n : ℕ), 0 < n → ∀ (j : ℤ) (a : UnitAddCircle), W ((j:ℝ)/n) a ≠ 0 → j ∈ S n ∧ χ n j a = 1)
    (ht : Tendsto (fun n : ℕ => ∑' j : ℤ, ∫ a : UnitAddCircle,
      |‖exactPassageCoeff m (H n) A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|
        ∂AddCircle.haarAddCircle) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A (S n) (χ n) ψ (passageChart (H n) x)‖^2
        ∂tripleVolume) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) _ ht
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hEc (j : ℤ) : Continuous (fun a =>
      |‖exactPassageCoeff m (H n) A j a‖^2-(n:ℝ)⁻¹*W ((j:ℝ)/n) a|) := by
    exact (((continuous_exactPassageCoeff (hH n) hA j).norm.pow 2).sub
      (continuous_const.mul (hWc.comp (continuous_const.prodMk continuous_id)))).abs
  apply physical_retainedPassage_error_le (hH n) hA (S n) (χ n)
    (fun j a => (n:ℝ)⁻¹*W ((j:ℝ)/n) a) (hχc n) ψ hψc hψ (hχ n)
  · intro j a ha
    exact hW n hn j a (fun hz => ha (by simp [hz]))
  · intro j
    exact (hEc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · apply Filter.Eventually.of_forall
    intro a
    exact pointwise_array_mass_error_summable hWk
      (fun a => continuous_fourier_summable
        ((continuous_passageFourierInput (hH n) hA).comp (continuous_const.prodMk continuous_id))) hn a
  · simpa only [sub_zero] using integrated_array_mass_error_summable hWc hWk
      (continuous_exactPassageCoeff (hH n) hA) (exactPassageCoeff_summable (hH n) hA) hn 0

/-- Physical transport for the actual signed packet. The summed stationary
mass error is proved, not an input to this statement. -/
lemma exact_physical_retainedPassage_tendsto
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {P V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(P x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hsupp : ∀ a, Function.support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv P = V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {χ : ℝ → UnitAddCircle → ℝ} (hχc : Continuous χ.uncurry)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (ψ : UnitAddCircle → ℝ) (hψc : Continuous ψ) (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (A₀ a) s ≠ 0 → χ s a = 1)
    (S : ℕ → Finset ℤ)
    (hS : ∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) :
    Tendsto (fun n => ∫ x : TripleTorus,
      ‖(ψ x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
          (passageChart (H n) x)‖^2 ∂tripleVolume) atTop (𝓝 0) := by
  have hbranch := scaled_speed_good_branch hm hR hV hd
  have hW := stationaryWeight_signed_compact_continuous (contDiff_const.mul hV) hAc
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hR hbranch.1 hbranch.2
  apply physical_retainedPassage_tendsto
    (W := fun s a => stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m:ℝ)*V x) (A₀ a) s) hHc hAcont hW.1 hW.2 S
    (fun n j => χ ((j:ℝ)/n))
    (fun _ _ => hχc.comp (continuous_const.prodMk continuous_id))
    (fun _ _ _ => hχ _ _) ψ hψc hψ
  · intro n hn j a hw
    have he := hχW ((j:ℝ)/n) a hw
    refine ⟨?_,he⟩
    by_contra hj
    have hz := hS n hn j hj a
    linarith
  · exact exactPassageCoeff_summed hm hH hA hA₀ hAc hAd hsupp hlo huo hlu hR
      hP hV hPV hd hHc hAcont hδt

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology

noncomputable section
open Set Function Filter
open scoped Topology

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology
namespace ThreeTorus
namespace CompactParameter

/-- Compact-parameter differentiation, used by the exact passage near epsilon=0. -/
lemma hasFDerivAt_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ 1 F) (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ t in a..b, F (y,t))
      (∫ t in a..b, (fderiv ℝ F (x,t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  let D : E × ℝ → E →L[ℝ] G := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD : Continuous D := hF.continuous_fderiv (by norm_num) |>.clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hD.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun y t => F (y,t)) (F' := fun y t => D (y,t))
    (bound := fun _ => C) (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact Eventually.of_forall (fun y => (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro y hy
    exact hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact Eventually.of_forall (fun t y _ => by
      simpa [D,Function.comp_def] using ((hF.differentiable one_ne_zero ((ContinuousLinearMap.inl ℝ E ℝ) y+(0,t))).hasFDerivAt).comp y
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.add_const (0,t)))

/-- Smooth parameter integration over a fixed compact interval. -/
lemma contDiff_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (n : ℕ) {F : E × ℝ → G} (hF : ContDiff ℝ n F) (a b : ℝ) :
    ContDiff ℝ n (fun y => ∫ t in a..b, F (y,t)) := by
  induction n generalizing G with
  | zero =>
    apply contDiff_zero.mpr
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous (Function.uncurry (fun y t => F (y,t))) from hF.continuous) a b
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] G := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD : ContDiff ℝ n D := (hF.fderiv_right (by simp)).clm_comp contDiff_const
    have hder (x : E) := hasFDerivAt_compact_integral (hF.of_le (by exact_mod_cast Nat.succ_pos n)) a b x
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 by simp, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (fun y => ∫ t in a..b, F (y,t)) =
          fun y => ∫ t in a..b, D (y,t) := by
        funext y
        exact (hder y).fderiv
      rw [heq]
      exact ih hD

lemma smooth_compact_integral
    {E : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (a b : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ t in a..b, F (y,t)) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_compact_integral n (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))) a b

end CompactParameter

/-- Smoothness of a Fourier coefficient in an arbitrary finite-dimensional
parameter, obtained from a compact interval integral of the literal lift. -/
lemma smooth_fourierCoeff_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → UnitAddCircle → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => f p.1 (p.2 : UnitAddCircle))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => fourierCoeff (f x) j) := by
  have hchar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : E × ℝ => (fourier (-j) (p.2 : UnitAddCircle) : ℂ)) := by
    simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp
  have h := CompactParameter.smooth_compact_integral (hchar.mul hf) 0 1
  have he (x : E) : fourierCoeff (f x) j =
      ∫ t in (0:ℝ)..1, (fourier (-j) (t : UnitAddCircle) : ℂ) * f x t := by
    simpa only [one_div_one,one_smul,zero_add,smul_eq_mul] using
      fourierCoeff_eq_intervalIntegral (f x) j 0
  simpa only [he] using h

lemma smooth_fourier_lift (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (fourier m (x : UnitAddCircle) : ℂ)) := by
  simp only [fourier_coe_apply,Complex.ofReal_one,div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Smoothness of the exact old-amplitude coefficients; no stationary-phase
approximation replaces these coefficients. -/
lemma smooth_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {Hl : ℝ → ℝ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t : UnitAddCircle) = (Hl t : UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A (p.1,p.2))) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : ℝ => exactPassageCoeff m H A j a) := by
  apply smooth_fourierCoeff_param
  change ContDiff ℝ _ (fun p : ℝ × ℝ => A (p.2,p.1)*fourier m (H p.2))
  simp_rw [hH]
  exact (hA.comp (contDiff_snd.prodMk contDiff_fst)).mul ((smooth_fourier_lift m).comp (hHl.comp contDiff_snd))

end ThreeTorus

noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology ENNReal
namespace ThreeTorus

/-- A nonnegative integrable density identity proved with signed vector
measures is the identical ordinary measure identity. -/
lemma positive_density_map_of_vectorMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} {q : X → ℝ} {p : Y → ℝ}
    (hf : Measurable f) (hq : Integrable q μ) (hp : Integrable p ν)
    (hq0 : ∀ x, 0 ≤ q x) (hp0 : ∀ y, 0 ≤ p y)
    (he : (μ.withDensityᵥ q).map f = ν.withDensityᵥ p) :
    (μ.withDensity (fun x => ENNReal.ofReal (q x))).map f =
      ν.withDensity (fun y => ENNReal.ofReal (p y)) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal hq.integrableOn (Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hp.integrableOn (Eventually.of_forall hp0)]
  congr 1
  have h := congrArg (fun v : VectorMeasure Y ℝ => v s) he
  simpa only [VectorMeasure.map_apply _ hf hs,withDensityᵥ_apply hq (hf hs),
    withDensityᵥ_apply hp hs] using h

lemma branchDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) (y : ℝ) : 0 ≤ branchDensity I J g D q y := by
  classical
  simp only [branchDensity,Set.indicator_apply]
  split_ifs
  · exact div_nonneg (hq _) (abs_nonneg _)
  · rfl

lemma unfoldedModeDensity_nonneg {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : ∀ t, 0 ≤ q t) {n : ℝ} (hn : 0 ≤ n) (j t : ℝ) :
    0 ≤ unfoldedModeDensity I J g D q n j t := by
  unfold unfoldedModeDensity scaledBranchKernel
  exact mul_nonneg (inv_nonneg.mpr (abs_nonneg _))
    (branchDensity_nonneg (fun a => mul_nonneg hn (hq a)) _)

lemma foldCircleDensity_nonneg {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (z : UnitAddCircle) :
    0 ≤ foldCircleDensity q z := by
  unfold foldCircleDensity periodizedReal
  exact tsum_nonneg (fun k => hq _)

lemma retainedPassage_eq_sum_packets (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) (x : TripleTorus) :
    retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ x =
      ∑ j ∈ S, packet j (retainedAmplitude ψ χ m H A n j) x := rfl

lemma retainedAmplitude_norm_sq (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (p : UnitAddCircle × UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j p‖^2 =
      retainedCircleWeight ψ χ (fun n j => exactPassageCoeff m (H n) A j) n j p.1 := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m p.2‖ = 1 from Circle.norm_coe _,
    mul_one,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,retainedCircleWeight]

lemma retainedAmplitude_modulus (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a b : UnitAddCircle) :
    ‖retainedAmplitude ψ χ m H A n j (a,b)‖ =
      ‖retainedAmplitude ψ χ m H A n j (a,0)‖ := by
  simp only [retainedAmplitude,norm_mul,show ‖fourier m b‖ = 1 from Circle.norm_coe _,
    show ‖fourier m (0:UnitAddCircle)‖ = 1 from Circle.norm_coe _]

-- The same elementary identity used in the supplied whitening proof.
lemma map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {ζ : X → Y} {w : Y → ℝ≥0∞}
    (hζ : Measurable ζ) (hw : Measurable w) :
    (μ.withDensity (w ∘ ζ)).map ζ = (μ.map ζ).withDensity w := by
  ext s hs
  rw [Measure.map_apply hζ hs, withDensity_apply _ (hζ hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hζ hs), ← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hζ]
  apply lintegral_congr
  intro x
  rfl

/-- If a coefficient's modulus is independent of its spare coordinate, its
literal packet spectral measure is the single-coordinate weighted image. -/
lemma packetSpectralMeasure_of_modulus
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) {j : ℤ}
    {B : UnitAddCircle × UnitAddCircle → ℂ} {q : UnitAddCircle → ℝ}
    (hq : Measurable q) (hB : ∀ p, ‖B p‖^2 = q p.1) :
    packetSpectralMeasure φ j B =
      (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => j • φ a) := by
  unfold packetSpectralMeasure
  have he : (fun p : UnitAddCircle × UnitAddCircle => ENNReal.ofReal (‖B p‖^2)) =
      (fun a => ENNReal.ofReal (q a)) ∘ Prod.fst := funext (fun p => congrArg _ (hB p))
  rw [he]
  change Measure.map ((fun a => j • φ a) ∘ Prod.fst) _ = _
  rw [← Measure.map_map (show Measurable (fun a => j • φ a) from hφ.const_smul j) measurable_fst,
    map_withDensity_comp slowVolume measurable_fst hq.ennreal_ofReal]
  simp only [slowVolume,Measure.map_fst_prod,measure_univ,one_smul]

lemma retainedCircleWeight_nonneg (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (c : ℕ → ℤ → UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (a : UnitAddCircle) :
    0 ≤ retainedCircleWeight ψ χ c n j a := by unfold retainedCircleWeight; positivity

lemma circleDensityLift_nonneg {q : UnitAddCircle → ℝ} (hq : ∀ a, 0 ≤ q a)
    (o x : ℝ) : 0 ≤ circleDensityLift o q x := by
  classical
  simp only [circleDensityLift,Set.indicator_apply]
  split_ifs
  · exact hq _
  · rfl

/-- The folded branch is the ordinary (positive) spectral density, not just
an identity of signed integrals. -/
lemma positive_foldedModeDensity_pushforward {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqm : Measurable q₀)
    (hq0 : ∀ a, 0 ≤ q a) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n j : ℝ} (hn : 0 < n) (hjn : j ≠ 0) :
    (AddCircle.haarAddCircle.withDensity (fun a => ENNReal.ofReal (q a))).map
        (fun a => (((j+(j/n)*J a)/n : ℝ) : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hqi : Integrable q₀ := by
    rw [← circleDensityLift_eq hq₀ hq₀s]
    exact integrable_circleDensityLift hq o
  have hD : ∀ x ∈ I, HasDerivWithinAt J₀ (deriv J₀ x) I x :=
    fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
  have hmi := measurable_unfoldedModeDensity hJ hIo hinj hd hqm n j
  have hii := integrable_unfoldedModeDensity hIo.measurableSet
    (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet hD hinj
    (fun _ hx => hinj.leftInvOn_invFunOn hx) hd hqi hn hjn
  exact positive_density_map_of_vectorMeasure
    (AddCircle.measurable_mk'.comp ((measurable_const.add (hj.const_mul _)).div_const n))
    hq (integrable_foldCircleDensity hmi hii) hq0
    (foldCircleDensity_nonneg (unfoldedModeDensity_nonneg hq00 hn.le j))
    (foldedModeDensity_pushforward hq hqm hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn hjn)

lemma passage_speed_mode (J : UnitAddCircle → ℝ) (n : ℝ) (j : ℤ) (a : UnitAddCircle) :
    j • (((1+J a/n)/n : ℝ) : UnitAddCircle) =
      ((((j:ℝ)+((j:ℝ)/n)*J a)/n : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_zsmul]
  congr 1
  simp only [zsmul_eq_mul]
  ring

/-- Any coefficient with the actual retained modulus has the displayed
nonnegative folded density under the actual new twist. -/
lemma packetSpectralMeasure_new_speed {q : UnitAddCircle → ℝ} {q₀ J₀ : ℝ → ℝ}
    {J : UnitAddCircle → ℝ} {o : ℝ} {I : Set ℝ}
    {B : UnitAddCircle × UnitAddCircle → ℂ}
    (hq : Integrable q AddCircle.haarAddCircle) (hqmeas : Measurable q) (hqm : Measurable q₀)
    (hB : ∀ p, ‖B p‖^2 = q p.1) (hq00 : ∀ x, 0 ≤ q₀ x)
    (hq₀ : ∀ x ∈ Ioc o (o+1), q (x : UnitAddCircle) = q₀ x)
    (hq₀s : support q₀ ⊆ Ioc o (o+1)) (hqs : support q₀ ⊆ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x : UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℝ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j B =
      AddCircle.haarAddCircle.withDensity
        (fun z => ENNReal.ofReal
          (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀) q₀ n j) z)) := by
  have hσ : Measurable (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp ((measurable_const.add (hj.div_const n)).div_const n)
  rw [packetSpectralMeasure_of_modulus hσ hqmeas hB]
  simp_rw [passage_speed_mode]
  exact positive_foldedModeDensity_pushforward hq hqm
    (fun a => (hB (a,0)) ▸ sq_nonneg _) hq00 hq₀ hq₀s hqs hj hJ hJe hIo hinj hd hn
    (by exact_mod_cast hjn)

/-- Density identity for the literal retained coefficient used by the passage.
The only support hypothesis is that the cutoff lies on the chosen good branch. -/
lemma retainedAmplitude_spectralDensity
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {o : ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hψs : ∀ x ∈ Ioc o (o+1), ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Measurable J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℕ} {j : ℤ} (hn : 0 < n) (hjn : j ≠ 0) :
    packetSpectralMeasure (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) j
      (retainedAmplitude ψ χ m H A n j) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
        (foldCircleDensity (unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) z)) := by
  let C n j := exactPassageCoeff m (H n) A j
  let q := retainedCircleWeight ψ χ C n j
  have hC n j : Continuous (C n j) := continuous_exactPassageCoeff (hH n) hA j
  have hq : Continuous q :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hC n j).norm.pow 2)
  have hqs : support (circleDensityLift o q) ⊆ Ioc o (o+1) ∩ I := by
    intro x hx
    have hxI : x ∈ Ioc o (o+1) := by
      by_contra hh
      exact hx (by simp [circleDensityLift,hh])
    refine ⟨hxI,hψs x hxI ?_⟩
    intro hz
    exact hx (by simp [circleDensityLift,hxI,q,retainedCircleWeight,hz])
  exact packetSpectralMeasure_new_speed
    (retainedCircleWeight_integrable hψ hχ hC n j) hq.measurable
    (measurable_circleDensityLift hq.measurable o)
    (retainedAmplitude_norm_sq ψ χ m H A n j)
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ C n j) o)
    (fun _ hx => by simp only [circleDensityLift,indicator_of_mem hx]; rfl)
    (hqs.trans inter_subset_left) (hqs.trans inter_subset_right)
    hj hJ hJe hIo hinj hd (by exact_mod_cast hn) hjn

lemma packet_twisted_pair_zero {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : Continuous A) (hB : Continuous B)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ) {m k : ℤ}
    (hdisj : m = k → Disjoint (support A) (support B)) (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B (twistIter φ n x)
      ∂tripleVolume) = 0 := by
  let B' : UnitAddCircle × UnitAddCircle → ℂ := fun p => fourier n (k • φ p.1)*B p
  have hb' : Continuous B' :=
    ((fourier n).continuous.comp ((hφ.comp continuous_fst).const_smul k)).mul hB
  have he (x : TripleTorus) : packet k B (twistIter φ n x) = packet k B' x := by
    rw [packet_twistIter]
    dsimp [packet,B']
    ring
  simp_rw [he]
  rw [integral_packet_pair hA hb']
  split_ifs with hmk
  · apply integral_eq_zero_of_ae
    filter_upwards [] with p
    by_cases ha : A p = 0
    · simp [ha]
    · have hb : B p = 0 := by
        by_contra hh
        exact Set.disjoint_left.mp (hdisj hmk) ha hh
      simp [B',hb]
  · rfl

/-- The spectral measure of a smooth disjoint packet list is the sum of the
literal packet pushforwards, demonstrated by every bilateral Fourier moment. -/
lemma disjoint_packet_list_correlation {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (hA : ∀ i, Continuous (A i)) {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (hd : ∀ i j, i ≠ j → m i = m j → Disjoint (support (A i)) (support (A j)))
    (n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (∑ i, packet (m i) (A i) x)*
        (∑ i, packet (m i) (A i) (twistIter φ n x)) ∂tripleVolume) =
      ∑ i, ∫ z, fourier n z ∂packetSpectralMeasure φ (m i) (A i) := by
  classical
  have ht : Continuous (twistIter φ n) :=
    (continuous_fst.add ((hφ.comp (continuous_fst.comp continuous_snd)).const_smul n)).prodMk
      continuous_snd
  have hc (i j : ι) : Continuous (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) :=
    (Complex.continuous_conj.comp (continuous_packet (hA i))).mul
      ((continuous_packet (hA j)).comp ht)
  have hi (i j : ι) : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet (m i) (A i) x)*packet (m j) (A j) (twistIter φ n x)) tripleVolume :=
    (hc i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j),Finset.sum_eq_single i]
  · exact (packet_spectral_moment hφ (hA i) (m i) n).symm
  · intro j _ hji
    exact packet_twisted_pair_zero (hA i) (hA j) hφ (hd i j hji.symm) n
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end ThreeTorus
end
end
end
end
end
end

section

/-! Exact spectral identity for the literal retained packet vector. This closes
 the interface between the previously proved coefficient-density estimates and
 the actual Koopman correlations, without an abstract density hypothesis. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma foldCircleDensity_add_ae {q r : ℝ → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqi : Integrable q) (hri : Integrable r) :
    foldCircleDensity (fun x => q x+r x) =ᵐ[AddCircle.haarAddCircle]
      fun z => foldCircleDensity q z+foldCircleDensity r z := by
  apply (integrable_foldCircleDensity (hq.add hr) (hqi.add hri)).ae_eq_of_withDensityᵥ_eq
    ((integrable_foldCircleDensity hq hqi).add (integrable_foldCircleDensity hr hri))
  rw [← foldCircleDensity_pushforward (hq.add hr) (hqi.add hri),
    withDensityᵥ_add hqi hri,
    withDensityᵥ_add (integrable_foldCircleDensity hq hqi) (integrable_foldCircleDensity hr hri)]
  have he := map_add (VectorMeasure.mapGm (fun x : ℝ => (x:UnitAddCircle)))
    (volume.withDensityᵥ q) (volume.withDensityᵥ r)
  change (volume.withDensityᵥ q+volume.withDensityᵥ r).map _ =
    (volume.withDensityᵥ q).map _+(volume.withDensityᵥ r).map _ at he
  rw [he,foldCircleDensity_pushforward hq hqi,foldCircleDensity_pushforward hr hri]

lemma foldCircleDensity_finsetSum_ae {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, Measurable (q i)) (hqi : ∀ i ∈ S, Integrable (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =ᵐ[AddCircle.haarAddCircle]
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [] with z
    simp [foldCircleDensity,periodizedReal,AddCircle.liftIoc,Set.domRestrict]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    have hh := foldCircleDensity_add_ae (hq i (Finset.mem_insert_self i S))
      (Finset.measurable_sum S (fun j hj => hq j (Finset.mem_insert_of_mem hj)))
      (hqi i (Finset.mem_insert_self i S))
      (integrable_finsetSum S (fun j hj => hqi j (Finset.mem_insert_of_mem hj)))
    have ht := ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))
      (fun j hj => hqi j (Finset.mem_insert_of_mem hj))
    filter_upwards [hh,ht] with z hz ht
    rw [hz,ht]

lemma moment_withDensity_real {p : UnitAddCircle → ℝ} (hp : Measurable p)
    (hp0 : ∀ z, 0 ≤ p z) (v : UnitAddCircle → ℂ) :
    (∫ z, v z ∂AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z))) =
      ∫ z, (p z:ℂ)*v z ∂AddCircle.haarAddCircle := by
  rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
    (by filter_upwards [] with z; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (hp0 z),Complex.real_smul]

lemma continuous_retainedAmplitude
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A) (n : ℕ) (j : ℤ) :
    Continuous (retainedAmplitude ψ χ m H A n j) := by
  unfold retainedAmplitude
  exact ((((Complex.continuous_ofReal.comp hψ).comp continuous_fst).mul
    (Complex.continuous_ofReal.comp (hχ.comp (continuous_const.prodMk continuous_fst)))).mul
    ((continuous_exactPassageCoeff (hH n) hA j).comp continuous_fst)).mul
      ((fourier m).continuous.comp continuous_snd)

/-- All bilateral Koopman moments of the actual finite retained vector are
exactly those of its explicit nonnegative folded coefficient density. -/
theorem retainedPassage_spectral_moment
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hψs : ∀ x ∈ Ioc (0:ℝ) 1, ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Continuous J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    {n : ℕ} {S : Finset ℤ} (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) (k : ℤ) :
    let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
    let f := retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ
    (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
      ∫ z, (exactRetainedPacketDensity I J₀ ψ χ m H A S n z:ℂ)*fourier k z
        ∂AddCircle.haarAddCircle := by
  classical
  dsimp only
  let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
  let B := retainedAmplitude ψ χ m H A n
  let q := fun j : ℤ => unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
    (circleDensityLift 0 (retainedCircleWeight ψ χ
      (fun n j => exactPassageCoeff m (H n) A j) n j)) n j
  have hφ : Continuous φ :=
    (AddCircle.continuous_mk' 1).comp ((continuous_const.add (hj.div_const n)).div_const n)
  have hB j : Continuous (B j) := continuous_retainedAmplitude hψ hχ hH hA n j
  have hreg j (hjS : j ∈ S) := retained_unfolded_regular hJ hIo hinj hd hψ hχ
    (fun n j => continuous_exactPassageCoeff (m := m) (hH n) hA j) 0 hn (hS j hjS)
  have hqm j (hjS : j ∈ S) : Measurable (q j) := (hreg j hjS).1
  have hqi j (hjS : j ∈ S) : Integrable (q j) := (hreg j hjS).2
  have hq0 j : ∀ t, 0 ≤ q j t :=
    unfoldedModeDensity_nonneg (circleDensityLift_nonneg
      (retainedCircleWeight_nonneg ψ χ _ n j) 0) (Nat.cast_nonneg n) j
  have hds j (hjS : j ∈ S) : packetSpectralMeasure φ j (B j) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (foldCircleDensity (q j) z)) :=
    retainedAmplitude_spectralDensity hψ hχ hH hA (by simpa using hψs) hj.measurable
      hJ hJe hIo hinj hd hn (hS j hjS)
  have hfold := foldCircleDensity_finsetSum_ae S q hqm hqi
  have hint j (hjS : j ∈ S) : Integrable
      (fun z => (foldCircleDensity (q j) z:ℂ)*fourier k z) AddCircle.haarAddCircle :=
    (integrable_foldCircleDensity (hqm j hjS) (hqi j hjS)).ofReal.mul_bdd
      (fourier k).continuous.aestronglyMeasurable
      (ae_of_all _ (fun z => le_of_eq (Circle.norm_coe _)))
  have hc := disjoint_packet_list_correlation (fun j : S => (j:ℤ))
    (fun j : S => B j) (fun j => hB j) hφ
    (fun i j hij he => (hij (Subtype.ext he)).elim) k
  have hsum (x : TripleTorus) : (∑ j : S, packet (j:ℤ) (B j) x) =
      ∑ j ∈ S, packet j (B j) x := Finset.sum_coe_sort S (fun j => packet j (B j) x)
  simp_rw [hsum] at hc
  rw [Finset.sum_coe_sort S (fun j => ∫ z, fourier k z ∂packetSpectralMeasure φ j (B j))] at hc
  simp only [retainedPassage_eq_sum_packets]
  change (∫ x : TripleTorus, starRingEnd ℂ (∑ j ∈ S, packet j (B j) x)*
      (∑ j ∈ S, packet j (B j) (twistIter φ k x)) ∂tripleVolume) = _
  rw [hc]
  calc
    _ = ∑ j ∈ S, ∫ z, (foldCircleDensity (q j) z:ℂ)*fourier k z
        ∂AddCircle.haarAddCircle := by
      apply Finset.sum_congr rfl
      intro j hjS
      rw [hds j hjS]
      exact moment_withDensity_real (measurable_foldCircleDensity (hqm j hjS))
        (foldCircleDensity_nonneg (hq0 j)) (fourier k)
    _ = ∫ z, (∑ j ∈ S, (foldCircleDensity (q j) z:ℂ))*fourier k z
        ∂AddCircle.haarAddCircle := by
      simp_rw [Finset.sum_mul]
      exact (integral_finsetSum _ hint).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hfold] with z hz
      change (∑ j ∈ S, (foldCircleDensity (q j) z:ℂ))*fourier k z =
        (foldCircleDensity (fun t => ∑ j ∈ S, q j t) z:ℂ)*fourier k z
      rw [hz,Complex.ofReal_sum]

end ThreeTorus
end
end

section

/-! Smoothness at the edge of the good arc is essential: the actual retained
spectral densities must be valid smooth inputs to the next stage. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma support_branchDensity_subset {J q : ℝ → ℝ} {I : Set ℝ} :
    support (branchDensity I J (invFunOn J I) (deriv J) q) ⊆ J '' tsupport q := by
  intro y hy
  have hyI : y ∈ J '' I := by
    by_contra hh
    exact hy (by simp [branchDensity,hh])
  have hx := invFunOn_pos hyI
  refine ⟨invFunOn J I y,subset_tsupport q ?_,hx.2⟩
  intro hq
  exact hy (by simp [branchDensity,hyI,hq])

lemma branchDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hq : HasCompactSupport q) :
    HasCompactSupport (branchDensity I J (invFunOn J I) (deriv J) q) := by
  apply HasCompactSupport.intro (hq.image hJ)
  intro y hy
  exact notMem_support.mp (fun hh => hy (support_branchDensity_subset hh))

lemma branchDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let g := invFunOn J I
  have hM : IsCompact (J '' tsupport q) := hc.image hJ.continuous
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ J '' tsupport q
  · obtain ⟨x,hx,rfl⟩ := hy
    have hxI := hs hx
    have hyI : J x ∈ J '' I := mem_image_of_mem J hxI
    have hg := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := hinj (invFunOn_pos hyI).1 hxI (invFunOn_pos hyI).2
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => |deriv J (g y)|) (J x) :=
      (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x)
        (hD.contDiffAt.comp (J x) hg)
    have hquot := (hq.contDiffAt.comp (J x) hg).div hden
      (by simpa only [hge] using abs_ne_zero.mpr (hd x hxI))
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hyI] with z hz
    simp only [branchDensity,indicator_of_mem hz,g]
    rfl
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hy] with z hz
    exact notMem_support.mp (fun hh => hz (support_branchDensity_subset hh))

lemma unfoldedModeDensity_smooth {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q)
    (hs : tsupport q ⊆ I) (n j : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hmul : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => n*q x) := contDiff_const.mul hq
  have hcs : HasCompactSupport (fun x => n*q x) := hc.mul_left
  have hs' : tsupport (fun x => n*q x) ⊆ I := tsupport_mul_subset_right.trans hs
  have hh := branchDensity_smooth hJ hIo hinj hd hmul hcs hs' 
  unfold unfoldedModeDensity scaledBranchKernel
  exact contDiff_const.mul (hh.comp ((contDiff_const.mul contDiff_id).sub contDiff_const |>.div_const _))

lemma unfoldedModeDensity_compact {J q : ℝ → ℝ} {I : Set ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport q) {n j : ℝ} (hn : n ≠ 0) (hj : j ≠ 0) :
    HasCompactSupport (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hh := branchDensity_compact (I := I) hJ (hc.mul_left (f := fun _ => n))
  let e : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ n hn).trans (Homeomorph.addRight (-j))
  let e' : ℝ ≃ₜ ℝ := e.trans (Homeomorph.mulRight₀ (n/j) (div_ne_zero hn hj))
  have he (t : ℝ) : e' t = (n*t-j)/(j/n) := by
    dsimp [e',e]
    field_simp
    ring
  have hc' := hh.comp_homeomorph e'
  have heq : unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j =
      fun t => |j/n|⁻¹ * branchDensity I J (invFunOn J I) (deriv J) (fun x => n*q x) (e' t) := by
    funext t
    rw [he]
    rfl
  rw [heq]
  exact hc'.mul_left

lemma periodizedReal_eq_periodize {q : ℝ → ℝ} (hc : HasCompactSupport q) :
    periodizedReal q = periodize q := by
  funext x
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|x|+1)
  have hs : support (fun k : ℤ => q (x+k)) ⊆ (Finset.Icc (-(N:ℤ)) N : Set ℤ) := by
    intro k hk
    have hr := hR (x+k) (subset_tsupport q hk)
    have hh : |(k:ℝ)| < N := by
      have ha := abs_sub_le (x+(k:ℝ)) 0 x
      simp only [sub_zero,zero_sub,abs_neg,add_sub_cancel_left,Real.norm_eq_abs] at hr ha
      linarith
    have hab := abs_lt.mp hh
    simp only [Finset.mem_coe,Finset.mem_Icc]
    constructor
    · exact_mod_cast (by linarith : -(N:ℝ) ≤ (k:ℝ))
    · exact_mod_cast (by linarith : (k:ℝ) ≤ (N:ℝ))
  exact tsum_eq_finsum ((Finset.finite_toSet _).subset hs)

lemma foldCircleDensity_smooth_lift {q : ℝ → ℝ}
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q) (hc : HasCompactSupport q) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) := by
  have he : (fun x : ℝ => foldCircleDensity q (x:UnitAddCircle)) = periodize q := by
    funext x
    rw [foldCircleDensity_coe_all]
    exact congrFun (periodizedReal_eq_periodize hc) x
  rw [he]
  exact contDiff_periodize hq hc

lemma realRetainedWeight_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    tsupport (realRetainedWeight ψ₀ χ m H A n j) ⊆ tsupport ψ₀ := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp [realRetainedWeight,hz])

lemma realRetainedWeight_compact {ψ₀ : ℝ → ℝ} (hc : HasCompactSupport ψ₀)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) :
    HasCompactSupport (realRetainedWeight ψ₀ χ m H A n j) :=
  hc.of_isClosed_subset isClosed_closure (realRetainedWeight_support ψ₀ χ m H A n j)

lemma realRetainedWeight_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (realRetainedWeight ψ₀ χ m H A n j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => χ ((j:ℝ)/n) x) := hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((hψ.pow 2).mul (hχ'.pow 2)).mul
    ((smooth_exactPassageCoeff (hHl n) (hH n) hA j).norm_sq (𝕜 := ℂ))

lemma retainedWeight_lift_eq {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1)) :
    circleDensityLift 0 (retainedCircleWeight ψ χ
      (fun n j => exactPassageCoeff m (H n) A j) n j) =
      realRetainedWeight ψ₀ χ m H A n j := by
  apply circleDensityLift_eq
  · intro x hx
    simp only [retainedCircleWeight,realRetainedWeight,he x hx]
  · exact (subset_tsupport _).trans ((realRetainedWeight_support ψ₀ χ m H A n j).trans hs)

/-- Actual retained densities are smooth at all branch edges, including their
zero set. This supplies the next passage's regularity; it is not an assumption
that the density is already smooth. -/
theorem exactRetainedPacketDensity_smooth_lift
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => exactRetainedPacketDensity I J ψ χ m H A S n x) := by
  unfold exactRetainedPacketDensity
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_smooth_lift
  · apply ContDiff.sum
    intro j hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · have hh (j : ℤ) (hj : j ∈ S) : HasCompactSupport
        (unfoldedModeDensity I J (invFunOn J I) (deriv J)
          (realRetainedWeight ψ₀ χ m H A n j) n j) :=
      unfoldedModeDensity_compact hJ.continuous
        (realRetainedWeight_compact hc χ m H A n j)
        (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)
    convert HasCompactSupport.finset_sum hh using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | (funext time; simp only [Finset.sum_apply])

end ThreeTorus
end
end

section

/-! Quantitative physical and spectral conclusions for the same actual packet.
This is the analytic (not yet geometric finite-stage) transmission boundary. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

lemma sq_norm_sub_le_two (x y z : ℂ) :
    ‖x-z‖^2 ≤ 2*‖x-y‖^2+2*‖y-z‖^2 := by
  have hh : ‖x-z‖ ≤ ‖x-y‖+‖y-z‖ := by
    convert norm_add_le (x-y) (y-z) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have h0 := norm_nonneg (x-z)
  have h1 := norm_nonneg (x-y)
  have h2 := norm_nonneg (y-z)
  nlinarith [sq_nonneg (‖x-y‖-‖y-z‖)]

lemma continuous_passageChart {H : UnitAddCircle → UnitAddCircle} (hH : Continuous H) :
    Continuous (passageChart H) := by
  change Continuous (fun x : TripleTorus => (x.2.1,x.2.2,x.1+(-H x.2.1)))
  exact continuous_snd.fst.prodMk (continuous_snd.snd.prodMk
    (continuous_fst.add (hH.comp continuous_snd.fst).neg))

lemma continuous_retainedPassage {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A) (n : ℕ) (S : Finset ℤ) :
    Continuous (retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ) := by
  change Continuous (fun x => ∑ j ∈ S, packet j (retainedAmplitude ψ χ m H A n j) x)
  exact continuous_finsetSum _ (fun j _ => continuous_packet
    (continuous_retainedAmplitude hψ hχ hH hA n j))

lemma cutoff_packet_error_eq {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖) (ψ : UnitAddCircle → ℝ) (m : ℤ) :
    (∫ x : TripleTorus, ‖packet m A x-(ψ x.2.2:ℂ)*packet m A x‖^2 ∂tripleVolume) =
      (∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)*
      (∫ a, (1-ψ a)^2 ∂AddCircle.haarAddCircle) := by
  have he (x : TripleTorus) : ‖packet m A x-(ψ x.2.2:ℂ)*packet m A x‖^2 =
      ‖A (x.2.1,0)‖^2*(1-ψ x.2.2)^2 := by
    rw [show packet m A x-(ψ x.2.2:ℂ)*packet m A x =
      (1-(ψ x.2.2:ℂ))*packet m A x by ring]
    simp only [packet,norm_mul,fourier_apply,Circle.norm_coe,mul_one]
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      mul_pow,sq_abs,hmod]
    ring
  simp_rw [he]
  change (∫ x : UnitAddCircle × (UnitAddCircle × UnitAddCircle),
    ‖A (x.2.1,0)‖^2*(1-ψ x.2.2)^2 ∂AddCircle.haarAddCircle.prod slowVolume) = _
  rw [integral_fun_snd (μ := AddCircle.haarAddCircle) (ν := slowVolume)
    (fun p : UnitAddCircle × UnitAddCircle => ‖A (p.1,0)‖^2*(1-ψ p.2)^2)]
  simpa only [probReal_univ,one_smul] using
    (integral_prod_mul (μ := AddCircle.haarAddCircle) (ν := AddCircle.haarAddCircle)
      (fun u => ‖A (u,0)‖^2) (fun a => (1-ψ a)^2))

lemma cutoff_packet_error_le {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖) {δ : ℝ}
    (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) (m : ℤ) :
    (∫ x : TripleTorus,
      ‖packet m A x-(neutralCircleCutoff c x.2.2:ℂ)*packet m A x‖^2 ∂tripleVolume) ≤
      (∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)*(4*δ) := by
  rw [cutoff_packet_error_eq hmod]
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun _ => sq_nonneg _))
  have hc := continuous_neutralCircleCutoff c
  have hi : Integrable (fun a => (1-neutralCircleCutoff c a^2)) AddCircle.haarAddCircle :=
    (continuous_const.sub (hc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ a, (1-neutralCircleCutoff c a^2) ∂AddCircle.haarAddCircle := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _)) hi
      exact ae_of_all _ (fun a => by
        have h := neutralCircleCutoff_bounds c hδ a
        nlinarith)
    _ ≤ _ := neutralCircleCutoff_error c hδ hδ'

/-- Removing the good-arc cutoff adds no assumed physical approximation.
Its missing mass is explicitly paid. -/
lemma uncut_retainedPassage_error_le
    {A : UnitAddCircle × UnitAddCircle → ℂ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {χ : ℝ → UnitAddCircle → ℝ}
    (hA : Continuous A) (hH : ∀ n, Continuous (H n)) (hχ : Continuous χ.uncurry)
    (hmod : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖) {δ : ℝ}
    (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8) (n : ℕ) (S : Finset ℤ) :
    (∫ x : TripleTorus,
      ‖packet m A x-retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
        (neutralCircleCutoff c) (passageChart (H n) x)‖^2 ∂tripleVolume) ≤
      8*δ*(∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)+
      2*(∫ x : TripleTorus,
      ‖(neutralCircleCutoff c x.2.2:ℂ)*packet m A x-
        retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
          (neutralCircleCutoff c) (passageChart (H n) x)‖^2 ∂tripleVolume) := by
  let f := packet m A
  let g := fun x : TripleTorus => (neutralCircleCutoff c x.2.2:ℂ)*f x
  let h := fun x : TripleTorus => retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n))
    (neutralCircleCutoff c) (passageChart (H n) x)
  have hf : Continuous f := continuous_packet hA
  have hg : Continuous g := (Complex.continuous_ofReal.comp
    ((continuous_neutralCircleCutoff c).comp continuous_snd.snd)).mul hf
  have hh : Continuous h :=
    (continuous_retainedPassage (continuous_neutralCircleCutoff c) hχ hH hA n S).comp
      (continuous_passageChart (hH n))
  have hi (v w : TripleTorus → ℂ) (hv : Continuous v) (hw : Continuous w) :
      Integrable (fun x => ‖v x-w x‖^2) tripleVolume :=
    ((hv.sub hw).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfg := hi f g hf hg
  have hgh := hi g h hg hh
  calc
    _ ≤ ∫ x, (2*‖f x-g x‖^2+2*‖g x-h x‖^2) ∂tripleVolume := by
      apply integral_mono (hi f h hf hh) ((hfg.const_mul 2).add (hgh.const_mul 2))
      intro x
      exact sq_norm_sub_le_two (f x) (g x) (h x)
    _ = 2*(∫ x, ‖f x-g x‖^2 ∂tripleVolume)+2*(∫ x, ‖g x-h x‖^2 ∂tripleVolume) := by
      rw [integral_add (hfg.const_mul 2) (hgh.const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by
      have hh := cutoff_packet_error_le hmod c hδ hδ' m
      change (∫ x, ‖f x-g x‖^2 ∂tripleVolume) ≤ _ at hh
      dsimp only [g,h]
      nlinarith

/-- A single actual quantile passage simultaneously satisfies the physical,
spectral, smoothness and all bilateral-moment conclusions. The passage integer
remains arbitrarily large after the law, cutoffs and amplitudes are fixed. -/
theorem exact_quantile_passage_oai
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    (hmod : ∀ a x, ‖A₀ a x‖ = ‖A₀ 0 x‖)
    (hmodA : ∀ u a, ‖A (u,a)‖ = ‖A (u,0)‖)
    (hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχs : CylinderSmooth χ.uncurry)
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {g : UnitAddCircle → ℝ} (hg : Continuous g) {ε : ℝ}
    (hideal : ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g y| ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ 0)
    ∃ S : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ S n, j ≠ 0) ∧
      (∀ n, 0 < n → ∀ j ∉ S n, ∀ a, χ ((j:ℝ)/n) a = 0) ∧
      ∀ᶠ n : ℕ in atTop,
        let ψ := neutralCircleCutoff c
        let J := quantileCircleJitter ρ c
        let φ := fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)
        let f := retainedPassage m (H n) A (S n) (fun j => χ ((j:ℝ)/n)) ψ
        let p := exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ c) ψ χ m H A (S n) n
        (∫ x : TripleTorus, ‖packet m A x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
          8*δ*(∫ u, ‖A (u,0)‖^2 ∂AddCircle.haarAddCircle)+η ∧
        (∫ z, |p z-foldCircleDensity w z*g ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
          (∫ s, w s)*(4*δ+ε)+η ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
        (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter φ k x) ∂tripleVolume) =
          ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
        (∀ j u a, ‖retainedAmplitude ψ χ m H A n j (u,a)‖ =
          ‖retainedAmplitude ψ χ m H A n j (u,0)‖) := by
  dsimp only
  obtain ⟨S,hSN,hST,hsp⟩ := exact_quantile_circle_spectral_estimate hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt hmod
    hρ hi hp hρm hC hb hF c hδ hδ' hχc hcχ hzχ hχ hχW hg hideal hη
  refine ⟨S,hSN,hST,?_⟩
  have hψc := continuous_neutralCircleCutoff c
  have hph := exact_physical_retainedPassage_tendsto hm hH hA hA₀ hAc hAd hsupp
    hlo huo hlu hR hPr hV hPV hdV hHc hAcont hΔt hχc hχ
    (neutralCircleCutoff c) hψc (neutralCircleCutoff_bounds c hδ) hχW S hST
  have hJs := lawJitter_smooth c hρ hi hp hρm
  have hJinj := lawJitter_injOn c hρ.continuous hi hp hρm hδ
  have hJd : ∀ x ∈ Ioo δ (1-δ), deriv (lawJitter ρ c) x ≠ 0 := by
    intro x hx
    obtain ⟨hd,hdp⟩ := lawJitter_deriv_pos c hρ hi hp hρm hδ hx
    rw [hd.deriv]
    exact hdp.ne'
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff c (x:UnitAddCircle) = c.ψ x := by
    intro x hx
    exact lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩
  have hψsupport : ∀ x ∈ Ioc (0:ℝ) 1,
      neutralCircleCutoff c (x:UnitAddCircle) ≠ 0 → x ∈ Ioo δ (1-δ) := by
    intro x hx hn
    rw [heψ x (by simpa using hx)] at hn
    exact (hψs (subset_tsupport c.ψ hn)).2
  have hHl : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (n:ℝ)*(Pr x+Δ n*x)) :=
    fun _ => contDiff_const.mul (hPr.add (contDiff_const.mul contDiff_id))
  filter_upwards [hsp,hph.eventually (eventually_lt_nhds (half_pos hη)),
    eventually_gt_atTop (0:ℕ)] with n hnsp hnph hn
  refine ⟨?_,hnsp,?_,?_,?_⟩
  · have hh := uncut_retainedPassage_error_le (m := m) hAcont hHc hχc hmodA c hδ hδ' n (S n)
    exact hh.trans_lt (by linarith)
  · exact exactRetainedPacketDensity_smooth_lift hJs isOpen_Ioo hJinj hJd
      c.ψ_smooth c.ψ_compact heψ hψs hχs hHl hH hAs hn (hSN n hn)
  · intro k
    exact retainedPassage_spectral_moment hψc hχc hHc hAcont hψsupport
      (continuous_quantileCircleJitter c hρ hi hp hρm) hJs
      (fun x _ => quantileCircleJitter_coe ρ c x) isOpen_Ioo hJinj hJd hn (hSN n hn) k
  · exact fun _ _ _ => retainedAmplitude_modulus _ _ _ _ _ _ _ _ _

end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exact_quantile_passage_oai := @OAI.ThreeTorus.exact_quantile_passage_oai
