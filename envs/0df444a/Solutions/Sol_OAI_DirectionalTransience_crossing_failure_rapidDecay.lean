-- Prove2me | solution 1 for OAI.DirectionalTransience.crossing_failure_rapidDecay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:41.874744+00:00
-- url     : https://prove2.me/submissions/0e3e59e7-63d8-4431-96fe-cbddd9997f07

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_stationary_array_law
import Theorems.Thm_OAI_DirectionalTransience_actual_profile_tail_decorrelation
import Theorems.Thm_OAI_DirectionalTransience_operational_constants_exist
import Theorems.Thm_OAI_DirectionalTransience_spatial_confinement

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LowerClip
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma lowerClip_tendsto (x : ℝ) :
    Tendsto (fun n => lowerClip n x) atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (-x)
  have heq : (fun n => lowerClip n x) =ᶠ[atTop] (fun _ => x) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact max_eq_left (by linarith)
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

lemma lowerClip_sub_bound (n : ℕ) (x y g : ℝ) (hg : g ≤ y - x) :
    |min g (lowerClip n y - lowerClip n x)| ≤ |g| := by
  have hd : min g 0 ≤ lowerClip n y - lowerClip n x := by
    rcases le_total x (-(n : ℝ)) with hx | hx
    · rw [lowerClip, lowerClip, max_eq_right hx]
      have := le_max_right y (-(n : ℝ))
      have := min_le_right g 0
      linarith
    · rw [lowerClip, lowerClip, max_eq_left hx]
      have := le_max_left y (-(n : ℝ))
      have := min_le_left g 0
      linarith
  apply abs_le.mpr
  constructor
  · apply le_min
    · exact neg_abs_le g
    · exact (le_min (neg_abs_le g) (by simp)).trans hd
  · exact (min_le_left _ _).trans (le_abs_self g)

lemma integral_le_zero_of_identDistrib_lower_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {X Y G : α → ℝ} (hXY : IdentDistrib X Y μ μ)
    (hX : ∀ᵐ a ∂μ, X a ≤ 0) (hY : ∀ᵐ a ∂μ, Y a ≤ 0)
    (hG : Integrable G μ) (hlower : ∀ᵐ a ∂μ, G a ≤ Y a - X a) :
    ∫ a, G a ∂μ ≤ 0 := by
  let D : ℕ → α → ℝ := fun n a => lowerClip n (Y a) - lowerClip n (X a)
  let F : ℕ → α → ℝ := fun n a => min (G a) (D n a)
  have hclipmeas (n : ℕ) : Measurable (lowerClip n) :=
    measurable_id.max measurable_const
  have hclipint (Z : α → ℝ) (hZm : AEMeasurable Z μ)
      (hZ : ∀ᵐ a ∂μ, Z a ≤ 0) (n : ℕ) :
      Integrable (fun a => lowerClip n (Z a)) μ := by
    apply Integrable.of_bound ((hclipmeas n).comp_aemeasurable hZm).aestronglyMeasurable n
    filter_upwards [hZ] with a ha
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · exact le_max_right _ _
    · show max (Z a) (-(n : ℝ)) ≤ (n : ℝ)
      exact max_le (ha.trans (Nat.cast_nonneg n)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hDX (n : ℕ) := hclipint X hXY.aemeasurable_fst hX n
  have hDY (n : ℕ) := hclipint Y hXY.aemeasurable_snd hY n
  have hDint (n : ℕ) : Integrable (D n) μ := (hDY n).sub (hDX n)
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (hG.aemeasurable.min (hDint n).aemeasurable).aestronglyMeasurable
  have hFbound (n : ℕ) : ∀ᵐ a ∂μ, ‖F n a‖ ≤ |G a| := by
    filter_upwards [hlower] with a ha
    exact lowerClip_sub_bound n (X a) (Y a) (G a) ha
  have hFint (n : ℕ) : Integrable (F n) μ :=
    hG.abs.mono' (hFm n) (hFbound n)
  have hDzero (n : ℕ) : ∫ a, D n a ∂μ = 0 := by
    rw [show D n = (fun a => lowerClip n (Y a) - lowerClip n (X a)) from rfl,
      integral_sub (hDY n) (hDX n)]
    have hid := (hXY.comp (hclipmeas n)).integral_eq
    change (∫ a, lowerClip n (X a) ∂μ) = (∫ a, lowerClip n (Y a) ∂μ) at hid
    rw [hid, sub_self]
  have hFnonpos (n : ℕ) : ∫ a, F n a ∂μ ≤ 0 := by
    rw [← hDzero n]
    exact integral_mono_ae (hFint n) (hDint n) (Eventually.of_forall fun a => min_le_right _ _)
  have hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (G a)) := by
    filter_upwards [hlower] with a ha
    have hDlim := (lowerClip_tendsto (Y a)).sub (lowerClip_tendsto (X a))
    simpa only [min_eq_left ha] using (tendsto_const_nhds (x := G a)).min hDlim
  exact le_of_tendsto
    (tendsto_integral_of_dominated_convergence (fun a => |G a|) hFm hG.abs hFbound hlim)
    (Eventually.of_forall hFnonpos)

lemma prefixMax_nonneg (z : ℕ → ℝ) (n : ℕ) : 0 ≤ prefixMax z n := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma prefixMax_le_truncation (z : ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    prefixMax z n ≤ T + ∑ j ∈ Finset.range n, max (z j - T) 0 := by
  induction n with
  | zero => simpa [prefixMax] using hT
  | succ n ih =>
    rw [prefixMax, Finset.sum_range_succ]
    apply max_le
    · linarith [le_max_right (z n - T) 0]
    · have hsum : 0 ≤ ∑ j ∈ Finset.range n, max (z j - T) 0 :=
        Finset.sum_nonneg fun j _ => le_max_right _ _
      linarith [le_max_left (z n - T) 0]

lemma integrable_prefixMax
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Z : ℕ → α → ℝ} (hZ : ∀ j, Integrable (Z j) μ) (n : ℕ) :
    Integrable (fun a => prefixMax (fun j => Z j a) n) μ := by
  induction n with
  | zero => exact integrable_zero α ℝ μ
  | succ n ih => exact ih.sup (hZ n)

lemma integral_prefixMax_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {Z : ℕ → α → ℝ} (hZ : Integrable (Z 0) μ)
    (hid : ∀ j, IdentDistrib (Z j) (Z 0) μ μ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (∫ a, prefixMax (fun j => Z j a) n ∂μ) ≤
      T + n * ∫ a, max (Z 0 a - T) 0 ∂μ := by
  have hint (j : ℕ) : Integrable (Z j) μ := (hid j).integrable_iff.mpr hZ
  have htail (j : ℕ) : Integrable (fun a => max (Z j a - T) 0) μ :=
    ((hint j).sub (integrable_const _)).sup (integrable_const _)
  calc
    (∫ a, prefixMax (fun j => Z j a) n ∂μ)
        ≤ ∫ a, T + ∑ j ∈ Finset.range n, max (Z j a - T) 0 ∂μ := by
      apply integral_mono (integrable_prefixMax μ hint n)
        ((integrable_const T).add (integrable_finsetSum _ fun j _ => htail j))
      intro a
      exact prefixMax_le_truncation _ hT _
    _ = T + ∑ j ∈ Finset.range n, ∫ a, max (Z j a - T) 0 ∂μ := by
      rw [integral_add (integrable_const T)
        (integrable_finsetSum _ fun j _ => htail j), integral_const,
        integral_finsetSum _ fun j _ => htail j]
      simp
    _ = T + n * ∫ a, max (Z 0 a - T) 0 ∂μ := by
      congr 1
      have heq (j : ℕ) : (∫ a, max (Z j a - T) 0 ∂μ) =
          ∫ a, max (Z 0 a - T) 0 ∂μ :=
        ((hid j).comp ((measurable_id.sub_const T).max measurable_const)).integral_eq
      simp_rw [heq]
      simp

lemma integral_prefixMax_div_tendsto_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {Z : ℕ → α → ℝ} (hZ : Integrable (Z 0) μ)
    (hid : ∀ j, IdentDistrib (Z j) (Z 0) μ μ) :
    Tendsto (fun n : ℕ => (∫ a, prefixMax (fun j => Z j a) n ∂μ) / n)
      atTop (𝓝 0) := by
  have htail : Tendsto (fun T : ℕ => ∫ a, max (Z 0 a - T) 0 ∂μ) atTop (𝓝 0) := by
    have hbound (T : ℕ) : ∀ᵐ a ∂μ, ‖max (Z 0 a - T) 0‖ ≤ |Z 0 a| := by
      apply Eventually.of_forall
      intro a
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      apply max_le
      · linarith [le_abs_self (Z 0 a), Nat.cast_nonneg (α := ℝ) T]
      · exact abs_nonneg _
    have hlim : ∀ᵐ a ∂μ,
        Tendsto (fun T : ℕ => max (Z 0 a - T) 0) atTop (𝓝 0) := by
      apply Eventually.of_forall
      intro a
      obtain ⟨N, hN⟩ := exists_nat_ge (Z 0 a)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact (max_eq_right (by linarith)).symm
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun a => |Z 0 a|)
      (fun T => (hZ.aemeasurable.sub_const T |>.max aemeasurable_const).aestronglyMeasurable)
      hZ.abs hbound hlim
  have hnonneg (n : ℕ) : 0 ≤ (∫ a, prefixMax (fun j => Z j a) n ∂μ) / n :=
    div_nonneg (integral_nonneg fun a => prefixMax_nonneg _ _) (Nat.cast_nonneg _)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hnonneg n)
  · intro ε hε
    obtain ⟨T, hT⟩ := (htail.eventually (gt_mem_nhds (half_pos hε))).exists
    have hdiv : Tendsto (fun n : ℕ => (T : ℝ) / n) atTop (𝓝 0) :=
      tendsto_natCast_atTop_atTop.const_div_atTop _
    filter_upwards [hdiv.eventually (gt_mem_nhds (half_pos hε)),
      eventually_ge_atTop 1] with n hn hn1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hbd := div_le_div_of_nonneg_right
      (integral_prefixMax_le μ hZ hid (Nat.cast_nonneg T) n) hnpos.le
    rw [add_div, mul_div_cancel_left₀ _ hnpos.ne'] at hbd
    linarith

lemma le_prefixMax (z : ℕ → ℝ) {j n : ℕ} (hj : j < n) : z j ≤ prefixMax z n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · exact (ih h).trans (le_max_left _ _)
    · exact le_max_right _ _

lemma log_sum_le_log_add_prefixMax (h : ℕ → ℝ) (hh : ∀ j, 0 ≤ h j)
    {n : ℕ} (hn : 0 < n) :
    Real.log (1 + ∑ j ∈ Finset.range n, h j) ≤
      Real.log n + prefixMax (fun j => Real.log (1 + h j)) n := by
  let M := prefixMax (fun j => Real.log (1 + h j)) n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ j ∈ Finset.range n, h j := Finset.sum_nonneg fun j _ => hh j
  apply (Real.log_le_iff_le_exp (by linarith)).mpr
  rw [Real.exp_add, Real.exp_log hnR]
  have hterm : ∀ j ∈ Finset.range n, 1 + h j ≤ Real.exp M := by
    intro j hj
    exact (Real.log_le_iff_le_exp (by linarith [hh j])).mp
      (le_prefixMax (fun j => Real.log (1 + h j)) (Finset.mem_range.mp hj))
  have hbd := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hbd
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma integral_log_sum_div_tendsto_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {h : ℕ → α → ℝ} (hh : ∀ᵐ a ∂μ, ∀ j, 0 ≤ h j a)
    (hid : ∀ j, IdentDistrib (h j) (h 0) μ μ)
    (hint : Integrable (fun a => Real.log (1 + h 0 a)) μ) :
    Tendsto (fun n : ℕ => (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) / n)
      atTop (𝓝 0) := by
  let Z : ℕ → α → ℝ := fun j a => Real.log (1 + h j a)
  have hZid (j : ℕ) : IdentDistrib (Z j) (Z 0) μ μ :=
    (hid j).comp (Real.measurable_log.comp (measurable_const.add measurable_id))
  have hZint (j : ℕ) : Integrable (Z j) μ := (hZid j).integrable_iff.mpr hint
  have hnonneg (n : ℕ) :
      0 ≤ (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) / n := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply integral_nonneg_of_ae
    filter_upwards [hh] with a ha
    apply Real.log_nonneg
    have := Finset.sum_nonneg (s := Finset.range n) (fun j _ => ha j)
    linarith
  have hupper : ∀ᶠ n : ℕ in atTop,
      (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) / n ≤
        Real.log n / n + (∫ a, prefixMax (fun j => Z j a) n ∂μ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have hm : AEStronglyMeasurable
        (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
      (Real.measurable_log.comp_aemeasurable
        (aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun j _ => (hid j).aemeasurable_fst))).aestronglyMeasurable
    have hbd : ∀ᵐ a ∂μ,
        Real.log (1 + ∑ j ∈ Finset.range n, h j a) ≤
          Real.log n + prefixMax (fun j => Z j a) n := by
      filter_upwards [hh] with a ha
      exact log_sum_le_log_add_prefixMax _ ha hn0
    have hubint : Integrable (fun a => Real.log n + prefixMax (fun j => Z j a) n) μ :=
      (integrable_const _).add (integrable_prefixMax μ hZint n)
    have hsint : Integrable (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ := by
      apply hubint.mono' hm
      filter_upwards [hh, hbd] with a ha hb
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
        have := Finset.sum_nonneg (s := Finset.range n) (fun j _ => ha j)
        linarith))]
      exact hb
    have hbint := integral_mono_ae hsint hubint hbd
    rw [integral_add (integrable_const _) (integrable_prefixMax μ hZint n)] at hbint
    simp only [integral_const] at hbint
    simp at hbint
    have hd := div_le_div_of_nonneg_right hbint (Nat.cast_nonneg n)
    simpa only [add_div] using hd
  apply squeeze_zero' (Eventually.of_forall hnonneg) hupper
  have hlog : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa using hlog.add (integral_prefixMax_div_tendsto_zero μ hint hZid)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_CoordinateStrip
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma integrable_log_sum
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {h : ℕ → α → ℝ} (hh : ∀ᵐ a ∂μ, ∀ j, 0 ≤ h j a)
    (hm : ∀ j, AEMeasurable (h j) μ)
    (hint : ∀ j, Integrable (fun a => Real.log (1 + h j a)) μ) (n : ℕ) :
    Integrable (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  let Z : ℕ → α → ℝ := fun j a => Real.log (1 + h j a)
  have hup : Integrable (fun a => Real.log n + prefixMax (fun j => Z j a) n) μ :=
    (integrable_const _).add (integrable_prefixMax μ hint n)
  apply hup.mono'
    (Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add (Finset.aemeasurable_fun_sum _ fun j _ => hm j))).aestronglyMeasurable
  filter_upwards [hh] with a ha
  simp only [Function.comp_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
    have := Finset.sum_nonneg (s := Finset.range n) (fun j _ => ha j)
    linarith))]
  exact log_sum_le_log_add_prefixMax _ ha hn0

lemma stationary_tail_growth_obstruction
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {c h : ℕ → α → ℝ} {X : ℕ → ℕ → α → ℝ} {Z : ℕ → ℕ → α → ℝ}
    (hcint : Integrable (c 0) μ)
    (hcid : ∀ j, IdentDistrib (c j) (c 0) μ μ)
    (hh : ∀ᵐ a ∂μ, ∀ j, 0 ≤ h j a)
    (hhid : ∀ j, IdentDistrib (h j) (h 0) μ μ)
    (hhint : Integrable (fun a => Real.log (1 + h 0 a)) μ)
    (hXid : ∀ n R, IdentDistrib (X 0 R) (X n R) μ μ)
    (hXnonpos : ∀ n R, ∀ᵐ a ∂μ, X n R a ≤ 0)
    (hZint : ∀ n R, Integrable (Z n R) μ)
    (A C : ℝ)
    (hZmean : ∀ n, ∀ᶠ R : ℕ in atTop, (∫ a, Z n R a ∂μ) ≤ C)
    (hgrowth : ∀ n R, ∀ᵐ a ∂μ,
      (∑ j ∈ Finset.range n, c j a) -
        A * Real.log (1 + ∑ j ∈ Finset.range n, h j a) - Z n R a - Real.log 2 ≤
          X n R a - X 0 R a) :
    (∫ a, c 0 a ∂μ) ≤ 0 := by
  have hcj (j : ℕ) : Integrable (c j) μ := (hcid j).integrable_iff.mpr hcint
  have hhj (j : ℕ) : Integrable (fun a => Real.log (1 + h j a)) μ :=
    ((hhid j).comp (Real.measurable_log.comp (measurable_const.add measurable_id))).integrable_iff.mpr hhint
  have hsumint (n : ℕ) : Integrable (fun a => Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
    integrable_log_sum μ hh (fun j => (hhid j).aemeasurable_fst) hhj n
  have hbound (n : ℕ) : (n : ℝ) * (∫ a, c 0 a ∂μ) ≤
      A * (∫ a, Real.log (1 + ∑ j ∈ Finset.range n, h j a) ∂μ) + C + Real.log 2 := by
    obtain ⟨R, hR⟩ := (hZmean n).exists
    have hcs : Integrable (fun a => ∑ j ∈ Finset.range n, c j a) μ :=
      integrable_finsetSum _ (fun j _ => hcj j)
    have h1 : Integrable (fun a => (∑ j ∈ Finset.range n, c j a) -
        A * Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
      hcs.sub ((hsumint n).const_mul A)
    have h2 : Integrable (fun a => (∑ j ∈ Finset.range n, c j a) -
        A * Real.log (1 + ∑ j ∈ Finset.range n, h j a) - Z n R a) μ :=
      h1.sub (hZint n R)
    have h3 : Integrable (fun a => A * Real.log (1 + ∑ j ∈ Finset.range n, h j a)) μ :=
      (hsumint n).const_mul A
    have hG := h2.sub (integrable_const (Real.log 2))
    have hle := integral_le_zero_of_identDistrib_lower_bound μ (hXid n R)
      (hXnonpos 0 R) (hXnonpos n R) hG (hgrowth n R)
    simp only [Pi.sub_apply] at hle
    rw [integral_sub h2 (integrable_const (Real.log 2)),
      integral_sub h1 (hZint n R), integral_sub hcs h3, integral_const_mul,
      integral_finsetSum _ (fun j _ => hcj j)] at hle
    simp only [(hcid _).integral_eq, integral_const, probReal_univ, smul_eq_mul,
      one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    linarith
  have hlim :=
    ((integral_log_sum_div_tendsto_zero μ hh hhid hhint).const_mul A).add
      (tendsto_const_div_atTop_nhds_zero_nat (C + Real.log 2))
  simp only [mul_zero, add_zero] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← mul_div_assoc, ← add_div]
  apply (le_div_iff₀ hnpos).mpr
  nlinarith [hbound n]

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SignedCoordinate
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.annealedFrom_probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.fixedQuenchedKernel_markov _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.sharedPairKernel_markov _root_.OAI.DirectionalTransience.sharedPairLaw_probability _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma measurableSet_boundedHeightPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (n : ℕ) :
    MeasurableSet (BoundedHeightPrefix ℓ H n) := by
  simp only [BoundedHeightPrefix, Set.ofPred_forall, Set.ofPred_and]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
  have hh : Measurable (fun X : Path d => dot (realPosition (X j)) ℓ) := by unfold dot realPosition; fun_prop
  exact (measurableSet_le measurable_const hh).inter (measurableSet_le hh measurable_const)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PairPrefix
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma firstLayerHit_exists {d : ℕ} (h : Lattice d → ℤ)
    (hstep : ∀ x e, h (x+step e) ≤ h x+1) (X : Path d)
    (hnn : ∀ n, ∃ e, X (n+1) = X n+step e)
    (ht : Tendsto (fun n => (h (X n) : ℝ)) atTop atTop)
    (H : ℤ) (h0 : h (X 0) < H) : ∃ n, X ∈ FirstLayerHit h H n := by
  classical
  have hge : ∀ᶠ n : ℕ in atTop, (H : ℝ) ≤ (h (X n) : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  obtain ⟨k,hk⟩ := hge.exists
  have he : ∃ n, H ≤ h (X n) := ⟨k, by exact_mod_cast hk⟩
  let n := Nat.find he
  have hn : H ≤ h (X n) := Nat.find_spec he
  have hb : ∀ j < n, h (X j) < H := fun j hj => lt_of_not_ge (Nat.find_min he hj)
  have hn0 : 0 < n := by
    by_contra hh
    have hz : n = 0 := by omega
    rw [hz] at hn
    omega
  obtain ⟨e,he⟩ := hnn (n-1)
  have hprev := hb (n-1) (by omega)
  have hinc := hstep (X (n-1)) e
  rw [← he,show n-1+1 = n by omega] at hinc
  exact ⟨n,by omega,hb⟩

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BadCrossingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma badCrossingEvent_measurable {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ) :
    MeasurableSet (badCrossingEvent e N β) :=
  measurableSet_lt (measurable_crossingQuenched _ _ _).ennreal_toReal measurable_const

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossTranslation
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma cross_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    (fun X : Path d => fun n => X n-x) ⁻¹' Cross ℓ 0 H = Cross ℓ x H := by
  ext X
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  simp only [Cross,Set.mem_preimage,Set.mem_ofPred_eq,hzero,zero_add,dot_realPosition_sub]
  constructor
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SurvivingLane
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma hitKernel_ae_target {d : ℕ} (S V : Set (Lattice d)) (z : State d) :
    ∀ᵐ y ∂hitKernel S V z, y ∈ V := by
  apply ae_iff.mpr
  rw [hitKernel_apply]
  have he : V ∩ {a | a ∉ V} = ∅ := by ext a; simp
  rw [he]
  simp only [HitAt,Set.mem_empty_iff_false,false_and,Set.ofPred_false,measure_empty,tsum_zero]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_FirstLayerHitRecordIndexTime
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma noDrop_firstLayerHit_exists {d : ℕ} (e : Direction d) (X : Path d)
    (h0 : X 0 = 0) (hnn : ∀ n, ∃ f, X (n+1) = X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e))) {k : ℕ} (hk : 0 < k) :
    ∃ n, X ∈ FirstLayerHit (signedHeight e) k n := by
  apply firstLayerHit_exists (signedHeight e) (signedHeight_step_le e) X hnn
  · simpa only [TransientPaths,Set.mem_ofPred_eq,signedHeight_projection] using ht
  · rw [h0]
    simp only [signedHeight,Pi.zero_apply,ite_self,neg_zero]
    exact_mod_cast hk

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicy
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma crossingQuenched_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℝ) (ω : Environment d) :
    crossingQuenched ℓ x H ω = crossingQuenched ℓ 0 H (fun y => ω (x+y)) := by
  have hm : Measurable (fun X : Path d => fun j => X j-x) := by fun_prop
  have he := congrArg (fun μ : Measure (Path d) => μ (Cross ℓ 0 H)) (quenched_translation ω x 0)
  rw [Measure.map_apply hm (measurableSet_cross _ _ _),cross_translation] at he
  simpa only [add_zero,crossingQuenched] using he

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_UpperKernel
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma upperHorizontalKernel_mass_le_one {d : ℕ} (e : Direction d) (H : ℕ) (ξ : UpperRows e)
    (z : HorizontalSpace e) : upperHorizontalKernel e H ξ z Set.univ ≤ 1 := by
  rw [upperHorizontalKernel_apply,Set.preimage_univ]
  exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_StationaryGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DirectionalTransience

lemma orbitAverage_measurable {Ω : Type*} [MeasurableSpace Ω] (T : Ω → Ω) (hT : Measurable T)
    (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) : Measurable (orbitAverage T f n) := by
  unfold orbitAverage
  fun_prop

lemma orbitAverage_bounds {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ)
    (hf : ∀ ω, f ω∈Set.Icc 0 1) (n : ℕ) (ω : Ω) : orbitAverage T f n ω∈Set.Icc 0 1 := by
  refine ⟨mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (Finset.sum_nonneg fun i _ => (hf _).1),?_⟩
  by_cases hn : n=0
  · simp [orbitAverage,hn]
  calc orbitAverage T f n ω ≤ (n:ℝ)⁻¹*∑ _i∈Finset.range n, (1:ℝ) :=
         mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hf _).2) (by positivity)
       _ = 1 := by simp [hn]

lemma orbitAverage_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (n : ℕ) (hn : n≠0) : (∫ ω, orbitAverage T f n ω ∂μ)=∫ ω, f ω ∂μ := by
  simp only [orbitAverage]
  rw [integral_const_mul,integral_finsetSum (Finset.range n) (fun i _ => (show Integrable (fun ω => f (T^[i] ω)) μ from (hT.iterate i).integrable_comp_of_integrable hf))]
  have hi (i : ℕ) : (∫ ω, f (T^[i] ω) ∂μ)=∫ ω, f ω ∂μ := by
    have hh := integral_map (hT.iterate i).measurable.aemeasurable
      (show AEStronglyMeasurable f (μ.map (T^[i])) from by rw [(hT.iterate i).map_eq]; exact hf.aestronglyMeasurable)
    rw [(hT.iterate i).map_eq] at hh
    exact hh.symm
  simp only [hi]
  simp [hn]

lemma lp_orbitAverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (x : Lp ℝ 2 μ) (n : ℕ) :
    (birkhoffAverage ℝ (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).toContinuousLinearMap id n x : Lp ℝ 2 μ)
      =ᵐ[μ] orbitAverage T x n := by
  let L := (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).toContinuousLinearMap
  have hi (i : ℕ) : (L^[i] x : Lp ℝ 2 μ)=ᵐ[μ] (fun ω => x (T^[i] ω)) := by
    change ((Lp.compMeasurePreserving T hT)^[i] x : Lp ℝ 2 μ)=ᵐ[μ] _
    rw [Lp.compMeasurePreserving_iterate]
    exact Lp.coeFn_compMeasurePreserving x (hT.iterate i)
  have hs := Lp.coeFn_fun_finsetSum (Finset.range n) (fun i => L^[i] x)
  have hm := Lp.coeFn_smul ((n:ℝ)⁻¹) (∑ i∈Finset.range n, L^[i] x)
  have hall := ae_all_iff.mpr hi
  filter_upwards [hs,hm,hall] with ω hs hm hh
  change (((n:ℝ)⁻¹ • ∑ i∈Finset.range n, L^[i] x : Lp ℝ 2 μ) : Ω → ℝ) ω=_
  rw [hm]
  change (n:ℝ)⁻¹ * _ = _
  rw [hs]
  simp only [orbitAverage,hh]

lemma stationary_bounded_growth_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ ω, f ω∈Set.Icc 0 1) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ᵐ ω ∂μ, g ω∈Set.Icc 0 1) ∧
      (∀ᵐ ω ∂μ, g (T ω)=g ω) ∧ (∫ ω, g ω ∂μ)=∫ ω, f ω ∂μ ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T f (ns k) ω) atTop (𝓝 (g ω)) := by
  let hfLp : MemLp f 2 μ := memLp_of_bounded (Eventually.of_forall hb) hf.aestronglyMeasurable 2
  let x := hfLp.toLp f
  let L := (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).toContinuousLinearMap
  let y := (L.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto x
  have hy : L (y : Lp ℝ 2 μ)=(y : Lp ℝ 2 μ) := y.property
  have hlim := L.tendsto_birkhoffAverage_orthogonalProjection
    (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).norm_toContinuousLinearMap_le x
  obtain ⟨ns,hns,hnsLim⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  let g := (Lp.aestronglyMeasurable (y : Lp ℝ 2 μ)).mk (y : Lp ℝ 2 μ)
  have hgm : Measurable g := (Lp.aestronglyMeasurable (y : Lp ℝ 2 μ)).measurable_mk
  have hg : (y : Lp ℝ 2 μ)=ᵐ[μ] g := (Lp.aestronglyMeasurable (y : Lp ℝ 2 μ)).ae_eq_mk
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℕ, x (T^[i] ω)=f (T^[i] ω) :=
    ae_all_iff.mpr fun i => (hT.iterate i).quasiMeasurePreserving.ae hfLp.coeFn_toLp
  have hco : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      (birkhoffAverage ℝ L id n x : Lp ℝ 2 μ) ω=orbitAverage T f n ω := by
    have ha := ae_all_iff.mpr (lp_orbitAverage μ hT x)
    filter_upwards [ha,hall] with ω ha hh n
    rw [ha n]
    simp only [orbitAverage,hh]
  have hgLim : ∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T f (ns k) ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hnsLim,hco,hg] with ω hh hc hg
    change Tendsto (fun k => (birkhoffAverage ℝ L id (ns k) x : Lp ℝ 2 μ) ω) atTop (𝓝 ((y : Lp ℝ 2 μ) ω)) at hh
    simpa only [hc,hg] using hh
  have hgb : ∀ᵐ ω ∂μ, g ω∈Set.Icc 0 1 := hgLim.mono fun ω hh =>
    isClosed_Icc.mem_of_tendsto hh (Eventually.of_forall fun k => orbitAverage_bounds T f hb _ ω)
  have hinv : ∀ᵐ ω ∂μ, g (T ω)=g ω := by
    have he := Lp.coeFn_compMeasurePreserving (y : Lp ℝ 2 μ) hT
    change ((L (y : Lp ℝ 2 μ) : Lp ℝ 2 μ) : Ω → ℝ)=ᵐ[μ] _ at he
    rw [hy] at he
    filter_upwards [he,hg,hT.quasiMeasurePreserving.ae hg] with ω he hg hgt
    exact hgt.symm.trans (he.symm.trans hg)
  have hfi : Integrable f μ := (memLp_of_bounded (Eventually.of_forall hb) hf.aestronglyMeasurable 1).integrable (by rfl)
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun k => (orbitAverage_measurable T hT.measurable f hf (ns k)).aestronglyMeasurable)
    (integrable_const 1) (fun k => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (orbitAverage_bounds T f hb (ns k) ω).1]
      exact (orbitAverage_bounds T f hb (ns k) ω).2) hgLim
  have hevent : ∀ᶠ k in atTop, (∫ ω, orbitAverage T f (ns k) ω ∂μ)=∫ ω, f ω ∂μ := by
    filter_upwards [hns.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    exact orbitAverage_integral μ hT hfi _ (by omega)
  refine ⟨g,hgm,hgb,hinv,?_,ns,hns,hgLim⟩
  exact tendsto_nhds_unique hint (tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm))

lemma growth_limit_respects_symmetry {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {T : Ω → Ω} {f g : Ω → ℝ} (ns : ℕ → ℕ)
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T f (ns k) ω) atTop (𝓝 (g ω)))
    {S : Ω → Ω} (hS : MeasurePreserving S μ μ)
    (hcomm : Function.Commute T S) (hfS : ∀ ω, f (S ω)=f ω) :
    ∀ᵐ ω ∂μ, g (S ω)=g ω := by
  filter_upwards [hg,hS.quasiMeasurePreserving.ae hg] with ω hω hSω
  have he (k : ℕ) : orbitAverage T f (ns k) (S ω)=orbitAverage T f (ns k) ω := by
    simp only [orbitAverage, (hcomm.iterate_left _).eq, hfS]
  exact tendsto_nhds_unique (hSω.congr fun k => he k) hω

lemma stationary_positive_growth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (c : Ω → ℝ) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hci : Integrable c μ) (hcp : 0<∫ ω, c ω ∂μ) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ᵐ ω ∂μ, g ω∈Set.Icc 0 1) ∧
      (∀ᵐ ω ∂μ, g (T ω)=g ω) ∧ ∃ ζ : ℝ, 0<ζ ∧ 0<μ {ω | ζ<g ω} ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T (fun ω => min (c ω) 1) (ns k) ω) atTop (𝓝 (g ω))) ∧
        ∀ᵐ ω ∂μ, ζ<g ω → ∀ᶠ k in atTop,
          ζ*(ns k:ℝ)<∑ i∈Finset.range (ns k), c (T^[i] ω) := by
  let f := fun ω => min (c ω) 1
  have hfm : Measurable f := hc.min measurable_const
  have hfb : ∀ ω, f ω∈Set.Icc 0 1 := fun ω => ⟨le_min (hc0 ω) (by norm_num),min_le_right _ _⟩
  have hfi : Integrable f μ := (memLp_of_bounded (Eventually.of_forall hfb) hfm.aestronglyMeasurable 1).integrable (by rfl)
  have hfp : 0<∫ ω, f ω ∂μ := by
    by_contra hh
    have hz := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => (hfb ω).1) hfi).mp
      (le_antisymm (le_of_not_gt hh) (integral_nonneg fun ω => (hfb ω).1))
    have hcz : c=ᵐ[μ] 0 := hz.mono fun ω hh => by
      change min (c ω) 1=0 at hh
      change c ω=0
      rcases min_cases (c ω) 1 with h|h
      · rw [h.1] at hh; exact hh
      · rw [h.1] at hh; norm_num at hh
    have hi0 : (∫ ω, c ω ∂μ)=0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hc0) hci).mpr hcz
    linarith
  obtain ⟨g,hgm,hgb,hgT,hgi,ns,hns,hlim⟩ := stationary_bounded_growth_limit μ hT f hfm hfb
  have hgp : 0<∫ ω, g ω ∂μ := by rw [hgi]; exact hfp
  have hex : ∃ ζ : ℝ, 0<ζ ∧ 0<μ {ω | ζ<g ω} := by
    by_contra! hh
    have hz (k : ℕ) : ∀ᵐ ω ∂μ, g ω≤1/(k+1:ℝ) := by
      rw [ae_iff]
      simpa only [not_le] using (le_zero_iff.mp (hh (1/(k+1:ℝ)) (by positivity)))
    have hgz : ∀ᵐ ω ∂μ, g ω≤0 := by
      filter_upwards [ae_all_iff.mpr hz] with ω hω
      exact ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat) (Eventually.of_forall hω)
    have hgi' : Integrable g μ := (memLp_of_bounded hgb hgm.aestronglyMeasurable 1).integrable (by rfl)
    have hgle := integral_nonpos_of_ae hgz
    linarith
  obtain ⟨ζ,hζ,hE⟩ := hex
  refine ⟨g,hgm,hgb,hgT,ζ,hζ,hE,ns,hns,hlim,?_⟩
  filter_upwards [hlim] with ω hω hgω
  filter_upwards [hω.eventually (lt_mem_nhds hgω),hns.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk hn
  have hn0 : (0:ℝ)<ns k := by exact_mod_cast (show 0<ns k by omega)
  have hh : ζ*(ns k:ℝ)<∑ i∈Finset.range (ns k), f (T^[i] ω) := by
    apply (lt_div_iff₀ hn0).mp
    simpa only [orbitAverage,div_eq_mul_inv,mul_comm] using hk
  exact hh.trans_le (Finset.sum_le_sum fun i _ => min_le_left _ _)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ArrayCostGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma array_cost_decay_of_growth {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hc : ∀ j, (Y.1 j).2.2≠⊤) (ζ : ℝ) (hζ : 0<ζ) (ns : ℕ → ℕ) (hns : StrictMono ns)
    (hg : ∀ᶠ k in atTop, ζ*(ns k:ℝ)<∑ j∈Finset.range (ns k), arrayRealCost e (StationaryCompact.shift^[j] Y)) :
    ∀ ε : ℝ, 0<ε → ∃ m, (expNeg (arrayWindowCost e 0 m Y)).toReal<ε := by
  have ht : Tendsto (fun k => ζ*(ns k:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop).const_mul_atTop hζ
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  intro ε hε
  obtain ⟨k,hk,hk'⟩ := (hg.and (he.eventually (gt_mem_nhds hε))).exists
  refine ⟨ns k,?_⟩
  have hf : arrayWindowCost e 0 (ns k) Y≠⊤ := by
    unfold arrayWindowCost
    exact ENNReal.sum_ne_top.mpr fun j _ => hc (0+j)
  rw [expNeg_toReal_of_ne_top _ hf,arrayWindowCost_toReal e Y hc]
  exact (Real.exp_lt_exp.mpr (neg_lt_neg hk)).trans hk'

lemma array_growth_symmetry {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    (g : ActualEpisodeArray e → ℝ) (ns : ℕ → ℕ)
    (hlim : ∀ᵐ Y ∂μ, Tendsto (fun k => orbitAverage StationaryCompact.shift
      (fun Y => min (arrayRealCost e Y) 1) (ns k) Y) atTop (𝓝 (g Y)))
    (hperm : ∀ σ, MeasurePreserving (arrayPerm e σ) μ μ) (σ : Equiv.Perm ℕ) :
    ∀ᵐ Y ∂μ, g (arrayPerm e σ Y)=g Y := by
  exact growth_limit_respects_symmetry μ ns hlim (hperm σ) (fun Y => rfl) (fun Y => rfl)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentDyadic
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma upperNoDrop_positive_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν), 0<upperNoDrop e ξ := by
  rw [←upperField_map e ν 0]
  apply (ae_map_iff ((upperField_measurable_rows e 0).mono (rowSigma_le _) le_rfl).aemeasurable
    (measurableSet_lt measurable_const (upperNoDrop_measurable e))).mpr
  filter_upwards [quenched_noDrop_positive_of_directionallyTransient ν hue _ (signed_direction_unit e) htrans] with ω hω
  rw [upperNoDrop_restrict]
  exact hω 0

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Dust
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma upperNoDropMean_pos {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (htrans : DirectionallyTransient ν (realPosition (step e))) :
    0<upperNoDropMean e ν := by
  have hi : Integrable (fun ξ => (upperNoDrop e ξ).toReal)
      (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)) :=
    (integrable_const (1:ℝ)).mono' (upperNoDrop_measurable e).ennreal_toReal.aestronglyMeasurable
      (Eventually.of_forall (upperNoDrop_toReal_bound e))
  by_contra hh
  have hz : (∫ ξ, (upperNoDrop e ξ).toReal ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))=0 :=
    le_antisymm (le_of_not_gt hh) (integral_nonneg fun _ => ENNReal.toReal_nonneg)
  have he := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hi).mp hz
  obtain ⟨ξ,hp,hz⟩ := ((upperNoDrop_positive_ae e ν hue htrans).and he).exists
  exact (ENNReal.toReal_pos hp.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (upperNoDrop_le_one e ξ))).ne' hz

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma average_zero_of_survival (p : ℝ) (hp : 0<p) (D : ℕ → ℝ)
    (hD : ∀ r, 0≤D r) (S W : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hS : ∀ m, IsBoundedUnder (·≤·) atTop (S m))
    (hWS : ∀ m r, W m r≤S m r)
    (hcenter : ∀ m, Tendsto (fun r => W m r-p*D r) atTop (𝓝 0))
    (hlim : ∀ m, limsup (S m) atTop≤a m)
    (hz : ∀ ε : ℝ, 0<ε → ∃ m, a m<ε) : Tendsto D atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := hz (p*ε/2) (by positivity)
  have hsev := eventually_lt_of_limsup_lt ((hlim m).trans_lt hm) (hS m)
  have hwev := (tendsto_order.mp (hcenter m)).1 (-p*ε/2) (by nlinarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsev.and hwev)
  refine ⟨N,fun r hr => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hD r)]
  have hh := hN r hr
  have hw := hWS m r
  nlinarith

lemma symmetric_indicator_zero_of_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : ℕ → Ω → ℝ)
    (hI : ∀ a, Measurable (I a)) (hb : ∀ a ω, I a ω∈Set.Icc 0 1)
    (hmean : ∀ a, (∫ ω, I a ω ∂μ)=∫ ω, I 0 ω ∂μ)
    (ns : ℕ → ℕ) (hn : ∀ r, 0<ns r)
    (hz : ∀ᵐ ω ∂μ, Tendsto (fun r => (ns r:ℝ)⁻¹*∑ a∈Finset.range (ns r), I a ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ a, I a ω=0 := by
  have hi (a : ℕ) : Integrable (I a) μ :=
    (memLp_of_bounded (Eventually.of_forall (hb a)) (hI a).aestronglyMeasurable 1).integrable (by rfl)
  let F : ℕ → Ω → ℝ := fun r ω => (ns r:ℝ)⁻¹*∑ a∈Finset.range (ns r), I a ω
  have hf (r : ℕ) (ω : Ω) : F r ω∈Set.Icc 0 1 := by
    refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => (hb a ω).1),?_⟩
    calc F r ω ≤ (ns r:ℝ)⁻¹*∑ _a∈Finset.range (ns r), (1:ℝ) :=
           mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => (hb a ω).2) (by positivity)
         _ = 1 := by simp [(hn r).ne']
  have he (r : ℕ) : (∫ ω, F r ω ∂μ)=∫ ω, I 0 ω ∂μ := by
    dsimp only [F]
    rw [integral_const_mul,integral_finsetSum _ (fun a _ => hi a)]
    simp only [hmean,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast (hn r).ne'),one_mul]
  have hl := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun r => (show Measurable (F r) from by dsimp [F]; fun_prop).aestronglyMeasurable)
    (integrable_const 1) (fun r => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hf r ω).1]; exact (hf r ω).2) hz
  simp only [he,integral_zero] at hl
  have hzero : (∫ ω, I 0 ω ∂μ)=0 := tendsto_nhds_unique tendsto_const_nhds hl
  apply ae_all_iff.mpr
  intro a
  exact (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => (hb a ω).1) (hi a)).mp
    ((hmean a).trans hzero)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayDust
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayDust_measurable {d : ℕ} (e : Direction d) (i : ℤ) (a : ℕ) :
    MeasurableSet {Y : ActualEpisodeArray e | arrayDust e i a Y} := by
  exact (show Measurable (fun Y : ActualEpisodeArray e => (Y.2.2.1 (i,(i,a),0):ℝ)) from by fun_prop)
    (measurableSet_singleton 0)

lemma arrayDustFrequency_nonneg {d : ℕ} (e : Direction d) (i : ℤ) (n : ℕ) (Y : ActualEpisodeArray e) :
    0≤arrayDustFrequency e i n Y := by
  unfold arrayDustFrequency ReferenceClasses.dustFrequency
  positivity

lemma arraySurvivalAverage_le_one {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (hn : 0<n) (Y : ActualEpisodeArray e) : arraySurvivalAverage e i m H n Y≤1 := by
  have hk (a : ℕ) : upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (upperHorizontalKernel_mass_le_one e H _ 0)
  rw [arraySurvivalAverage,arraySurvivalSum,ENNReal.toReal_sum (fun a _ => hk a)]
  calc
    _ ≤ (n:ℝ)⁻¹*∑ _a∈Finset.range n, (1:ℝ) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a _ => by
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
          (upperHorizontalKernel_mass_le_one e H (arrayUpperRows e i m a Y) 0)) (by positivity)
    _ = 1 := by simp [hn.ne']

lemma arrayDustWeight_le_survival {d : ℕ} (e : Direction d) (i : ℤ) (m H n : ℕ)
    (Y : ActualEpisodeArray e)
    (h : ∀ a, upperNoDrop e (arrayUpperRows e i m a Y)≤
      upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ) :
    currentDustWeight e n (typedCurrentArrayWindow e i m Y)≤arraySurvivalAverage e i m H n Y := by
  have hk (a : ℕ) : upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ≠⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (upperHorizontalKernel_mass_le_one e H _ 0)
  rw [arraySurvivalAverage,arraySurvivalSum,ENNReal.toReal_sum (fun a _ => hk a)]
  unfold currentDustWeight ReferenceClasses.dustWeight sampleAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro a _
  dsimp only
  split_ifs
  · exact ENNReal.toReal_mono (hk a) (h a)
  · exact ENNReal.toReal_nonneg

lemma array_dust_frequency_zero {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (Y : ActualEpisodeArray e) (i : ℤ)
    (href : ∀ m, Tendsto (fun r : ℕ => currentDustWeight e (2^r) (typedCurrentArrayWindow e i m Y)-
      upperNoDropMean e ν*arrayDustFrequency e i (2^r) Y) atTop (𝓝 0) ∧
      ∀ a H : ℕ, upperNoDrop e (arrayUpperRows e i m a Y)≤
        upperHorizontalKernel e H (arrayUpperRows e i m a Y) 0 Set.univ)
    (hmarks : ∀ j, (Y.1 j).1<⊤) (hsurv : ArrayAveragedSurvival e Y)
    (hcost : ∀ ε : ℝ, 0<ε → ∃ m, (expNeg (arrayWindowCost e i m Y)).toReal<ε) :
    Tendsto (fun r : ℕ => arrayDustFrequency e i (2^r) Y) atTop (𝓝 0) := by
  have hfin (m : ℕ) : arrayWindowHeight e i m Y≠⊤ := by
    unfold arrayWindowHeight
    exact (ENat.sum_ne_top).mpr fun j hj => (hmarks (i+j)).ne
  let H := fun m => (arrayWindowHeight e i m Y).toNat
  have hH (m : ℕ) : arrayWindowHeight e i m Y=(H m:ℕ∞) := (ENat.natCast_toNat (hfin m)).symm
  apply average_zero_of_survival (upperNoDropMean e ν) (upperNoDropMean_pos e ν hue htrans)
    _ (fun r => arrayDustFrequency_nonneg e i _ Y)
    (fun m r => arraySurvivalAverage e i m (H m) (2^r) Y)
    (fun m r => currentDustWeight e (2^r) (typedCurrentArrayWindow e i m Y))
    (fun m => (expNeg (arrayWindowCost e i m Y)).toReal)
  · intro m
    exact isBoundedUnder_of_eventually_le (Eventually.of_forall fun r => arraySurvivalAverage_le_one e i m (H m) (2^r) (by positivity) Y)
  · exact fun m r => arrayDustWeight_le_survival e i m (H m) _ Y (fun a => (href m).2 a (H m))
  · exact fun m => (href m).1
  · exact fun m => hsurv i m (H m) (hH m)
  · exact hcost

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma arrayDust_perm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) (i : ℤ) (a : ℕ)
    (Y : ActualEpisodeArray e) : arrayDust e i a (arrayPerm e σ Y) ↔ arrayDust e i (σ a) Y := Iff.rfl

lemma array_no_dust_on_frequency_zero {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    [IsProbabilityMeasure μ] (i : ℤ) (E : Set (ActualEpisodeArray e)) (hE : MeasurableSet E)
    (hperm : ∀ σ, MeasurePreserving (arrayPerm e σ) μ μ)
    (hEinv : ∀ σ, ∀ᵐ Y ∂μ, arrayPerm e σ Y∈E ↔ Y∈E)
    (hfreq : ∀ᵐ Y ∂μ, Y∈E → Tendsto (fun r : ℕ => arrayDustFrequency e i (2^r) Y) atTop (𝓝 0)) :
    ∀ᵐ Y ∂μ, Y∈E → ∀ a, ¬arrayDust e i a Y := by
  let I : ℕ → ActualEpisodeArray e → ℝ := fun a Y => if Y∈E ∧ arrayDust e i a Y then 1 else 0
  have hm (a : ℕ) : Measurable (I a) := Measurable.ite (hE.inter (arrayDust_measurable e i a)) measurable_const measurable_const
  have hb (a : ℕ) (Y : ActualEpisodeArray e) : I a Y∈Set.Icc 0 1 := by dsimp [I]; split_ifs <;> norm_num
  have hmean (a : ℕ) : (∫ Y, I a Y ∂μ)=∫ Y, I 0 Y ∂μ := by
    let σ := Equiv.swap 0 a
    have he : (fun Y => I 0 (arrayPerm e σ Y))=ᵐ[μ] I a := by
      filter_upwards [hEinv σ] with Y hY
      dsimp only [I]
      rw [hY,arrayDust_perm,Equiv.swap_apply_left]
    calc
      _ = ∫ Y, I 0 (arrayPerm e σ Y) ∂μ := (integral_congr_ae he).symm
      _ = ∫ Y, I 0 Y ∂μ := by
        rw [←integral_map (hperm σ).measurable.aemeasurable (hm 0).aestronglyMeasurable,(hperm σ).map_eq]
  have hav : ∀ᵐ Y ∂μ, Tendsto (fun r : ℕ => ((2^r:ℕ):ℝ)⁻¹*∑ a∈Finset.range (2^r), I a Y) atTop (𝓝 0) := by
    filter_upwards [hfreq] with Y hY
    by_cases hy : Y∈E
    · simpa only [I,hy,true_and,arrayDustFrequency,ReferenceClasses.dustFrequency] using hY hy
    · simp only [I,hy,false_and,ite_false, if_false,Finset.sum_const_zero,mul_zero]
      exact tendsto_const_nhds
  have hz := symmetric_indicator_zero_of_average μ I hm hb hmean (fun r => 2^r) (fun r => by positivity) hav
  filter_upwards [hz] with Y hY hy a ha
  have hh := hY a
  simp only [I,hy,ha,and_self,ite_true, if_true] at hh
  norm_num at hh

lemma array_no_dust_on_cost_decay {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (μ : Measure (ActualEpisodeArray e)) [IsProbabilityMeasure μ]
    (hconsistent : ∀ᵐ Y ∂μ, ArrayOffsetsConsistent e Y ∧ ArrayProfilesConsistent e Y)
    (hzero : ∀ᵐ Y ∂μ, ∀ p q z, p≠q → arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0)
    (hentropy : ∀ i m, let W:=μ.map (typedCurrentArrayWindow e i m)
      InformationTheory.klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤)
    (hmarks : ∀ᵐ Y ∂μ, ∀ j, (Y.1 j).1<⊤)
    (hsurv : ∀ᵐ Y ∂μ, ArrayAveragedSurvival e Y)
    (hperm : ∀ σ, MeasurePreserving (arrayPerm e σ) μ μ)
    (i : ℤ) (E : Set (ActualEpisodeArray e)) (hE : MeasurableSet E)
    (hEinv : ∀ σ, ∀ᵐ Y ∂μ, arrayPerm e σ Y∈E ↔ Y∈E)
    (hcost : ∀ᵐ Y ∂μ, Y∈E → ∀ ε : ℝ, 0<ε → ∃ m, (expNeg (arrayWindowCost e i m Y)).toReal<ε) :
    ∀ᵐ Y ∂μ, Y∈E → ∀ a, ¬arrayDust e i a Y := by
  apply array_no_dust_on_frequency_zero e μ i E hE hperm hEinv
  have href := array_dust_reference_facts e ν htrans μ hconsistent hzero hentropy
  filter_upwards [href,hmarks,hsurv,hcost] with Y hr hm hs hc hY
  exact array_dust_frequency_zero e ν hue htrans Y i (hr i) hm hs (hc hY)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ArrayGrowthEvent
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

theorem growth_sector (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    Nonempty (ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) := by
  let μ := (L.law : Measure (ActualEpisodeArray e))
  obtain ⟨g,hgm,hgb,hgT,ζ,hζ,hE,ns,hns,hlim,hgrowth⟩ := stationary_positive_growth μ
    L.preserving (arrayRealCost e) (arrayRealCost_measurable e) (arrayRealCost_nonneg e)
      L.integrable_cost L.positive_cost
  let E := {Y | ζ<g Y}
  have hmE : MeasurableSet E := measurableSet_lt measurable_const hgm
  have heT : ∀ᵐ Y ∂μ, StationaryCompact.shift Y∈E ↔ Y∈E := by
    filter_upwards [hgT] with Y hY
    change ζ<g (StationaryCompact.shift Y) ↔ ζ<g Y
    rw [hY]
  have heP (σ : Equiv.Perm ℕ) : ∀ᵐ Y ∂μ, arrayPerm e σ Y∈E ↔ Y∈E := by
    filter_upwards [array_growth_symmetry e μ g ns hlim L.symmetric σ] with Y hY
    change ζ<g (arrayPerm e σ Y) ↔ ζ<g Y
    rw [hY]
  have hc : ∀ᵐ Y ∂μ, ∀ j, (Y.1 j).2.2≠⊤ := L.finite_marks.mono fun Y hY j => (hY j).2.2.2.ne
  have hd : ∀ᵐ Y ∂μ, Y∈E → ∀ ε : ℝ, 0<ε → ∃ m,
      (expNeg (arrayWindowCost e 0 m Y)).toReal<ε := by
    filter_upwards [hc,hgrowth] with Y hY hg hy
    exact array_cost_decay_of_growth e Y hY ζ hζ ns hns (hg hy)
  have hn0 := array_no_dust_on_cost_decay e ν hue htrans μ L.consistent L.zero_sampling
    L.entropy_finite (L.finite_marks.mono fun Y hY j => (hY j).2.1) L.survival L.symmetric 0 E hmE heP hd
  have hnd : ∀ᵐ Y ∂μ, Y∈E → ∀ i a, ¬arrayDust e i a Y := by
    have hh := stationary_ae_integer_family μ L.preserving (fun i Y => Y∈E → ∀ a, ¬arrayDust e i a Y)
      (fun i => hmE.imp (by
        simpa only [Set.ofPred_forall, Set.compl_ofPred] using MeasurableSet.iInter fun a => (arrayDust_measurable e i a).compl))
      (fun i => heT.mono fun Y hY => by
        rw [hY]
        rfl) hn0
    filter_upwards [hh] with Y hY hy i
    exact hY i hy
  refine ⟨⟨E,hmE,hE,heT,heP,ζ,hζ,ns,hns,?_,hnd⟩⟩
  filter_upwards [hc,hgrowth] with Y hY hg hy
  simpa only [arrayWindowCost_toReal e Y hY] using hg hy

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_CanonicalLogExcess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma canonicalLogExcess_nonneg {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) :
    0 ≤ canonicalLogExcess A p ω := ENNReal.toReal_nonneg

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_TailCuts
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace TailCuts

lemma lower_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) (j : ℤ) : 0 < lower μ j := by
  exact (hμ j).trans_le (measureReal_mono (by intro x hx; have hx' : x = j := hx; subst x; exact (show (j : ℤ) ≤ j from le_rfl)))

lemma upper_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) (j : ℤ) : 0 < upper μ j := by
  exact (hμ j).trans_le (measureReal_mono (by intro x hx; have hx' : x = j := hx; subst x; exact (show (j : ℤ) ≤ j from le_rfl)))

lemma lower_tendsto (μ : Measure ℤ) [IsFiniteMeasure μ] :
    Tendsto (lower μ) atBot (𝓝 0) := by
  have ht := tendsto_measure_iInter_atBot (μ := μ)
    (s := fun j : ℤ => Set.Iic j) (fun j => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ hij => Set.Iic_subset_Iic.mpr hij) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ j : ℤ, Set.Iic j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Set.mem_iInter.mp hx (x - 1)
    simp only [Set.mem_Iic] at hx'
    omega
  rw [he, measure_empty] at ht
  change Tendsto (fun j => (μ (Set.Iic j)).toReal) atBot (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

end TailCuts

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_TailGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailGrowth

lemma first_tail_threshold (μ : Measure ℤ) [IsFiniteMeasure μ] {q : ℝ}
    (hq : 0 < q) (hqμ : q < μ.real Set.univ) :
    ∃ j : ℤ, q ≤ μ.real (Set.Iic j) ∧ μ.real (Set.Iio j) < q := by
  have htop : Tendsto (fun j : ℤ => μ.real (Set.Iic j)) atTop (𝓝 (μ.real Set.univ)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_Iic_atTop μ)
  have hbot := TailCuts.lower_tendsto μ
  obtain ⟨b,hb⟩ := eventually_atBot.mp (hbot.eventually (gt_mem_nhds hq))
  have hbound : ∃ b : ℤ, ∀ z, q ≤ μ.real (Set.Iic z) → b ≤ z := by
    refine ⟨b,fun z hz => ?_⟩
    by_contra h
    exact (not_lt_of_ge hz) (hb z (le_of_lt (lt_of_not_ge h)))
  have hex : ∃ j : ℤ, q ≤ μ.real (Set.Iic j) :=
    ((htop.eventually (lt_mem_nhds hqμ)).exists).imp fun j hj => hj.le
  obtain ⟨j,hj,hmin⟩ := Int.exists_least_of_bdd hbound hex
  refine ⟨j,hj,?_⟩
  have he : Set.Iio j = Set.Iic (j-1) := by ext z; simp only [Set.mem_Iio,Set.mem_Iic]; omega
  rw [he]
  by_contra h
  have := hmin (j-1) (le_of_not_gt h)
  omega

lemma ordered_pair_common_cut (μ ν : Measure ℤ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ.real Set.univ ≤ 1) (hν : ν.real Set.univ ≤ 1)
    (R : ℤ) {q : ℝ} (hq : 0 < q)
    (hpair : q ≤ (μ.prod ν).real {p | p.1 + R ≤ p.2}) :
    ∃ j : ℤ, q / 2 ≤ μ.real (Set.Iic j) ∧ q / 2 ≤ ν.real (Set.Ici (j+R)) := by
  have hqμ : q ≤ μ.real Set.univ := by
    calc
      q ≤ (μ.prod ν).real {p | p.1 + R ≤ p.2} := hpair
      _ ≤ (μ.prod ν).real (Set.univ ×ˢ Set.univ) :=
        measureReal_mono (by intro p hp; exact ⟨Set.mem_univ _,Set.mem_univ _⟩) (measure_ne_top _ _)
      _ = μ.real Set.univ * ν.real Set.univ := measureReal_prod_prod _ _
      _ ≤ μ.real Set.univ * 1 := mul_le_mul_of_nonneg_left hν (measureReal_nonneg)
      _ = μ.real Set.univ := mul_one _
  obtain ⟨j,hj,hprev⟩ := first_tail_threshold μ (by linarith : 0 < q/2) (by linarith : q/2 < μ.real Set.univ)
  refine ⟨j,hj,?_⟩
  by_contra hh
  have hh' : ν.real (Set.Ici (j+R)) < q/2 := lt_of_not_ge hh
  have hsub : {p : ℤ × ℤ | p.1 + R ≤ p.2} ⊆
      (Set.Iio j ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Ici (j+R)) := by
    intro p hp
    by_cases hx : p.1 < j
    · exact Or.inl ⟨hx,Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _,by change j+R ≤ p.2; dsimp at hp; omega⟩
  have hle : q ≤ μ.real (Set.Iio j) + ν.real (Set.Ici (j+R)) := by
    calc
      q ≤ (μ.prod ν).real {p | p.1+R ≤ p.2} := hpair
      _ ≤ (μ.prod ν).real ((Set.Iio j ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Ici (j+R))) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (μ.prod ν).real (Set.Iio j ×ˢ Set.univ) +
          (μ.prod ν).real (Set.univ ×ˢ Set.Ici (j+R)) := measureReal_union_le _ _
      _ = μ.real (Set.Iio j) * ν.real Set.univ + μ.real Set.univ * ν.real (Set.Ici (j+R)) := by
        rw [measureReal_prod_prod,measureReal_prod_prod]
      _ ≤ μ.real (Set.Iio j) * 1 + 1 * ν.real (Set.Ici (j+R)) :=
        add_le_add (mul_le_mul_of_nonneg_left hν measureReal_nonneg)
          (mul_le_mul_of_nonneg_right hμ measureReal_nonneg)
      _ = μ.real (Set.Iio j) + ν.real (Set.Ici (j+R)) := by ring
  linarith

lemma score_bddAbove (μ : Measure ℤ) [IsFiniteMeasure μ] (R : ℤ) :
    BddAbove (Set.range (TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R)) := by
  refine ⟨μ.real Set.univ,?_⟩
  rintro _ ⟨j,rfl⟩
  exact (min_le_left _ _).trans (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))

lemma score_le_statistic (μ : Measure ℤ) [IsFiniteMeasure μ] (R j : ℤ) :
    TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j ≤ statistic μ R :=
  le_ciSup (score_bddAbove μ R) j

lemma statistic_le_mass (μ : Measure ℤ) [IsFiniteMeasure μ] (R : ℤ) :
    statistic μ R ≤ μ.real Set.univ := by
  apply ciSup_le
  intro j
  exact (min_le_left _ _).trans (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))

lemma statistic_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hfull : ∀ j, 0 < μ.real {j}) (R : ℤ) : 0 < statistic μ R := by
  apply lt_of_lt_of_le _ (score_le_statistic μ R 0)
  exact lt_min (TailCuts.lower_pos μ hfull _) (TailCuts.upper_pos μ hfull _)

lemma statistic_eq_max (μ : Measure ℤ) [IsFiniteMeasure μ] (R j : ℤ)
    (hj : ∀ k, TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R k ≤
      TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j) :
    statistic μ R = TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j := by
  exact le_antisymm (ciSup_le hj) (score_le_statistic μ R j)

lemma statistic_grows (μ ν w' : Measure ℤ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure w']
    (hμ : μ.real Set.univ ≤ 1) (hν : ν.real Set.univ ≤ 1)
    (R : ℤ) {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t)
    (hpair : q ≤ (μ.prod ν).real {p | p.1+R ≤ p.2})
    (hleft : ∀ j, t * μ.real (Set.Iic j) ≤ w'.real (Set.Iic j))
    (hright : ∀ j, t * ν.real (Set.Ici j) ≤ w'.real (Set.Ici j)) :
    t * q / 2 ≤ statistic w' R := by
  obtain ⟨j,hj,hj'⟩ := ordered_pair_common_cut μ ν hμ hν R hq hpair
  apply le_trans _ (score_le_statistic w' R j)
  change t*q/2 ≤ min _ _
  exact le_min (by simpa [mul_div_assoc, TailCuts.lower, TailCuts.upper] using (mul_le_mul_of_nonneg_left hj ht).trans (hleft j))
    (by simpa [mul_div_assoc, TailCuts.lower, TailCuts.upper] using (mul_le_mul_of_nonneg_left hj' ht).trans (hright (j+R)))

lemma log_statistic_grows (μ ν w w' : Measure ℤ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure w] [IsFiniteMeasure w']
    (hμ : μ.real Set.univ ≤ 1) (hν : ν.real Set.univ ≤ 1)
    (R : ℤ) {Q C a Z : ℝ} (hw : 0 < statistic w R) (hQ : 0 < Q)
    (hpair : Q ≤ (μ.prod ν).real {p | p.1+R ≤ p.2})
    (hlog : -a-Z ≤ Real.log Q)
    (hleft : ∀ j, (Real.exp C * statistic w R) * μ.real (Set.Iic j) ≤ w'.real (Set.Iic j))
    (hright : ∀ j, (Real.exp C * statistic w R) * ν.real (Set.Ici j) ≤ w'.real (Set.Ici j)) :
    C-a-Z-Real.log 2 ≤ Real.log (statistic w' R) - Real.log (statistic w R) := by
  have ht := mul_pos (Real.exp_pos C) hw
  have hg := statistic_grows μ ν w' hμ hν R hQ ht.le hpair hleft hright
  have hp : 0 < Real.exp C * statistic w R * Q / 2 :=
    div_pos (mul_pos ht hQ) (by norm_num)
  have hh := Real.log_le_log hp hg
  rw [Real.log_div (ne_of_gt (mul_pos ht hQ)) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul (ne_of_gt ht) (ne_of_gt hQ),
    Real.log_mul (ne_of_gt (Real.exp_pos C)) (ne_of_gt hw), Real.log_exp] at hh
  linarith

end TailGrowth

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailSampling
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]

lemma cutKernel_apply (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) (d : D) :
    cutKernel w S hS j hj d = (w d (S (j d)))⁻¹ • (w d).restrict (S (j d)) := rfl

lemma cutKernel_markov (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j)
    (hpos : ∀ d, w d (S (j d)) ≠ 0) (hfin : ∀ d, w d (S (j d)) ≠ ∞) :
    IsMarkovKernel (cutKernel w S hS j hj) := by
  constructor
  intro d
  constructor
  simp only [cutKernel_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel (hpos d) (hfin d)

lemma coordinate_atom_pos (μ : Measure X) [IsFiniteMeasure μ]
    [MeasurableSingletonClass X] (ξ : X → ℤ) (hξ : Measurable ξ)
    (hsurj : Function.Surjective ξ) (hμ : ∀ x, 0 < μ.real {x}) (z : ℤ) :
    0 < (μ.map ξ).real {z} := by
  obtain ⟨x,hx⟩ := hsurj z
  rw [Measure.real, Measure.map_apply hξ (measurableSet_singleton z)]
  apply lt_of_lt_of_le (hμ x)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro y hy
  simp only [Set.mem_singleton_iff] at hy
  subst y
  exact hx

end TailSampling

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TailGrowth

lemma log_integral_lower_of_exp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (Z p : X → ℝ) (a : ℝ)
    (hZ : Integrable Z μ) (hZ0 : ∀ᵐ x ∂μ, 0 ≤ Z x)
    (hp : Integrable p μ) (hlower : ∀ᵐ x ∂μ, Real.exp (-a - Z x) ≤ p x) :
    0 < ∫ x, p x ∂μ ∧
      -a - (∫ x, Z x ∂μ) ≤ Real.log (∫ x, p x ∂μ) := by
  have hF : Integrable (fun x => -a - Z x) μ := (integrable_const (-a)).sub hZ
  have hE : Integrable (fun x => Real.exp (-a - Z x)) μ := by
    apply (integrable_const (Real.exp (-a))).mono' (Real.continuous_exp.comp_aestronglyMeasurable hF.aestronglyMeasurable)
    filter_upwards [hZ0] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    hF hE
  have hi : (∫ x, -a - Z x ∂μ) = -a - ∫ x, Z x ∂μ := by
    rw [integral_sub (integrable_const _) hZ, integral_const]
    simp
  rw [hi] at hj
  have hb := hj.trans (integral_mono_ae hE hp hlower)
  have hp0 := (Real.exp_pos _).trans_le hb
  refine ⟨hp0, ?_⟩
  calc
    -a - (∫ x, Z x ∂μ) = Real.log (Real.exp (-a - ∫ x, Z x ∂μ)) :=
      (Real.log_exp _).symm
    _ ≤ Real.log (∫ x, p x ∂μ) := Real.log_le_log (Real.exp_pos _) hb

lemma log_integral_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (Z p : X → ℝ) (a : ℝ)
    (hZ : Integrable Z μ) (hZ0 : ∀ᵐ x ∂μ, 0 ≤ Z x)
    (hp : Integrable p μ) (hp0 : ∀ᵐ x ∂μ, 0 < p x)
    (hlower : ∀ᵐ x ∂μ, -a - Z x ≤ Real.log (p x)) :
    0 < ∫ x, p x ∂μ ∧
      -a - (∫ x, Z x ∂μ) ≤ Real.log (∫ x, p x ∂μ) := by
  apply log_integral_lower_of_exp μ Z p a hZ hZ0 hp
  filter_upwards [hp0,hlower] with x hx h
  simpa only [Real.exp_log hx] using Real.exp_le_exp.mpr h

end TailGrowth

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TailGrowth

lemma measurable_statistic {D : Type*} [MeasurableSpace D] (w : Kernel D ℤ) (R : ℤ) :
    Measurable (fun d => statistic (w d) R) := by
  apply Measurable.iSup
  intro j
  exact ((w.measurable_coe (s := Set.Iic j) measurableSet_Iic).ennreal_toReal).min
    ((w.measurable_coe (s := Set.Ici (j+R)) measurableSet_Ici).ennreal_toReal)

lemma statistic_translate (μ : Measure ℤ) (R z : ℤ) :
    statistic (μ.map (fun x => x+z)) R = statistic μ R := by
  unfold statistic
  have he (j : ℤ) : TailCuts.score (TailCuts.lower (μ.map (fun x => x+z)))
      (TailCuts.upper (μ.map (fun x => x+z))) R j =
      TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R (j-z) := by
    unfold TailCuts.score TailCuts.lower TailCuts.upper Measure.real
    rw [Measure.map_apply (show Measurable (fun x : ℤ => x+z) from measurable_of_countable _) measurableSet_Iic,
      Measure.map_apply (show Measurable (fun x : ℤ => x+z) from measurable_of_countable _) measurableSet_Ici]
    congr 3
    · ext x
      simp only [Set.mem_preimage, Set.mem_Iic]
      omega
    · ext x
      simp only [Set.mem_preimage, Set.mem_Ici]
      omega
  simp_rw [he]
  exact (show Function.Surjective (fun j : ℤ => j-z) from
    fun j => ⟨j+z,by dsimp; omega⟩).iSup_comp _

lemma comp_mono_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) {μ ν : Measure X} (h : μ ≤ ν) :
    κ ∘ₘ μ ≤ κ ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.bind_apply hs κ.measurable.aemeasurable,
    Measure.bind_apply hs κ.measurable.aemeasurable]
  exact lintegral_mono' h le_rfl

lemma smul_mono_scalar {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {a b : ℝ≥0∞} (h : a ≤ b) : a • μ ≤ b • μ := by
  apply Measure.le_iff.mpr
  intro s _
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul h le_rfl zero_le zero_le

lemma normalized_tail_dominated {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Set X)
    (hpos : μ s ≠ 0) {t : ℝ} (ht : t ≤ μ.real s) :
    ENNReal.ofReal t • ((μ s)⁻¹ • μ.restrict s) ≤ μ := by
  have hh : ENNReal.ofReal t ≤ μ s :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr ht
  calc
    ENNReal.ofReal t • ((μ s)⁻¹ • μ.restrict s) ≤
        μ s • ((μ s)⁻¹ • μ.restrict s) := smul_mono_scalar _ hh
    _ = μ.restrict s := by
      rw [smul_smul, ENNReal.mul_inv_cancel hpos (measure_ne_top _ _), one_smul]
    _ ≤ μ := Measure.restrict_le_self

lemma continued_tail_dominated {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) (w : Measure X) [IsFiniteMeasure w] (w' : Measure Y)
    (s : Set X) (hpos : w s ≠ 0) {C t : ℝ} (ht : t ≤ w.real s)
    (hupdate : ENNReal.ofReal (Real.exp C) • (κ ∘ₘ w) ≤ w') :
    ENNReal.ofReal (Real.exp C * t) •
      (κ ∘ₘ ((w s)⁻¹ • w.restrict s)) ≤ w' := by
  have hh := comp_mono_left κ (normalized_tail_dominated w s hpos ht)
  rw [Measure.comp_smul] at hh
  have hh' := smul_le_smul_left (ENNReal.ofReal (Real.exp C)) hh
  rw [smul_smul, ← ENNReal.ofReal_mul (Real.exp_pos C).le] at hh'
  exact hh'.trans hupdate

lemma stream_real_lower {X : Type*} [MeasurableSpace X]
    (μ w' : Measure X) [IsFiniteMeasure w'] {t : ℝ} (ht : 0 ≤ t)
    (h : ENNReal.ofReal t • μ ≤ w') (s : Set X) : t * μ.real s ≤ w'.real s := by
  have hh := ENNReal.toReal_mono (measure_ne_top w' s) (h s)
  simpa only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht] using hh

lemma prod_comp {X X' Y Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Y']
    (κ : Kernel X Y) (η : Kernel X' Y') [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (μ : Measure X) (ν : Measure X') [SFinite μ] [SFinite ν] :
    (κ ∘ₘ μ).prod (η ∘ₘ ν) = (κ ∥ₖ η) ∘ₘ (μ.prod ν) := by
  have hh := congrArg (fun K : Kernel (Unit × Unit) (Y × Y') => K ((),()))
    (Kernel.parallelComp_comp_parallelComp
      (κ := Kernel.const Unit μ) (κ' := Kernel.const Unit ν) (η := κ) (η' := η))
  simpa only [Kernel.comp_apply,Kernel.parallelComp_apply,Kernel.const_apply] using hh.symm

end TailGrowth

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ProfileGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.state_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailGrowth

lemma normalizedRestriction_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (s : Set X) (hpos : μ s ≠ 0) :
    IsProbabilityMeasure (normalizedRestriction μ s) := by
  constructor
  simp only [normalizedRestriction, Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

lemma normalizedRestriction_supported {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ∀ᵐ x ∂normalizedRestriction μ s, x ∈ s :=
  Measure.ae_smul_measure (ae_restrict_mem hs) _

lemma comp_total_le_one {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) (hκ : ∀ x, κ x Set.univ ≤ 1)
    (μ : Measure X) [IsProbabilityMeasure μ] : (κ ∘ₘ μ) Set.univ ≤ 1 := by
  rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]
  calc
    (∫⁻ x, κ x Set.univ ∂μ) ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂μ := lintegral_mono hκ
    _ = 1 := by simp

lemma real_le_one_of_total_le_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (hμ : μ Set.univ ≤ 1) (s : Set X) : μ.real s ≤ 1 := by
  exact (ENNReal.toReal_mono (by simp) ((measure_mono (Set.subset_univ s)).trans hμ)).trans_eq (by simp)

lemma ordered_stream_mass_lower {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (κ : Kernel X ℤ) [IsFiniteKernel κ] (hκ : ∀ x, κ x Set.univ ≤ 1)
    (ξ : X → ℤ) (α β : Measure X) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (R : ℤ) (hgap : ∀ᵐ p ∂α.prod β, R ≤ ξ p.2 - ξ p.1) :
    (∫ p, outwardMass κ ξ p ∂α.prod β) ≤
      ((κ ∘ₘ α).prod (κ ∘ₘ β)).real {y | y.1+R ≤ y.2} := by
  have hset : MeasurableSet {y : ℤ × ℤ | y.1+R ≤ y.2} := (Set.to_countable _).measurableSet
  have hfin : ∀ p : X × X, (κ p.1).prod (κ p.2) Set.univ ≤ 1 := by
    intro p
    rw [←Set.univ_prod_univ,Measure.prod_prod]
    exact (mul_le_of_le_one_left (by positivity) (hκ _)).trans (hκ _)
  have hm : Measurable (fun p : X × X =>
      (κ p.1).prod (κ p.2) {y | ξ p.2 - ξ p.1 ≤ y.2-y.1}) := measurable_of_countable _
  rw [Measure.real,prod_comp,
    Measure.bind_apply hset (κ ∥ₖ κ).measurable.aemeasurable]
  unfold outwardMass Measure.real
  rw [integral_toReal hm.aemeasurable (Eventually.of_forall fun p =>
    ((measure_mono (Set.subset_univ _)).trans (hfin p)).trans_lt (by simp))]
  apply ENNReal.toReal_mono
  · have hb : (∫⁻ p, (κ ∥ₖ κ) p {y | y.1+R ≤ y.2} ∂α.prod β) ≤ 1 := by
      calc
        _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂α.prod β := by
          apply lintegral_mono
          intro p
          dsimp only
          rw [Kernel.parallelComp_apply]
          exact (measure_mono (Set.subset_univ _)).trans (hfin p)
        _ = 1 := by simp
    exact ne_of_lt (hb.trans_lt (by simp))
  · apply lintegral_mono_ae
    filter_upwards [hgap] with p hp
    rw [Kernel.parallelComp_apply]
    apply measure_mono
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    omega

theorem profile_tail_growth {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X]
    (w : Measure X) [IsFiniteMeasure w] (w' : Measure ℤ) [IsFiniteMeasure w']
    (ξ : X → ℤ) (hsurj : Function.Surjective ξ) (hfull : ∀ x, 0 < w.real {x})
    (κ : Kernel X ℤ) [IsFiniteKernel κ] (hκ : ∀ x, κ x Set.univ ≤ 1)
    (R j : ℤ) (hj : ∀ k, TailCuts.score (TailCuts.lower (w.map ξ))
      (TailCuts.upper (w.map ξ)) R k ≤
      TailCuts.score (TailCuts.lower (w.map ξ)) (TailCuts.upper (w.map ξ)) R j)
    (C a : ℝ) (hupdate : ENNReal.ofReal (Real.exp C) • (κ ∘ₘ w) ≤ w')
    (Z : X × X → ℝ)
    (hZi : Integrable Z ((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))))
    (hZ0 : ∀ p, 0 ≤ Z p)
    (hp0 : ∀ᵐ p ∂((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))), 0 < outwardMass κ ξ p)
    (hp : ∀ᵐ p ∂((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))),
      -a-Z p ≤ Real.log (outwardMass κ ξ p)) :
    C-a-(∫ p, Z p ∂((normalizedRestriction w (ξ ⁻¹' Set.Iic j)).prod
      (normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R)))))-Real.log 2 ≤
      Real.log (statistic w' R) - Real.log (statistic (w.map ξ) R) := by
  have hξ : Measurable ξ := measurable_of_countable _
  have hwfull := TailSampling.coordinate_atom_pos w ξ hξ hsurj hfull
  have hLp := TailCuts.lower_pos (w.map ξ) hwfull j
  have hUp := TailCuts.upper_pos (w.map ξ) hwfull (j+R)
  rw [TailCuts.lower,Measure.real,Measure.map_apply hξ measurableSet_Iic] at hLp
  rw [TailCuts.upper,Measure.real,Measure.map_apply hξ measurableSet_Ici] at hUp
  have hL : w (ξ ⁻¹' Set.Iic j) ≠ 0 := (ENNReal.toReal_pos_iff.mp hLp).1.ne'
  have hU : w (ξ ⁻¹' Set.Ici (j+R)) ≠ 0 := (ENNReal.toReal_pos_iff.mp hUp).1.ne'
  let α := normalizedRestriction w (ξ ⁻¹' Set.Iic j)
  let β := normalizedRestriction w (ξ ⁻¹' Set.Ici (j+R))
  let : IsProbabilityMeasure α := normalizedRestriction_probability w _ hL
  let : IsProbabilityMeasure β := normalizedRestriction_probability w _ hU
  have hT := statistic_pos (w.map ξ) hwfull R
  have hTls : statistic (w.map ξ) R ≤ w.real (ξ ⁻¹' Set.Iic j) := by
    rw [statistic_eq_max _ R j hj]
    exact (min_le_left _ _).trans_eq (by
      simp only [TailCuts.lower,Measure.real,Measure.map_apply hξ measurableSet_Iic])
  have hTus : statistic (w.map ξ) R ≤ w.real (ξ ⁻¹' Set.Ici (j+R)) := by
    rw [statistic_eq_max _ R j hj]
    exact (min_le_right _ _).trans_eq (by
      simp only [TailCuts.upper,Measure.real,Measure.map_apply hξ measurableSet_Ici])
  have hdl := continued_tail_dominated κ w w' _ hL hTls hupdate
  have hdu := continued_tail_dominated κ w w' _ hU hTus hupdate
  have hgap : ∀ᵐ p ∂α.prod β, R ≤ ξ p.2 - ξ p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((Set.to_countable _).measurableSet)).mpr
    filter_upwards [normalizedRestriction_supported w _ (hξ measurableSet_Iic)] with x hx
    filter_upwards [normalizedRestriction_supported w _ (hξ measurableSet_Ici)] with y hy
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_Ici] at hx hy
    omega
  have hPi : Integrable (outwardMass κ ξ) (α.prod β) := by
    apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]
      unfold outwardMass
      rw [abs_of_nonneg measureReal_nonneg]
      apply real_le_one_of_total_le_one
      rw [←Set.univ_prod_univ,Measure.prod_prod]
      exact (mul_le_of_le_one_left (by positivity) (hκ _)).trans (hκ _)
  obtain ⟨hQ,hlog⟩ := log_integral_lower (α.prod β) Z (outwardMass κ ξ) a
    hZi (Eventually.of_forall hZ0) hPi hp0 hp
  exact log_statistic_grows (κ ∘ₘ α) (κ ∘ₘ β) (w.map ξ) w'
    (real_le_one_of_total_le_one _ (comp_total_le_one κ hκ α) _)
    (real_le_one_of_total_le_one _ (comp_total_le_one κ hκ β) _)
    R hT hQ (ordered_stream_mass_lower κ hκ ξ α β R hgap) hlog
    (fun j => stream_real_lower _ w' (mul_pos (Real.exp_pos C) hT).le hdl (Set.Iic j))
    (fun j => stream_real_lower _ w' (mul_pos (Real.exp_pos C) hT).le hdu (Set.Ici j))

end TailGrowth

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ProfileGrowth2
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma horizontal_coordinate_surjective {d : ℕ} (e : Direction d) (f : Fin d)
    (hef : e.1 ≠ f) : Function.Surjective (fun x : HorizontalLayer e => x.1 f) := by
  intro z
  refine ⟨⟨Pi.single f z, ?_⟩, ?_⟩
  · simp [Ne.symm hef]
  · simp

lemma horizontalCoordinateKernel_total {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) (x : HorizontalLayer e) :
    horizontalCoordinateKernel e f H ω x Set.univ ≤ 1 := by
  rw [horizontalCoordinateKernel_apply, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _

lemma coordinate_outwardMass {d : ℕ} (e : Direction d) (f : Fin d)
    (H : ℕ) (ω : Environment d) (p : HorizontalLayer e × HorizontalLayer e) :
    TailGrowth.outwardMass (horizontalCoordinateKernel e f H ω) (fun x => x.1 f) p =
      outwardKernelMass e (f,true) H (p.1.1,p.2.1) ω := by
  unfold TailGrowth.outwardMass Measure.real
  rw [horizontalCoordinateKernel_apply, horizontalCoordinateKernel_apply,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet)]
  unfold outwardKernelMass rawPairEndpointLaw
  congr 2
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    signedCoordinate, reduceIte, Pi.sub_apply, Int.cast_sub]
  exact_mod_cast Iff.rfl

lemma horizontal_pair_height {d : ℕ} (e : Direction d)
    (p : HorizontalLayer e × HorizontalLayer e) :
    dot (realPosition p.1.1) (realPosition (step e)) =
      dot (realPosition p.2.1) (realPosition (step e)) := by
  rw [dot_signed_direction, dot_signed_direction]
  simp only [signedCoordinate, p.1.2, p.2.2, Int.cast_zero, neg_zero, ite_self]

theorem actual_profile_tail_growth {d : ℕ} (e : Direction d) (f : Fin d)
    (hef : e.1 ≠ f) (A : ℝ) (ω : Environment d)
    (hω : ∀ x : Lattice d × Lattice d,
      dot (realPosition x.1) (realPosition (step e)) =
        dot (realPosition x.2) (realPosition (step e)) →
      ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x ω ∧
        -Real.log (outwardKernelMass e (f,true) (t+1) x ω) ≤
          2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x ω)
    (H : ℕ) (hH : 0 < H)
    (w : Measure (HorizontalLayer e)) [IsFiniteMeasure w]
    (hfull : ∀ x, 0 < w.real {x}) (w' : Measure ℤ) [IsFiniteMeasure w']
    (R j : ℤ) (hj : ∀ k, TailCuts.score (TailCuts.lower (w.map (fun x => x.1 f)))
      (TailCuts.upper (w.map (fun x => x.1 f))) R k ≤
      TailCuts.score (TailCuts.lower (w.map (fun x => x.1 f)))
        (TailCuts.upper (w.map (fun x => x.1 f))) R j)
    (C : ℝ) (hupdate : ENNReal.ofReal (Real.exp C) •
      (horizontalCoordinateKernel e f H ω ∘ₘ w) ≤ w')
    (hZi : Integrable (fun p : HorizontalLayer e × HorizontalLayer e =>
      outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω)
      ((TailGrowth.normalizedRestriction w {x | x.1 f ≤ j}).prod
        (TailGrowth.normalizedRestriction w {x | j+R ≤ x.1 f}))) :
    C-2*A*Real.log (1+(H:ℝ))-
      (∫ p : HorizontalLayer e × HorizontalLayer e,
        outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω
        ∂((TailGrowth.normalizedRestriction w {x | x.1 f ≤ j}).prod
          (TailGrowth.normalizedRestriction w {x | j+R ≤ x.1 f}))) - Real.log 2 ≤
      Real.log (TailGrowth.statistic w' R) -
        Real.log (TailGrowth.statistic (w.map (fun x => x.1 f)) R) := by
  have hpoint (p : HorizontalLayer e × HorizontalLayer e) :
      0 < outwardKernelMass e (f,true) H (p.1.1,p.2.1) ω ∧
        -Real.log (outwardKernelMass e (f,true) H (p.1.1,p.2.1) ω) ≤
          2*A*Real.log (1+(H:ℝ))+outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω := by
    have hh := hω (p.1.1,p.2.1) (horizontal_pair_height e p) (H-1)
    have hn : H-1+1=H := by omega
    have hnR : ((H-1:ℕ):ℝ)+2 = 1+(H:ℝ) := by
      have heq := congrArg (fun n : ℕ => (n:ℝ)) hn
      push_cast at heq
      linarith
    simpa only [hn,hnR] using hh
  apply TailGrowth.profile_tail_growth w w' (fun x => x.1 f)
    (horizontal_coordinate_surjective e f hef) hfull
    (horizontalCoordinateKernel e f H ω) (horizontalCoordinateKernel_total e f H ω)
    R j hj C (2*A*Real.log (1+(H:ℝ))) hupdate
    (fun p => outwardCanonicalExcess e (f,true) A (p.1.1,p.2.1) ω) hZi
  · intro p
    exact canonicalLogExcess_nonneg _ _ ω
  · exact Eventually.of_forall fun p => (coordinate_outwardMass e f H ω p) ▸ (hpoint p).1
  · apply Eventually.of_forall
    intro p
    rw [coordinate_outwardMass]
    linarith [(hpoint p).2]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProperProfile
attribute [-instance] _root_.OAI.DirectionalTransience.coordinateProfile_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

lemma properProfile_nonempty (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (G : ArrayGrowthSector e (L.law : Measure (ActualEpisodeArray e))) : Nonempty (ProperProfile e) := by
  have := markedArrayLaw_probability e (L.law : Measure (ActualEpisodeArray e)) G.event G.positive_event.ne'
  obtain ⟨p,hp⟩ := (L.marked_profile_proper hue htrans G).exists
  exact ⟨⟨_,hp⟩⟩

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]
    [MeasurableSingletonClass X]

lemma lowerKernel_markov (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (lowerKernel w ξ hξ j hj) := by
  apply cutKernel_markov
  · intro d
    have ht := TailCuts.lower_pos ((w d).map ξ)
      (coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)) (j d)
    rw [TailCuts.lower, Measure.real, Measure.map_apply hξ measurableSet_Iic] at ht
    exact (ENNReal.toReal_pos_iff.mp ht).1.ne'
  · exact fun d => measure_ne_top _ _

lemma upperKernel_markov (w : Kernel D X) [IsFiniteKernel w]
    (ξ : X → ℤ) (hξ : Measurable ξ) (hsurj : Function.Surjective ξ)
    (hfull : ∀ d x, 0 < (w d).real {x}) (j : D → ℤ) (hj : Measurable j) :
    IsMarkovKernel (upperKernel w ξ hξ j hj) := by
  apply cutKernel_markov
  · intro d
    have ht := TailCuts.upper_pos ((w d).map ξ)
      (coordinate_atom_pos (w d) ξ hξ hsurj (hfull d)) (j d)
    rw [TailCuts.upper, Measure.real, Measure.map_apply hξ measurableSet_Ici] at ht
    exact (ENNReal.toReal_pos_iff.mp ht).1.ne'
  · exact fun d => measure_ne_top _ _

end TailSampling

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma profilePairKernel_integral {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) (z : D) (F : ZeroHeightPair e → ℝ) :
    (∫ p, F p ∂profilePairKernel e f w R j hj z) =
      ∫ p : HorizontalLayer e × HorizontalLayer e, F (horizontalPair e p)
        ∂((TailGrowth.normalizedRestriction (w z) {x | x.1 f ≤ j z}).prod
          (TailGrowth.normalizedRestriction (w z) {x | j z+R ≤ x.1 f})) := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  rw [profilePairKernel, Kernel.map_apply _ (measurable_of_countable _),
    integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    Kernel.prod_apply]
  rfl

lemma profilePairKernel_integrable {d : ℕ} (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (hfull : ∀ z x, 0 < (w z).real {x}) (R : ℤ) (j : D → ℤ) (hj : Measurable j) (z : D)
    (F : ZeroHeightPair e → ℝ) :
    Integrable F (profilePairKernel e f w R j hj z) ↔
      Integrable (fun p : HorizontalLayer e × HorizontalLayer e => F (horizontalPair e p))
        ((TailGrowth.normalizedRestriction (w z) {x | x.1 f ≤ j z}).prod
          (TailGrowth.normalizedRestriction (w z) {x | j z+R ≤ x.1 f})) := by
  have := TailSampling.lowerKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull j hj
  have := TailSampling.upperKernel_markov w (fun x => x.1 f) (measurable_of_countable _)
    (horizontal_coordinate_surjective e f hef) hfull (fun z => j z+R) (hj.add_const R)
  rw [profilePairKernel, Kernel.map_apply _ (measurable_of_countable _), Kernel.prod_apply]
  exact integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DensityTransfer
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailDecorrelation

lemma controlled_ae {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ρ : Measure X) {T : Ω → X} (hT : Measurable T)
    {g : X → ℝ} (hg : Measurable g)
    (hLaw : μ.map T = ρ.withDensity (fun x => ENNReal.ofReal (g x)))
    {p : X → Prop} (hp : ∀ᵐ x ∂ρ, g x ≠ 0 → p x) :
    ∀ᵐ ω ∂μ, p (T ω) := by
  have hp' : ∀ᵐ x ∂ρ.withDensity (fun x => ENNReal.ofReal (g x)), p x := by
    apply (ae_withDensity_iff hg.ennreal_ofReal).mpr
    filter_upwards [hp] with x hx hne
    exact hx (fun heq => hne (by simp [heq]))
  have hpres : MeasurePreserving T μ (ρ.withDensity (fun x => ENNReal.ofReal (g x))) := ⟨hT,hLaw⟩
  exact hpres.quasiMeasurePreserving.ae hp'

lemma controlled_integral {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ρ : Measure X) {T : Ω → X} (hT : Measurable T)
    {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hLaw : μ.map T = ρ.withDensity (fun x => ENNReal.ofReal (g x)))
    {F : X → ℝ} (hi : Integrable (fun x => g x * F x) ρ) :
    Integrable (fun ω => F (T ω)) μ ∧
      (∫ ω, F (T ω) ∂μ) = ∫ x, g x * F x ∂ρ := by
  have htop : ∀ᵐ x ∂ρ, ENNReal.ofReal (g x) < ∞ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hFi : Integrable F (ρ.withDensity (fun x => ENNReal.ofReal (g x))) := by
    apply (integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal htop).mpr
    simpa only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul] using hi
  have hpres : MeasurePreserving T μ (ρ.withDensity (fun x => ENNReal.ofReal (g x))) := ⟨hT,hLaw⟩
  refine ⟨(hpres.integrable_comp hFi.aestronglyMeasurable).mpr hFi,?_⟩
  have hFm : AEStronglyMeasurable F (μ.map T) := hLaw ▸ hFi.aestronglyMeasurable
  rw [← integral_map hT.aemeasurable hFm, hLaw,
    integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal htop]
  simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]

end TailDecorrelation

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryProfile
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma profile_statistic_nonpos {d : ℕ} (e : Direction d) (f : Fin d)
    {D : Type*} [MeasurableSpace D] (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (htotal : ∀ z, w z Set.univ ≤ 1) (z : D) (R : ℤ) :
    Real.log (TailGrowth.statistic (coordinateProfile e f w z) R) ≤ 0 := by
  have hnon : 0 ≤ TailGrowth.statistic (coordinateProfile e f w z) R := by
    apply le_trans _ (TailGrowth.score_le_statistic _ R 0)
    exact le_min (measureReal_nonneg) (measureReal_nonneg)
  apply Real.log_nonpos hnon
  apply (TailGrowth.statistic_le_mass _ _).trans
  rw [coordinateProfile_apply,Measure.real,
    Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using htotal z)

lemma iterate_identDistrib {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {F : Ω → Y} (hF : Measurable F) (n : ℕ) :
    IdentDistrib (fun ω => F (T^[n] ω)) F μ μ := by
  refine ⟨(hF.comp (hT.iterate n).measurable).aemeasurable,hF.aemeasurable,?_⟩
  change Measure.map (F ∘ T^[n]) μ = _
  rw [←Measure.map_map hF (hT.iterate n).measurable, (hT.iterate n).map_eq]

theorem stationary_profile_mean_nonpos {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (Ω D : Type) [MeasurableSpace Ω] [MeasurableSpace D]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w]
    (S : StationaryProfileSystem ν e f Ω D μ w) :
    (∫ ω, S.c ω ∂μ) ≤ 0 := by
  classical
  obtain ⟨A,hA,hpoint,M,hM,hdec⟩ := actual_profile_tail_decorrelation ν hue e f hef htrans
  let δ := μ.map S.data
  let : IsProbabilityMeasure δ :=
    (Measure.isProbabilityMeasure_map_iff S.measurable_data.aemeasurable).2 inferInstance
  let X : ℕ → ℕ → Ω → ℝ := fun n R ω =>
    Real.log (TailGrowth.statistic (coordinateProfile e f w (S.data (S.T^[n] ω))) (R:ℤ))
  have hXa (R : ℕ) : Measurable (fun ω => X 0 R ω) := by
    exact Real.measurable_log.comp ((TailGrowth.measurable_statistic
      (coordinateProfile e f w) (R:ℤ)).comp S.measurable_data)
  have hXid (n R : ℕ) : IdentDistrib (X 0 R) (X n R) μ μ := by
    exact (iterate_identDistrib μ S.preserving (hXa R) n).symm
  have hXnon (n R : ℕ) : ∀ᵐ ω ∂μ, X n R ω ≤ 0 :=
    Eventually.of_forall fun ω => profile_statistic_nonpos e f w S.total _ _
  have hpos : ∀ᵐ ω ∂μ, ∀ i, 1 ≤ S.h (S.T^[i] ω) :=
    ae_all_iff.mpr fun i => (S.preserving.iterate i).quasiMeasurePreserving.ae S.positive_h
  have hwindow (n : ℕ) (hn : 0 < n) : ∃ Z : ℕ → Ω → ℝ,
      (∀ R, Integrable (Z R) μ) ∧
      (∀ᶠ R in atTop, (∫ ω, Z R ω ∂μ) ≤ M+1) ∧
      (∀ R, ∀ᵐ ω ∂μ,
        (∑ i ∈ Finset.range n, S.c (S.T^[i] ω)) -
          (2*A)*Real.log (1+∑ i ∈ Finset.range n, (S.h (S.T^[i] ω):ℝ)) -
          Z R ω - Real.log 2 ≤ X n R ω-X 0 R ω) := by
    obtain ⟨g,hgm,hg0,hgi,hg1,hgH,hLaw⟩ := S.finite_entropy n hn
    obtain ⟨j,hj,hmax,hsect,hint,hmean,hlim⟩ := hdec D δ w S.full g hgm hg0 hgi hg1 hgH
    let κ := fun R : ℕ => profilePairKernel e f w (R:ℤ) (j R) (hj R)
    let F : ℕ → D × Environment d → ℝ := fun R z =>
      ∫ p : ZeroHeightPair e, outwardCanonicalExcess e (f,true) A p.1 z.2 ∂κ R z.1
    let V : Ω → D × Environment d := fun ω => (S.data ω,S.field n ω)
    have hVm : Measurable V := S.measurable_data.prodMk (S.measurable_field n)
    have hFi (R : ℕ) := TailDecorrelation.controlled_integral μ
      (δ.prod (environmentLaw ν)) hVm hgm hg0 hLaw (hint R)
    refine ⟨fun R ω => F R (V ω),fun R => (hFi R).1,?_,?_⟩
    · filter_upwards [hmean 1 (by norm_num)] with R hR
      exact ((hFi R).2).trans_le hR
    · intro R
      have hs := TailDecorrelation.controlled_ae μ (δ.prod (environmentLaw ν))
        hVm hgm hLaw (hsect R)
      have hp : ∀ᵐ ω ∂μ,
          ∀ x : Lattice d × Lattice d,
            dot (realPosition x.1) (realPosition (step e)) =
              dot (realPosition x.2) (realPosition (step e)) →
            ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x (S.field n ω) ∧
              -Real.log (outwardKernelMass e (f,true) (t+1) x (S.field n ω)) ≤
                2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x (S.field n ω) := by
        have hpref := (Measure.quasiMeasurePreserving_snd (μ := δ) (ν := environmentLaw ν)).ae hpoint
        exact TailDecorrelation.controlled_ae μ (δ.prod (environmentLaw ν)) hVm hgm hLaw
          (hpref.mono fun _ hz _ => hz)
      filter_upwards [S.update n hn,hs,hp,hpos] with ω hupdate hsec hpω hhω
      have hH : 0 < ∑ i ∈ Finset.range n, S.h (S.T^[i] ω) := by
        exact lt_of_lt_of_le (Nat.succ_le_iff.mp (hhω 0))
          (Finset.single_le_sum (s := Finset.range n) (f := fun i => S.h (S.T^[i] ω))
            (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hn))
      have hsec' := (profilePairKernel_integrable e f hef w S.full (R:ℤ)
        (j R) (hj R) (S.data ω)
        (fun p : ZeroHeightPair e => outwardCanonicalExcess e (f,true) A p.1 (S.field n ω))).mp hsec
      have hgrowth := actual_profile_tail_growth e f hef A (S.field n ω) hpω
        (∑ i ∈ Finset.range n, S.h (S.T^[i] ω)) hH (w (S.data ω)) (S.full _)
        ((coordinateProfile e f w (S.data (S.T^[n] ω))).map (fun x => x+S.offset n ω))
        (R:ℤ) (j R (S.data ω)) (hmax (S.data ω) R)
        (∑ i ∈ Finset.range n, S.c (S.T^[i] ω)) hupdate hsec'
      rw [TailGrowth.statistic_translate] at hgrowth
      have heq := profilePairKernel_integral e f hef w S.full (R:ℤ)
        (j R) (hj R) (S.data ω)
        (fun p : ZeroHeightPair e => outwardCanonicalExcess e (f,true) A p.1 (S.field n ω))
      dsimp only [horizontalPair] at heq
      rw [←heq] at hgrowth
      simpa only [Nat.cast_sum, X, Function.iterate_zero, id_eq, coordinateProfile_apply,
        F,V,κ] using hgrowth
  choose W hWi hWmean hWgrowth using fun n => hwindow (n+1) (Nat.succ_pos n)
  let Z : ℕ → ℕ → Ω → ℝ := fun n => match n with
    | 0 => fun _ _ => 0
    | k+1 => W k
  have hZint (n R : ℕ) : Integrable (Z n R) μ := by
    cases n with
    | zero => exact integrable_const 0
    | succ k => exact hWi k R
  have hZmean (n : ℕ) : ∀ᶠ R in atTop, (∫ ω, Z n R ω ∂μ) ≤ M+1 := by
    cases n with
    | zero => exact Eventually.of_forall fun R => by simp only [Z,integral_zero] <;> linarith
    | succ k => exact hWmean k
  have hgrowth (n R : ℕ) : ∀ᵐ ω ∂μ,
      (∑ i ∈ Finset.range n, S.c (S.T^[i] ω)) -
        (2*A)*Real.log (1+∑ i ∈ Finset.range n, (S.h (S.T^[i] ω):ℝ)) -
        Z n R ω-Real.log 2 ≤ X n R ω-X 0 R ω := by
    cases n with
    | zero =>
      apply Eventually.of_forall
      intro ω
      simp only [Finset.range_zero,Finset.sum_empty,add_zero,Real.log_one,mul_zero,
        Z,zero_sub,sub_self]
      exact neg_nonpos.mpr (Real.log_nonneg (by norm_num))
    | succ k => exact hWgrowth k R
  apply stationary_tail_growth_obstruction μ (c := fun i ω => S.c (S.T^[i] ω))
    (h := fun i ω => (S.h (S.T^[i] ω):ℝ)) (X := X) (Z := Z)
    S.integrable_c (fun i => iterate_identDistrib μ S.preserving S.measurable_c i)
    (Eventually.of_forall fun ω i => Nat.cast_nonneg _) (fun i => ?_)
    S.integrable_log_h hXid hXnon hZint (2*A) (M+1) hZmean hgrowth
  exact iterate_identDistrib μ S.preserving ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp S.measurable_h) i

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryProfile2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

namespace StationaryArrayLaw
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν] {e : Direction d}

theorem impossible (L : StationaryArrayLaw ν e) (hue : UniformElliptic ν)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (f : Fin d) (hef : e.1≠f) : False := by
  obtain ⟨G⟩ := L.growth_sector hue htrans
  obtain ⟨w₀⟩ := L.properProfile_nonempty hue htrans G
  let μ := markedArrayLaw e (L.law : Measure (ActualEpisodeArray e)) G.event
  have : IsProbabilityMeasure μ := markedArrayLaw_probability e _ G.event G.positive_event.ne'
  let η := μ.prod (environmentLaw ν)
  let S := L.actualProfileSystem hue htrans G w₀ f hef
  have hn := stationary_profile_mean_nonpos ν hue e f hef htrans (FullMarkedArray e)
    (ProperProfile e) η (properProfileKernel e) S
  have hz : S.c =ᵐ[η] 0 := (integral_eq_zero_iff_of_nonneg_ae S.nonneg_c S.integrable_c).mp
    (le_antisymm hn (integral_nonneg_of_ae S.nonneg_c))
  have hzero : ∀ᵐ p ∂η, ∀ i : ℕ, S.c (S.T^[i] p)=0 :=
    ae_all_iff.mpr fun i => (S.preserving.iterate i).quasiMeasurePreserving.ae hz
  have hgrowth := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event
    G.measurable_event G.growth
  have hmarks := markedArrayLaw_ae e (L.law : Measure (ActualEpisodeArray e)) G.event
    G.measurable_event (L.finite_marks.mono fun Y h _ => h)
  have hF := Measure.quasiMeasurePreserving_fst (μ := μ) (ν := environmentLaw ν)
  obtain ⟨p,hp0,hpg,hpm⟩ := (hzero.and ((hF.ae hgrowth).and (hF.ae hmarks))).exists
  have hwin (n : ℕ) : (arrayWindowCost e 0 n p.1.1).toReal=0 := by
    rw [arrayWindowCost_toReal e p.1.1 (fun j => (hpm j).2.2.2.ne)]
    apply Finset.sum_eq_zero
    intro i hi
    have h := hp0 i
    change arrayRealCost e (((fullMarkedShift e)^[i] p).1.1)=0 at h
    simpa only [fullMarkedShift_iterate_fst,markedShift_iterate_fst] using h
  obtain ⟨k,hk⟩ := hpg.exists
  rw [hwin] at hk
  exact (not_lt_of_ge (mul_nonneg G.positive_ζ.le (Nat.cast_nonneg _))) hk

end StationaryArrayLaw
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

theorem crossing_estimate {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) (D : ℝ) (hD : 0≤D) :
    ∀ᶠ N : ℕ in atTop, (environmentLaw ν).real (badCrossingEvent e N (1/2)) < (N:ℝ)^(-D) := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨f,hf⟩ := exists_ne e.1
  obtain ⟨C⟩ := operational_constants_exist ν hue e (f,true) (Ne.symm hf) htrans D hD
  by_contra hh
  have hfreq : ∃ᶠ N : ℕ in atTop, (N:ℝ)^(-D)≤(environmentLaw ν).real (badCrossingEvent e N (1/2)) := by
    simpa only [not_lt] using not_eventually.mp hh
  have hfloor : ∀ᶠ N : ℕ in atTop, C.sfloor≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlog : Tendsto (fun N : ℕ => (1/2:ℝ)*Real.log (N:ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop, 32*C.b≤(1/2:ℝ)*Real.log (N:ℝ) :=
    hlog.eventually (eventually_ge_atTop _)
  have hex := frequently_atTop.mp (hfreq.and_eventually (hfloor.and hlarge))
  choose Ns hNs hmass hfloor hlarge using hex
  obtain ⟨L⟩ := C.bad_stationary_array_law (Ne.symm hf) hD Ns
    (tendsto_atTop_mono hNs tendsto_id) hfloor hlarge hmass
  exact L.impossible hue htrans f (Ne.symm hf)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_HittingIteration
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma quenched_hit_future_bound {d : ℕ} (ω : Environment d) (x : Lattice d)
    {S T : Set (Lattice d)} (hST : Disjoint S T) (B : Lattice d → Set (Path d))
    (hB : ∀ y, MeasurableSet (B y)) (C : ℝ≥0∞)
    (hC : ∀ y ∈ T, quenchedKernel (ω,y) (B y) ≤ C) :
    quenchedKernel (ω,x) (⋃ n, HitAt S T n ∩ FutureEvent B n) ≤
      C * quenchedKernel (ω,x) (Hit S T) := by
  rw [← hitKernel_future ω x hST B hB,← hitKernel_total hST]
  calc
    _ ≤ ∫⁻ y, C ∂hitKernel S T (ω,x) := by
      apply lintegral_mono_ae
      filter_upwards [hitKernel_ae_target S T (ω,x)] with y hy
      exact hC y hy
    _ = _ := by simp

lemma hit_split_subset {d : ℕ} (S T U : Set (Lattice d)) (hST : Disjoint S T) (X : Path d)
    (h : X ∈ Hit S T) (hu : ∃ k, X k ∈ U ∧ ∀ j < k, X j ∈ S) :
    X ∈ ⋃ n, HitAt (S \ U) U n ∩ FutureEvent (fun _ => Hit S T) n := by
  obtain ⟨k,hkU,hkS⟩ := hu
  have hex : ∃ j, X j ∈ U := ⟨k,hkU⟩
  let n := Nat.find hex
  have hnU : X n ∈ U := Nat.find_spec hex
  have hnk : n ≤ k := Nat.find_min' hex hkU
  have hnS : ∀ j < n, X j ∈ S \ U := fun j hj => ⟨hkS j (hj.trans_le hnk),Nat.find_min hex hj⟩
  obtain ⟨m,hmT,hmS⟩ := Set.mem_iUnion.mp h
  by_cases hnm : n ≤ m
  · refine Set.mem_iUnion.mpr ⟨n,⟨hnU,hnS⟩,?_⟩
    change (fun j => X (n+j)) ∈ Hit S T
    refine Set.mem_iUnion.mpr ⟨m-n,?_,?_⟩
    · simpa [Nat.add_sub_of_le hnm] using hmT
    · intro j hj
      exact hmS (n+j) (by omega)
  · exact False.elim (Set.disjoint_left.mp hST (hkS m (by omega)) hmT)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_DescendingTrials
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma signedHeight_step_ge {d : ℕ} (e : Direction d) (x : Lattice d) (f : Direction d) :
    signedHeight e x-1 ≤ signedHeight e (x+step f) := by
  simp only [signedHeight,Pi.add_apply,step]
  split <;> split <;> (try split) <;> omega

lemma integer_first_descent (z : ℕ → ℤ) (k : ℕ) (m : ℕ)
    (h0 : z 0 = (k:ℤ)+1) (hm : z m < 0)
    (hstep : ∀ n, z n-1 ≤ z (n+1)) :
    ∃ n < m, z n = (k:ℤ) ∧ ∀ j < n, (k:ℤ)+1 ≤ z j := by
  have hex : ∃ j, z j < (k:ℤ)+1 := ⟨m,by omega⟩
  let n := Nat.find hex
  have hn : z n < (k:ℤ)+1 := Nat.find_spec hex
  have hnm : n ≤ m := Nat.find_min' hex (by omega)
  have hpre : ∀ j < n, (k:ℤ)+1 ≤ z j := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hn0 : 0 < n := by
    by_contra hh
    have hh0 : n=0 := by omega
    rw [hh0,h0] at hn
    omega
  have hp := hpre (n-1) (by omega)
  have hs := hstep (n-1)
  have hnEq : n-1+1=n := by omega
  rw [hnEq] at hs
  have he : z n = (k:ℤ) := by omega
  have hlt : n < m := by
    by_contra hh
    have hEq : n=m := by omega
    rw [hEq] at he
    omega
  exact ⟨n,hlt,he,hpre⟩

lemma down_hit_disjoint_cross {d : ℕ} (e : Direction d) (N : ℕ)
    (S T : Set (Lattice d)) (x : Lattice d)
    (hx : 0 ≤ signedHeight e x)
    (hS : ∀ y ∈ S, signedHeight e y ≤ (N:ℤ))
    (hT : ∀ y ∈ T, signedHeight e y < signedHeight e x) :
    Disjoint (Hit S T) (Cross (realPosition (step e)) x (N+1)) := by
  apply Set.disjoint_left.mpr
  intro X hdown hup
  obtain ⟨n,hnT,hnS⟩ := Set.mem_iUnion.mp hdown
  obtain ⟨m,hmH,hmD⟩ := hup
  simp only [signedHeight_projection] at hmH hmD
  by_cases hmn : m < n
  · have hb := hS (X m) (hnS m hmn)
    have hb' : (signedHeight e (X m):ℝ) ≤ (N:ℝ) := by exact_mod_cast hb
    have hx' : (0:ℝ) ≤ signedHeight e x := by exact_mod_cast hx
    linarith
  · have ht := hT (X n) hnT
    have ht' : (signedHeight e (X n):ℝ) < signedHeight e x := by exact_mod_cast ht
    by_cases hnm : n < m
    · have hl := hmD n hnm
      linarith
    · have heq : n=m := by omega
      rw [heq] at ht'
      have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
      linarith

lemma down_hit_mass_le {d : ℕ} (ω : Environment d) (e : Direction d) (N : ℕ)
    (S T : Set (Lattice d)) (x : Lattice d)
    (hx : 0 ≤ signedHeight e x)
    (hS : ∀ y ∈ S, signedHeight e y ≤ (N:ℤ))
    (hT : ∀ y ∈ T, signedHeight e y < signedHeight e x) (δ : ℝ≥0∞)
    (hδ : δ ≤ crossingQuenched (realPosition (step e)) x (N+1) ω) :
    quenchedKernel (ω,x) (Hit S T) ≤ 1-δ := by
  have hd := down_hit_disjoint_cross e N S T x hx hS hT
  calc
    _ ≤ quenchedKernel (ω,x) (Cross (realPosition (step e)) x (N+1))ᶜ :=
      measure_mono (Set.disjoint_left.mp hd)
    _ = 1-crossingQuenched (realPosition (step e)) x (N+1) ω := by
      rw [measure_compl (measurableSet_cross _ _ _) (measure_ne_top _ _),measure_univ]
      rfl
    _ ≤ _ := tsub_le_tsub_left hδ _

theorem quenched_descending_trials {d : ℕ} (ω : Environment d) (e : Direction d)
    (N : ℕ) (B : Set (Lattice d)) (δ : ℝ≥0∞)
    (hgood : ∀ y ∈ BoxStrip e N B,
      δ ≤ crossingQuenched (realPosition (step e)) y (N+1) ω) :
    ∀ k : ℕ, ∀ x ∈ B, signedHeight e x = (k:ℤ) → k ≤ N →
      quenchedKernel (ω,x) (Hit (BoxStrip e N B) {y | signedHeight e y < 0}) ≤ (1-δ)^(k+1) := by
  let S := BoxStrip e N B
  let T : Set (Lattice d) := {y | signedHeight e y < 0}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => not_lt_of_ge hs.2.1 ht)
  intro k
  induction k with
  | zero =>
    intro x hx hx0 hk
    simpa only [zero_add,pow_one] using down_hit_mass_le ω e N S T x
      (by omega) (fun y hy => hy.2.2) (fun y hy => by change signedHeight e y < 0 at hy; omega) δ
      (hgood x ⟨hx,by omega,by omega⟩)
  | succ k ih =>
    intro x hx hxk hkN
    let U : Set (Lattice d) := {y | y ∈ B ∧ signedHeight e y = (k:ℤ)}
    have hsub : ∀ᵐ X ∂quenchedKernel (ω,x),
        X ∈ Hit S T → X ∈ ⋃ n, HitAt (S \ U) U n ∩ FutureEvent (fun _ => Hit S T) n := by
      filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hNN hX
      obtain ⟨m,hm,hmS⟩ := Set.mem_iUnion.mp hX
      have hstep (n : ℕ) : signedHeight e (X n)-1 ≤ signedHeight e (X (n+1)) := by
        obtain ⟨f,hf⟩ := hNN n
        rw [hf]; exact signedHeight_step_ge e (X n) f
      obtain ⟨n,hnm,hnEq,_⟩ := integer_first_descent (fun n => signedHeight e (X n)) k m
        (by rw [h0,hxk]; simp) hm hstep
      apply hit_split_subset S T U hST X hX
      exact ⟨n,⟨(hmS n hnm).1,hnEq⟩,fun j hj => hmS j (hj.trans hnm)⟩
    calc
      _ ≤ quenchedKernel (ω,x) (⋃ n, HitAt (S \ U) U n ∩ FutureEvent (fun _ => Hit S T) n) :=
        measure_mono_ae hsub
      _ ≤ (1-δ)^(k+1) * quenchedKernel (ω,x) (Hit (S \ U) U) :=
        quenched_hit_future_bound ω x Set.disjoint_sdiff_left (fun _ => Hit S T)
          (fun _ => measurableSet_hit S T) _ (fun y hy => ih y hy.1 hy.2 (by omega))
      _ ≤ (1-δ)^(k+1) * (1-δ) := by
        apply mul_le_mul_right
        exact down_hit_mass_le ω e N (S \ U) U x (by omega)
          (fun y hy => hy.1.2.2) (fun y hy => by change _ = _ at hxk; rw [hy.2,hxk]; omega) δ
          (hgood x ⟨hx,by omega,by omega⟩)
      _ = _ := (pow_succ _ _).symm

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_SpatialConfinement
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.independentPairLaw_probability _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measurableSet_stripExcursion {d : ℕ} (ℓ : Vector d) (H R : ℝ) :
    MeasurableSet (StripExcursion ℓ H R) := by
  simp only [StripExcursion, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro n
  refine (measurableSet_boundedHeightPrefix ℓ H n).inter (MeasurableSet.iUnion fun u => ?_)
  exact measurableSet_lt measurable_const ((measurable_of_countable (signedCoordinate u)).comp (measurable_pi_apply n))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingGap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measurableSet_crossingGap {d : ℕ} (e : Direction d) (N : ℕ) :
    MeasurableSet (CrossingGap e N) := (measurableSet_cross _ _ _).diff (measurableSet_cross _ _ _)

lemma signedHeight_zero {d : ℕ} (e : Direction d) : signedHeight e (0 : Lattice d) = 0 := by
  simp [signedHeight]

lemma confined_crossingGap_split {d : ℕ} (e : Direction d) (N : ℕ) (hN : 0 < N)
    (R : ℝ) (B : Set (Lattice d))
    (hB : ∀ y, (∀ u : Direction d, signedCoordinate u y ≤ R) → y ∈ B)
    (X : Path d) (h0 : X 0=0) (hNN : ∀ n, ∃ f, X (n+1)=X n+step f)
    (ht : X ∈ TransientPaths (realPosition (step e)))
    (hgap : X ∈ CrossingGap e N)
    (hconf : X ∉ StripExcursion (realPosition (step e)) N R) :
    X ∈ ⋃ n, HitAt (BoxStrip e N B \ {y | signedHeight e y=(N:ℤ)})
      {y | y ∈ B ∧ signedHeight e y=(N:ℤ)} n ∩
      FutureEvent (fun _ => Hit (BoxStrip e N B) {y | signedHeight e y < 0}) n := by
  have hzero : dot (realPosition (0 : Lattice d)) (realPosition (step e))=0 := by
    rw [signedHeight_projection,signedHeight_zero,Int.cast_zero]
  have hex : ∃ j, signedHeight e (X j) < 0 := by
    by_contra hh
    push Not at hh
    apply hgap.2
    have hg := ht.eventually (eventually_ge_atTop ((N:ℝ)+1))
    obtain ⟨m,hm⟩ := hg.exists
    refine ⟨m,by rwa [hzero,zero_add],?_⟩
    intro i _
    rw [hzero,signedHeight_projection]
    exact_mod_cast hh i
  let j := Nat.find hex
  have hj : signedHeight e (X j) < 0 := Nat.find_spec hex
  have hp : ∀ i < j, 0 ≤ signedHeight e (X i) := fun i hi => le_of_not_gt (Nat.find_min hex hi)
  have htop : ∀ i < j, signedHeight e (X i) ≤ (N:ℤ) := by
    intro i hi
    by_contra hn
    have hn' : (N:ℤ)+1 ≤ signedHeight e (X i) := by omega
    apply hgap.2
    refine ⟨i,?_,?_⟩
    · rw [hzero,zero_add,signedHeight_projection]
      exact_mod_cast hn'
    · intro k hk
      rw [hzero,signedHeight_projection]
      exact_mod_cast hp k (hk.trans hi)
  have hbox : ∀ i < j, X i ∈ B := by
    intro i hi
    apply hB
    intro u
    by_contra hu
    apply hconf
    refine ⟨i,?_,u,lt_of_not_ge hu⟩
    intro k hk
    rw [signedHeight_projection]
    constructor
    · exact_mod_cast hp k (hk.trans_lt hi)
    · exact_mod_cast htop k (hk.trans_lt hi)
  obtain ⟨n,hn⟩ := noDrop_firstLayerHit_exists e X h0 hNN ht hN
  obtain ⟨m,hm,hmD⟩ := hgap.1
  have hnm : n ≤ m := by
    by_contra hh
    have hb := hn.2 m (by omega)
    rw [hzero,zero_add,signedHeight_projection] at hm
    have hb' : (signedHeight e (X m):ℝ) < (N:ℝ) := by exact_mod_cast hb
    linarith
  have hmj : m < j := by
    by_contra hh
    by_cases hjm : j < m
    · have hh := hmD j hjm
      rw [hzero,signedHeight_projection] at hh
      have hh' : (signedHeight e (X j):ℝ) < 0 := by exact_mod_cast hj
      linarith
    · have heq : m=j := by omega
      rw [heq,hzero,zero_add,signedHeight_projection] at hm
      have hh' : (signedHeight e (X j):ℝ) < 0 := by exact_mod_cast hj
      have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
      linarith
  have hnj := hnm.trans_lt hmj
  refine Set.mem_iUnion.mpr ⟨n,⟨⟨hbox n hnj,hn.1⟩,?_⟩,?_⟩
  · intro k hk
    exact ⟨⟨hbox k (hk.trans hnj),hp k (hk.trans hnj),htop k (hk.trans hnj)⟩,
      ne_of_lt (hn.2 k hk)⟩
  · change (fun k => X (n+k)) ∈ Hit (BoxStrip e N B) {y | signedHeight e y < 0}
    refine Set.mem_iUnion.mpr ⟨j-n,?_,?_⟩
    · simpa [Nat.add_sub_of_le hnj.le] using hj
    · intro k hk
      have hkj : n+k < j := by omega
      exact ⟨hbox (n+k) hkj,hp (n+k) hkj,htop (n+k) hkj⟩

lemma quenched_crossingGap_confined {d : ℕ} (ω : Environment d) (e : Direction d)
    (N : ℕ) (hN : 0 < N) (R : ℝ) (B : Set (Lattice d))
    (hB : ∀ y, (∀ u : Direction d, signedCoordinate u y ≤ R) → y ∈ B)
    (ht : ∀ᵐ X ∂quenchedKernel (ω,0), X ∈ TransientPaths (realPosition (step e)))
    (δ : ℝ≥0∞) (hgood : ∀ y ∈ BoxStrip e N B,
      δ ≤ crossingQuenched (realPosition (step e)) y (N+1) ω) :
    quenchedKernel (ω,0) (CrossingGap e N \ StripExcursion (realPosition (step e)) N R) ≤
      (1-δ)^(N+1) := by
  let S := BoxStrip e N B \ {y | signedHeight e y=(N:ℤ)}
  let T : Set (Lattice d) := {y | y ∈ B ∧ signedHeight e y=(N:ℤ)}
  have hST : Disjoint S T := Set.disjoint_left.mpr (fun _ hs ht => hs.2 ht.2)
  calc
    _ ≤ quenchedKernel (ω,0) (⋃ n, HitAt S T n ∩
        FutureEvent (fun _ => Hit (BoxStrip e N B) {y | signedHeight e y < 0}) n) := by
      apply measure_mono_ae
      filter_upwards [quenched_initial_ae (ω,0),quenched_nearest_neighbor (ω,0),ht] with X h0 hNN ht hX
      exact confined_crossingGap_split e N hN R B hB X h0 hNN ht hX.1 hX.2
    _ ≤ (1-δ)^(N+1)*quenchedKernel (ω,0) (Hit S T) :=
      quenched_hit_future_bound ω 0 hST _ (fun _ => measurableSet_hit _ _) _
        (fun y hy => quenched_descending_trials ω e N B δ hgood N y hy.1 hy.2 le_rfl)
    _ ≤ _ := by simpa using mul_le_mul_right (prob_le_one (μ := quenchedKernel (ω,0)) (s := Hit S T)) ((1-δ)^(N+1))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma mem_latticeBox {d : ℕ} (M : ℕ) (x : Lattice d) :
    x ∈ latticeBox M ↔ ∀ i, -(M:ℤ) ≤ x i ∧ x i ≤ M := by
  simp [latticeBox,Fintype.mem_piFinset]

lemma card_latticeBox {d : ℕ} (M : ℕ) : (latticeBox (d := d) M).card=(2*M+1)^d := by
  have h : ((M:ℤ)+1+(M:ℤ)).toNat=2*M+1 := by omega
  simp [latticeBox,Fintype.card_piFinset,Int.card_Icc,h]

lemma latticeBox_of_signed_bound {d : ℕ} (R : ℝ) (x : Lattice d)
    (hx : ∀ u : Direction d, signedCoordinate u x ≤ R) : x ∈ latticeBox ⌈R⌉₊ := by
  rw [mem_latticeBox]
  intro i
  have hp := hx (i,true)
  have hn := hx (i,false)
  simp [signedCoordinate] at hp hn
  have hc := Nat.le_ceil R
  constructor
  · have hh : -(⌈R⌉₊:ℝ) ≤ (x i:ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (x i:ℝ) ≤ (⌈R⌉₊:ℝ) := by linarith
    exact_mod_cast hh

lemma measurableSet_badBoxEvent {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ)
    (S : Finset (Lattice d)) : MeasurableSet (badBoxEvent e N β S) := by
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (measurable_crossingQuenched _ _ _).ennreal_toReal measurable_const

lemma badBox_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (N : ℕ) (β : ℝ) (S : Finset (Lattice d)) :
    (environmentLaw ν).real (badBoxEvent e N β S) ≤
      S.card*(environmentLaw ν).real (badCrossingEvent e N β) := by
  have htr (x : Lattice d) :
      (environmentLaw ν).real {ω | (crossingQuenched (realPosition (step e)) x N ω).toReal < (N:ℝ)^(-β)} =
      (environmentLaw ν).real (badCrossingEvent e N β) := by
    simp_rw [crossingQuenched_translation _ x]
    have hh := congrArg (fun μ : Measure (Environment d) => μ (badCrossingEvent e N β))
      (environment_translation ν x)
    rw [Measure.map_apply (by fun_prop) (badCrossingEvent_measurable e N β)] at hh
    exact congrArg ENNReal.toReal hh
  calc
    _ ≤ ∑ x ∈ S, (environmentLaw ν).real
        {ω | (crossingQuenched (realPosition (step e)) x N ω).toReal < (N:ℝ)^(-β)} :=
      measureReal_biUnion_finset_le _ _
    _ = _ := by simp [htr]

lemma good_box_crossing {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ)
    (S : Finset (Lattice d)) (ω : Environment d) (hω : ω ∉ badBoxEvent e N β S) :
    ∀ x ∈ S, ENNReal.ofReal ((N:ℝ)^(-β)) ≤ crossingQuenched (realPosition (step e)) x N ω := by
  intro x hx
  have hh : (N:ℝ)^(-β) ≤ (crossingQuenched (realPosition (step e)) x N ω).toReal := by
    by_contra hh
    exact hω (Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,lt_of_not_ge hh⟩⟩)
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (quenchedKernel (ω,x)) _)).mpr hh

lemma annealed_bound_bad_environment {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : Set (Path d)) (hA : MeasurableSet A) (E : Set (Environment d)) (hE : MeasurableSet E)
    (c : ℝ≥0∞) (hc : ∀ᵐ ω ∂environmentLaw ν, ω ∉ E → quenchedKernel (ω,0) A ≤ c) :
    annealedLaw ν A ≤ environmentLaw ν E+c := by
  rw [annealed_apply ν hA]
  calc
    _ ≤ ∫⁻ ω, E.indicator (fun _ => (1:ℝ≥0∞)) ω+c ∂environmentLaw ν := by
      apply lintegral_mono_ae
      filter_upwards [hc] with ω hω
      by_cases he : ω ∈ E
      · simpa [he] using (prob_le_one (μ := quenchedKernel (ω,0)) (s := A)).trans (le_add_right le_rfl)
      · simpa [he] using hω he
    _ = _ := by rw [lintegral_add_left (measurable_const.indicator hE),lintegral_indicator hE]; simp

lemma annealed_crossingGap_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (N : ℕ) (hN : 0<N) (R : ℝ) :
    (annealedLaw ν).real (CrossingGap e N) ≤
      (annealedLaw ν).real (StripExcursion (realPosition (step e)) N R)+
      (2*⌈R⌉₊+1)^d*(environmentLaw ν).real (badCrossingEvent e (N+1) (1/2))+
      (1-((N+1:ℕ):ℝ)^(-(1/2:ℝ)))^(N+1) := by
  let δ := ENNReal.ofReal (((N+1:ℕ):ℝ)^(-(1/2:ℝ)))
  have hNr : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hd1 : ((N+1:ℕ):ℝ)^(-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by norm_num)
  have hd0 : 0 ≤ ((N+1:ℕ):ℝ)^(-(1/2:ℝ)) := Real.rpow_nonneg (by positivity) _
  have hδ : δ ≤ 1 := by simpa [δ] using ENNReal.ofReal_le_ofReal hd1
  have hb := annealed_bound_bad_environment ν
    (CrossingGap e N \ StripExcursion (realPosition (step e)) N R)
    ((measurableSet_crossingGap e N).diff (measurableSet_stripExcursion _ _ _))
    (badBoxEvent e (N+1) (1/2) (latticeBox ⌈R⌉₊)) (measurableSet_badBoxEvent _ _ _ _)
    ((1-δ)^(N+1)) ?_
  · have hbr := ENNReal.toReal_mono (by finiteness) hb
    rw [ENNReal.toReal_add (measure_ne_top _ _) (by finiteness),ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hδ (by norm_num),ENNReal.toReal_one,ENNReal.toReal_ofReal hd0] at hbr
    have hpart : (annealedLaw ν).real (CrossingGap e N) ≤
        (annealedLaw ν).real (StripExcursion (realPosition (step e)) N R)+
        (annealedLaw ν).real (CrossingGap e N \ StripExcursion (realPosition (step e)) N R) := by
      apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (show CrossingGap e N ⊆ StripExcursion (realPosition (step e)) N R ∪
          (CrossingGap e N \ StripExcursion (realPosition (step e)) N R) from fun X hx => by
          by_cases hh : X ∈ StripExcursion (realPosition (step e)) N R
          · exact Or.inl hh
          · exact Or.inr ⟨hx,hh⟩)))
      exact measureReal_union_le _ _
    have hbox := badBox_bound ν e (N+1) (1/2) (latticeBox (d := d) ⌈R⌉₊)
    rw [card_latticeBox] at hbox
    push_cast at hbox
    change (annealedLaw ν).real _ ≤ (environmentLaw ν).real _+_ at hbr
    linarith
  · filter_upwards [quenched_directionallyTransient_ae ν _ htrans] with ω ht hω
    apply quenched_crossingGap_confined ω e N hN R (↑(latticeBox (d := d) ⌈R⌉₊) : Set (Lattice d)) (fun y hy => latticeBox_of_signed_bound R y hy) (ht 0) δ
    intro y hy
    simpa only [δ,Nat.cast_add,Nat.cast_one] using good_box_crossing e _ _ _ ω hω y hy.1

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RapidDecay
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma RapidDecay.of_le {a b : ℕ → ℝ} (hb : RapidDecay b) (ha : ∀ n, 0 ≤ a n)
    (hle : ∀ᶠ n in atTop, a n ≤ b n) : RapidDecay a := by
  intro m
  apply (hb m).of_norm_bounded_eventually_nat
  filter_upwards [hle] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

lemma RapidDecay.add {a b : ℕ → ℝ} (ha : RapidDecay a) (hb : RapidDecay b) :
    RapidDecay (fun n : ℕ => a n+b n) := by
  intro m
  simpa only [mul_add] using (ha m).add (hb m)

lemma RapidDecay.const_mul {a : ℕ → ℝ} (ha : RapidDecay a) (c : ℝ) :
    RapidDecay (fun n : ℕ => c*a n) := by
  intro m
  simpa only [mul_left_comm] using (ha m).mul_left c

lemma RapidDecay.pow_mul {a : ℕ → ℝ} (ha : RapidDecay a) (k : ℕ) :
    RapidDecay (fun n : ℕ => (n+1:ℝ)^k*a n) := by
  intro m
  simpa only [pow_add,mul_assoc] using ha (m+k)

lemma RapidDecay.shift {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n) (k : ℕ) :
    RapidDecay (fun n : ℕ => a (n+k)) := by
  intro m
  apply ((summable_nat_add_iff k).mpr (ha m)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha0 _))]
  apply mul_le_mul_of_nonneg_right _ (ha0 _)
  exact pow_le_pow_left₀ (by positivity) (by push_cast <;> linarith) m

lemma rapidDecay_of_power_bounds {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : ∀ D : ℝ, 0 ≤ D → ∀ᶠ n : ℕ in atTop, a n ≤ (n:ℝ)^(-D)) : RapidDecay a := by
  intro m
  have hs : Summable (fun n : ℕ => (2:ℝ)^m*(n:ℝ)^(-2:ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ)< -1)).mul_left _
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [h (m+2) (by positivity),eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1' : (1:ℝ)≤n := by exact_mod_cast hn1
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  calc
    _ ≤ (2*(n:ℝ))^m*(n:ℝ)^(-(m+2:ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) m) hn (ha n) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_assoc,← Real.rpow_natCast (n:ℝ) m,← Real.rpow_add hn0]
      congr 1
      congr 1
      ring

lemma rapidDecay_of_weighted_limit {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h : ∀ m : ℕ, Tendsto (fun n : ℕ => (n+1:ℝ)^m*a n) atTop (𝓝 0)) : RapidDecay a := by
  intro m
  have hs : Summable (fun n : ℕ => ((n+1:ℝ)^2)⁻¹) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by omega : 1<(2:ℕ)))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [(h (m+2)).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (ha n))]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℝ)^2)).mpr
  simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using hn.le

lemma power_stretchedExp_limit (p q c : ℝ) (hq : 0<q) (hc : 0 < c) :
    Tendsto (fun x : ℝ => x^p*Real.exp (-c*x^q)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/q) c hc).comp (tendsto_rpow_atTop hq)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  change (x^q)^(p/q)*Real.exp (-c*x^q)=_
  rw [← Real.rpow_mul hx]
  congr 2
  field_simp

lemma rapidDecay_stretchedExp (q c : ℝ) (hq : 0<q) (hc : 0 < c) :
    RapidDecay (fun n : ℕ => Real.exp (-c*(n+1:ℝ)^q)) := by
  apply rapidDecay_of_weighted_limit (fun _ => (Real.exp_pos _).le)
  intro m
  have ht : Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  simpa only [Real.rpow_natCast,Function.comp_def] using (power_stretchedExp_limit m q c hq hc).comp ht

lemma rapidDecay_geometric (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r<1) : RapidDecay (fun n : ℕ => r^n) := by
  intro m
  have hs := (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (r := r) m (by simpa [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)).mul_left ((2:ℝ)^m)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (2*(n:ℝ))^m*r^n := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith) m) (pow_nonneg hr0 _)
    _ = _ := by rw [mul_pow,mul_assoc]

lemma descending_probability_bound (N : ℕ) :
    (1-((N+1:ℕ):ℝ)^(-(1/2:ℝ)))^(N+1) ≤
      Real.exp (-((N+1:ℕ):ℝ)^(1/2:ℝ)) := by
  have hn : (0:ℝ)<(N+1:ℕ) := by positivity
  have h1 : (1:ℝ)≤(N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have ha := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num : -(1/2:ℝ)≤0)
  calc
    _ ≤ (Real.exp (-((N+1:ℕ):ℝ)^(-(1/2:ℝ))))^(N+1) :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-((N+1:ℕ):ℝ)^(1/2:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_neg]
      congr 1
      calc
        _ = ((N+1:ℕ):ℝ)^(1:ℝ)*((N+1:ℕ):ℝ)^(-(1/2:ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; norm_num

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingGapDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma polynomial_box_card_bound {d : ℕ} (C : ℝ) (hC : 0 ≤ C) (N : ℕ) :
    (2*(⌈C*(N+1:ℝ)^2⌉₊:ℝ)+1)^d ≤ (2*C+3)^d*(N+1:ℝ)^(2*d) := by
  have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ C*(N+1:ℝ)^2)).le
  have hNsq : (1:ℝ) ≤ (N+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ ((2*C+3)*(N+1:ℝ)^2)^d := pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = _ := by rw [mul_pow,← pow_mul]

lemma bad_crossing_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (environmentLaw ν).real (badCrossingEvent e N (1/2))) := by
  apply rapidDecay_of_power_bounds (fun _ => measureReal_nonneg)
  intro D hD
  filter_upwards [crossing_estimate hd ν hue e htrans D hD] with N hN
  exact hN.le

lemma crossingGap_rapidDecay {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real (CrossingGap e N)) := by
  obtain ⟨C,ε,hC,hε,hε1,hconf⟩ := spatial_confinement ν hue e htrans
  have hbad := (bad_crossing_rapidDecay hd ν hue e htrans).shift (fun _ => measureReal_nonneg) 1
  have hgeom := (rapidDecay_geometric (1-ε) (by linarith) (by linarith)).const_mul (2*d:ℕ)
  have hbox := (hbad.pow_mul (2*d)).const_mul ((2*C+3)^d)
  have hexp := rapidDecay_stretchedExp (1/2) 1 (by norm_num) (by norm_num)
  apply ((hgeom.add hbox).add hexp).of_le (fun _ => measureReal_nonneg)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hh := annealed_crossingGap_bound ν e htrans N (by omega) (C*(N+1:ℝ)^2)
  have hc := hconf N
  have hb := mul_le_mul_of_nonneg_right (polynomial_box_card_bound (d := d) C hC.le N)
    (show 0 ≤ (environmentLaw ν).real (badCrossingEvent e (N+1) (1/2)) from measureReal_nonneg)
  have he := descending_probability_bound N
  simp only [Nat.cast_add,Nat.cast_one,neg_one_mul] at hh he ⊢
  exact hh.trans (add_le_add (add_le_add hc (by simpa only [mul_assoc] using hb)) he)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RapidDecayTail
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma RapidDecay.summable {a : ℕ → ℝ} (ha : RapidDecay a) : Summable a := by
  simpa using ha 0

lemma RapidDecay.tail {a : ℕ → ℝ} (ha : RapidDecay a) (ha0 : ∀ n, 0 ≤ a n) :
    RapidDecay (fun n => ∑' k, a (n+k)) := by
  intro m
  let T := ∑' k : ℕ, (k+1:ℝ)^(m+2)*a k
  have ht (n : ℕ) : Summable (fun k => a (n+k)) := by
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).mpr ha.summable
  have hbound (n : ℕ) : (n+1:ℝ)^(m+2)*(∑' k, a (n+k)) ≤ T := by
    rw [← (ht n).tsum_mul_left]
    have hshift : Summable (fun k : ℕ => (n+k+1:ℝ)^(m+2)*a (n+k)) := by
      simpa only [Nat.cast_add,add_comm (n:ℝ),Nat.add_comm n] using (summable_nat_add_iff n).mpr (ha (m+2))
    calc
      _ ≤ ∑' k : ℕ, (n+k+1:ℝ)^(m+2)*a (n+k) := by
        apply (ht n |>.mul_left _).tsum_le_tsum _ hshift
        intro k
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) k]) _) (ha0 _)
      _ ≤ T := by
        have hh := (ha (m+2)).sum_add_tsum_nat_add n
        have hz : 0 ≤ ∑ k ∈ Finset.range n, (k+1:ℝ)^(m+2)*a k :=
          Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (ha0 _))
        simpa only [T,Nat.add_comm n,Nat.cast_add,add_comm (n:ℝ)] using (show
          (∑' k : ℕ, (↑(k+n)+1:ℝ)^(m+2)*a (k+n)) ≤ T by linarith [hh])
  have hs : Summable (fun n : ℕ => T*((n+1:ℝ)^2)⁻¹) := by
    apply Summable.mul_left
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by omega : 1<(2:ℕ)))
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) (tsum_nonneg (fun k => ha0 _)))]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(n+1:ℝ)^2)).mpr
  simpa only [pow_add,mul_assoc,mul_comm,mul_left_comm] using hbound n

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CrossingSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measureReal_iUnion_le_of_summable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A : ℕ → Set α)
    (hs : Summable (fun n => μ.real (A n))) :
    μ.real (⋃ n, A n) ≤ ∑' n, μ.real (A n) := by
  have he : (∑' n, μ (A n))=ENNReal.ofReal (∑' n, μ.real (A n)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
    simp only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have hh := ENNReal.toReal_mono (by rw [he]; exact ENNReal.ofReal_ne_top) (measure_iUnion_le A)
  rw [he, ENNReal.toReal_ofReal (tsum_nonneg (fun n => measureReal_nonneg))] at hh
  exact hh

lemma antitone_sdiff_iInter_subset {α : Type*} (A : ℕ → Set α) (hA : Antitone A) (N : ℕ) :
    A N \ (⋂ k, A k) ⊆ ⋃ k, A (N+k) \ A (N+k+1) := by
  intro x hx
  have hex : ∃ k, x ∉ A (N+k) := by
    by_contra hh
    push Not at hh
    apply hx.2
    apply Set.mem_iInter.mpr
    intro k
    exact hA (by omega : k ≤ N+k) (hh k)
  have hpos : 0<Nat.find hex := by
    by_contra hh
    have hz : Nat.find hex=0 := by omega
    have hm := Nat.find_spec hex
    rw [hz,Nat.add_zero] at hm
    exact hm hx.1
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nat.find hex≠0)
  refine Set.mem_iUnion.mpr ⟨k,?_,?_⟩
  · by_contra hh
    exact Nat.find_min hex (by omega : k<Nat.find hex) hh
  · simpa only [hk,Nat.succ_eq_add_one,Nat.add_assoc] using Nat.find_spec hex

lemma cross_failure_subset_gaps {d : ℕ} (e : Direction d) (N : ℕ) :
    Cross (realPosition (step e)) 0 N \ NoDrop (realPosition (step e)) 0 ⊆
      ⋃ k, CrossingGap e (N+k) := by
  have hh := antitone_sdiff_iInter_subset
    (fun k => Cross (realPosition (step e)) 0 k)
      (fun i j hij => cross_antitone _ _ (Nat.cast_le.mpr hij)) N
  have hs := Set.Subset.trans (Set.sdiff_subset_sdiff_right (iInter_cross_subset_noDrop (realPosition (step e)) 0)) hh
  simpa only [CrossingGap, Nat.cast_add, Nat.cast_one] using hs

lemma crossing_failure_rapidDecay_oai {d : ℕ} (hd : 2≤d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    RapidDecay (fun N => (annealedLaw ν).real
      (Cross (realPosition (step e)) 0 N \ NoDrop (realPosition (step e)) 0)) := by
  have hg := crossingGap_rapidDecay hd ν hue e htrans
  apply (hg.tail (fun _ => measureReal_nonneg)).of_le (fun _ => measureReal_nonneg)
  apply Eventually.of_forall
  intro N
  calc
    _ ≤ (annealedLaw ν).real (⋃ k, CrossingGap e (N+k)) :=
      measureReal_mono (cross_failure_subset_gaps e N)
    _ ≤ _ := measureReal_iUnion_le_of_summable _ _ (by
      simpa only [Nat.add_comm N] using (summable_nat_add_iff N).mpr hg.summable)

end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.crossing_failure_rapidDecay_oai := @OAI.DirectionalTransience.crossing_failure_rapidDecay_oai
