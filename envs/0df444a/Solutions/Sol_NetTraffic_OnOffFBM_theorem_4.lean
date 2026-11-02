-- Prove2me | solution 1 for NetTraffic.OnOffFBM.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T03:12:51.897362+00:00
-- url     : https://prove2.me/submissions/76194488-db1e-424d-8ee9-7e1197c3e0e1

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

set_option linter.all false

-- ==== part Var.lean ====
section F05Part1

/-! Renewal measure of a stationary (equilibrium-delayed) renewal process (child C2a, step 1).

Abstract setting: `T_n = S_n + T0` with `S_n = Σ_{i<n} Z_i`. If the delay satisfies the
equilibrium identity `E f(y + T0) + ∫ G f (y + z) dF_Z(z) = G f y` with
`G f y = c ∫_{(y,∞)} f`, then the renewal measure `Σ_n law(T_n)` is `c · Leb|(0,∞)`
(`c = 1/μ`). Proof: telescoping + uniqueness via `P(S_n < b) → 0`. -/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Partial sums `S_n = Σ_{i<n} Z_i`. -/
noncomputable def psum (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ range n, Z i ω

theorem psum_measurable {Z : ℕ → Ω → ℝ} (hZm : ∀ n, Measurable (Z n)) (n : ℕ) :
    Measurable (psum Z n) := by
  unfold psum
  exact Finset.measurable_sum _ (fun i _ => hZm i)

/-- The tail integral `G f y = c ∫_{(y,∞)} f`. -/
noncomputable def tailInt (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  c * ∫⁻ x in Set.Ioi y, f x

theorem tailInt_measurable (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) : Measurable (tailInt c f) := by
  have hanti : Antitone (fun y : ℝ => ∫⁻ x in Set.Ioi y, f x) := fun y y' hyy' =>
    lintegral_mono_set (Set.Ioi_subset_Ioi hyy')
  exact hanti.measurable.const_mul c

theorem lintegral_indep_add [IsProbabilityMeasure P] {S T : Ω → ℝ} (hS : Measurable S) (hT : Measurable T)
    (hST : IndepFun S T P) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (S ω + T ω) ∂P = ∫⁻ s, ∫⁻ t, F (s + t) ∂(P.map T) ∂(P.map S) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable hT.aemeasurable).1 hST
  have hm : Measurable (fun p : ℝ × ℝ => F (p.1 + p.2)) :=
    hF.comp (measurable_fst.add measurable_snd)
  rw [← lintegral_prod _ hm.aemeasurable, ← h, lintegral_map hm (hS.prodMk hT)]

/-- Telescoping: `Σ_{k<n} E f(T_k) + E G(S_n) = G(0)`. -/
theorem renewal_telescope [IsProbabilityMeasure P] (T0 : Ω → ℝ) (Z : ℕ → Ω → ℝ) (FZ : Measure ℝ)
    (hT0m : Measurable T0) (hZm : ∀ n, Measurable (Z n)) (hlaw : ∀ n, P.map (Z n) = FZ)
    (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hid : ∀ y, ∫⁻ ω, f (y + T0 ω) ∂P + ∫⁻ z, g (y + z) ∂FZ = g y)
    (hind0 : ∀ n, IndepFun (psum Z n) T0 P) (hindZ : ∀ n, IndepFun (psum Z n) (Z n) P) :
    ∀ n, ∑ k ∈ range n, ∫⁻ ω, f (psum Z k ω + T0 ω) ∂P + ∫⁻ ω, g (psum Z n ω) ∂P = g 0 := by
  intro n
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    have hSm := psum_measurable hZm n
    have hsucc : (fun ω => g (psum Z (n + 1) ω)) = fun ω => g (psum Z n ω + Z n ω) := by
      funext ω; simp [psum, sum_range_succ]
    have key : ∫⁻ ω, g (psum Z n ω) ∂P =
        ∫⁻ ω, f (psum Z n ω + T0 ω) ∂P + ∫⁻ ω, g (psum Z (n + 1) ω) ∂P := by
      rw [hsucc, lintegral_indep_add hSm hT0m (hind0 n) hf,
        lintegral_indep_add hSm (hZm n) (hindZ n) hg, hlaw n]
      have hm1 : Measurable (fun s : ℝ => ∫⁻ t, f (s + t) ∂(P.map T0)) :=
        (hf.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
      rw [← lintegral_add_left hm1]
      have hmap := lintegral_map (μ := P) hg hSm
      rw [← hmap]
      refine lintegral_congr fun s => ?_
      rw [← hid s]
      congr 1
      exact (lintegral_map (hf.comp (measurable_const_add s)) hT0m).symm
    rw [sum_range_succ, add_assoc, ← key, ih]

/-- **Renewal measure of the equilibrium-delayed renewal process.** -/
theorem renewal_measure [IsProbabilityMeasure P] (T0 : Ω → ℝ) (Z : ℕ → Ω → ℝ) (FZ : Measure ℝ) (c : ℝ≥0∞)
    (hc : c ≠ ∞) (hT0m : Measurable T0) (hZm : ∀ n, Measurable (Z n))
    (hlaw : ∀ n, P.map (Z n) = FZ)
    (hid : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∀ y,
      ∫⁻ ω, f (y + T0 ω) ∂P + ∫⁻ z, tailInt c f (y + z) ∂FZ = tailInt c f y)
    (hind0 : ∀ n, IndepFun (psum Z n) T0 P) (hindZ : ∀ n, IndepFun (psum Z n) (Z n) P)
    (htail : ∀ b : ℝ, Tendsto (fun n => P {ω | psum Z n ω < b}) atTop (𝓝 0)) :
    Measure.sum (fun n => P.map (fun ω => psum Z n ω + T0 ω)) =
      c • volume.restrict (Set.Ioi (0 : ℝ)) := by
  have hTm : ∀ n, Measurable (fun ω => psum Z n ω + T0 ω) := fun n =>
    (psum_measurable hZm n).add hT0m
  -- the identity on intervals
  have hIoc : ∀ a b : ℝ, a < b →
      Measure.sum (fun n => P.map (fun ω => psum Z n ω + T0 ω)) (Set.Ioc a b) =
        (c • volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioc a b) := by
    intro a b _
    set f : ℝ → ℝ≥0∞ := (Set.Ioc a b).indicator 1 with hfdef
    have hf : Measurable f := measurable_one.indicator measurableSet_Ioc
    have hG : ∀ y, tailInt c f y = c * volume (Set.Ioc a b ∩ Set.Ioi y) := by
      intro y
      unfold tailInt
      rw [hfdef, lintegral_indicator_one measurableSet_Ioc,
        Measure.restrict_apply measurableSet_Ioc]
    set C : ℝ≥0∞ := c * ENNReal.ofReal (b - a) with hCdef
    have hCne : C ≠ ∞ := ENNReal.mul_ne_top hc ENNReal.ofReal_ne_top
    have hGle : ∀ y, tailInt c f y ≤ C * (Set.Iio b).indicator 1 y := by
      intro y
      rw [hG y]
      by_cases hy : y < b
      · rw [Set.indicator_of_mem (Set.mem_Iio.2 hy), Pi.one_apply, mul_one, hCdef,
          ← Real.volume_Ioc]
        gcongr
        exact Set.inter_subset_left
      · have hempty : Set.Ioc a b ∩ Set.Ioi y = ∅ :=
          Set.eq_empty_of_forall_notMem fun x hx =>
            hy (lt_of_lt_of_le (Set.mem_Ioi.1 hx.2) hx.1.2)
        rw [hempty, measure_empty, mul_zero]
        exact zero_le
    have htel := renewal_telescope T0 Z FZ hT0m hZm hlaw f (tailInt c f) hf
      (tailInt_measurable c f) (hid f hf) hind0 hindZ
    set e : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, tailInt c f (psum Z n ω) ∂P with hedef
    have he_le : ∀ n, e n ≤ C * P {ω | psum Z n ω < b} := by
      intro n
      have hmeas : MeasurableSet {ω | psum Z n ω < b} :=
        measurableSet_lt (psum_measurable hZm n) measurable_const
      calc e n ≤ ∫⁻ ω, C * {ω | psum Z n ω < b}.indicator 1 ω ∂P := by
            refine lintegral_mono fun ω => ?_
            have := hGle (psum Z n ω)
            by_cases hω : psum Z n ω < b
            · rw [Set.indicator_of_mem (Set.mem_Iio.2 hω)] at this
              rwa [Set.indicator_of_mem (show ω ∈ {ω | psum Z n ω < b} from hω)]
            · rw [Set.indicator_of_notMem (fun h => hω (Set.mem_Iio.1 h))] at this
              rwa [Set.indicator_of_notMem (show ω ∉ {ω | psum Z n ω < b} from hω)]
        _ = C * P {ω | psum Z n ω < b} := by
            rw [lintegral_const_mul _ (measurable_one.indicator hmeas),
              lintegral_indicator_one hmeas]
    have he0 : Tendsto e atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => C * P {ω | psum Z n ω < b}) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (htail b) (Or.inr hCne)
        rwa [mul_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
        (fun n => zero_le) he_le
    have hg0 : tailInt c f 0 ≠ ∞ := by
      rw [hG 0]
      refine ENNReal.mul_ne_top hc (ne_top_of_le_ne_top (b := volume (Set.Ioc a b))
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_left))
    have hpart : Tendsto (fun n => ∑ k ∈ range n, ∫⁻ ω, f (psum Z k ω + T0 ω) ∂P) atTop
        (𝓝 (tailInt c f 0)) := by
      have heq : ∀ n, ∑ k ∈ range n, ∫⁻ ω, f (psum Z k ω + T0 ω) ∂P =
          tailInt c f 0 - e n := by
        intro n
        have hle : e n ≤ tailInt c f 0 := by rw [← htel n]; exact le_add_self
        have hen : e n ≠ ∞ := ne_top_of_le_ne_top hg0 hle
        exact ENNReal.eq_sub_of_add_eq hen (htel n)
      simp_rw [heq]
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := tailInt c f 0)) he0 (Or.inl hg0)
      rwa [tsub_zero] at this
    have htsum : ∑' k, ∫⁻ ω, f (psum Z k ω + T0 ω) ∂P = tailInt c f 0 :=
      tendsto_nhds_unique (ENNReal.tendsto_nat_tsum _) hpart
    rw [Measure.sum_apply _ measurableSet_Ioc, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply measurableSet_Ioc, ← hG 0, ← htsum]
    refine tsum_congr fun k => ?_
    rw [← lintegral_indicator_one measurableSet_Ioc, lintegral_map (hf) (hTm k)]
  refine Measure.ext_of_Ioc' _ _ (fun a b hab => ?_) (fun a b hab => hIoc a b hab)
  rw [hIoc a b hab, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_ne_top hc (ne_top_of_le_ne_top (b := volume (Set.Ioc a b))
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (by rw [Measure.restrict_apply measurableSet_Ioc]; exact measure_mono Set.inter_subset_left))

/-- Integral form: `Σ_n E f(T_n) = c ∫_{(0,∞)} f` for every measurable `f ≥ 0`. -/
theorem renewal_lintegral [IsProbabilityMeasure P] (T0 : Ω → ℝ) (Z : ℕ → Ω → ℝ) (FZ : Measure ℝ) (c : ℝ≥0∞)
    (hc : c ≠ ∞) (hT0m : Measurable T0) (hZm : ∀ n, Measurable (Z n))
    (hlaw : ∀ n, P.map (Z n) = FZ)
    (hid : ∀ f : ℝ → ℝ≥0∞, Measurable f → ∀ y,
      ∫⁻ ω, f (y + T0 ω) ∂P + ∫⁻ z, tailInt c f (y + z) ∂FZ = tailInt c f y)
    (hind0 : ∀ n, IndepFun (psum Z n) T0 P) (hindZ : ∀ n, IndepFun (psum Z n) (Z n) P)
    (htail : ∀ b : ℝ, Tendsto (fun n => P {ω | psum Z n ω < b}) atTop (𝓝 0))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∑' n, ∫⁻ ω, f (psum Z n ω + T0 ω) ∂P = c * ∫⁻ x in Set.Ioi 0, f x := by
  have hν := renewal_measure T0 Z FZ c hc hT0m hZm hlaw hid hind0 hindZ htail
  have h1 : ∫⁻ x, f x ∂(Measure.sum (fun n => P.map (fun ω => psum Z n ω + T0 ω))) =
      ∑' n, ∫⁻ ω, f (psum Z n ω + T0 ω) ∂P := by
    rw [lintegral_sum_measure]
    exact tsum_congr fun n => lintegral_map hf ((psum_measurable hZm n).add hT0m)
  rw [← h1, hν, lintegral_smul_measure, smul_eq_mul]

/-- `P(S_n < b) → 0` for iid integrable increments with positive mean (strong law). -/
theorem psum_tail_tendsto_zero [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ)
    (hZm : ∀ n, Measurable (Z n)) (hint : Integrable (Z 0) P)
    (hindep : Pairwise (fun i j => IndepFun (Z i) (Z j) P))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P) (hpos : 0 < P[Z 0]) (b : ℝ) :
    Tendsto (fun n => P {ω | psum Z n ω < b}) atTop (𝓝 0) := by
  have hslln := strong_law_ae_real Z hint hindep hident
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ {ω | psum Z n ω < b} ↔ ω ∈ (∅ : Set Ω)) := by
    filter_upwards [hslln] with ω hω
    set m := P[Z 0] with hm
    have h1 : ∀ᶠ n : ℕ in atTop, m / 2 < (∑ i ∈ range n, Z i ω) / n :=
      hω.eventually (lt_mem_nhds (half_lt_self hpos))
    have h2 : ∀ᶠ n : ℕ in atTop, 2 * b / m < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_gt_atTop _
    have h3 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n :=
      tendsto_natCast_atTop_atTop.eventually_gt_atTop _
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    simp only [Set.mem_empty_iff_false, iff_false, not_lt]
    have hm2 : 0 < m / 2 := half_pos hpos
    have e1 : (m / 2) * n < ((∑ i ∈ range n, Z i ω) / n) * n :=
      mul_lt_mul_of_pos_right hn1 hn3
    have e2 : (m / 2) * (2 * b / m) < (m / 2) * n := mul_lt_mul_of_pos_left hn2 hm2
    have e3 : (m / 2) * (2 * b / m) = b := by field_simp
    have e4 : ((∑ i ∈ range n, Z i ω) / n) * n = psum Z n ω := by
      unfold psum; field_simp
    linarith
  have := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    MeasurableSet.empty (fun n => measurableSet_lt (psum_measurable hZm n) measurable_const) hlim
  rwa [measure_empty] at this

end NetTraffic.OnOffFBM.Lib

/-! The equilibrium (integrated-tail) law identity used to check the renewal hypothesis `hid`
(child C2a, step 2): for a law `F` on `[0, ∞)` with mean `m > 0`,
`m ∫ f(y+t) dF^{(0)}(t) + ∫ (∫_{(y+x,∞)} f) dF(x) = ∫_{(y,∞)} f`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

/-- Translation of a tail integral. -/
theorem setLIntegral_Ioi_add (f : ℝ → ℝ≥0∞) (y x : ℝ) :
    ∫⁻ u in Set.Ioi (y + x), f u = ∫⁻ t in Set.Ioi x, f (y + t) := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self (μ := volume) ((Set.Ioi (y + x)).indicator f) y]
  congr 1
  funext t
  by_cases ht : x < t
  · rw [Set.indicator_of_mem (show y + t ∈ Set.Ioi (y + x) by simp [ht]),
      Set.indicator_of_mem (show t ∈ Set.Ioi x from ht)]
  · rw [Set.indicator_of_notMem (show y + t ∉ Set.Ioi (y + x) by simpa using ht),
      Set.indicator_of_notMem (show t ∉ Set.Ioi x from ht)]

theorem tail_antitone (f : ℝ → ℝ≥0∞) : Antitone (fun y : ℝ => ∫⁻ u in Set.Ioi y, f u) :=
  fun _ _ h => lintegral_mono_set (Set.Ioi_subset_Ioi h)

theorem Fbar_measurable (F : Measure ℝ) [IsFiniteMeasure F] : Measurable (Fbar F) :=
  (show Antitone (Fbar F) from fun _ _ h => measureReal_mono (Set.Ioi_subset_Ioi h)).measurable

/-- **Equilibrium identity** for one law. -/
theorem eqLaw_identity (F : Measure ℝ) [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hm : 0 < mean F) (f : ℝ → ℝ≥0∞) (hf : Measurable f) (y : ℝ) :
    ENNReal.ofReal (mean F) * (∫⁻ t, f (y + t) ∂(eqLaw F)) +
      ∫⁻ x, (∫⁻ u in Set.Ioi (y + x), f u) ∂F = ∫⁻ u in Set.Ioi y, f u := by
  have hfy : Measurable (fun t => f (y + t)) := hf.comp (measurable_const_add y)
  have hdens : Measurable fun s => ENNReal.ofReal (Fbar F s / mean F) :=
    ((Fbar_measurable F).div_const _).ennreal_ofReal
  -- step 1: density
  have h1 : ENNReal.ofReal (mean F) * (∫⁻ t, f (y + t) ∂(eqLaw F)) =
      ∫⁻ t in Set.Ioi 0, F (Set.Ioi t) * f (y + t) := by
    unfold eqLaw
    rw [lintegral_withDensity_eq_lintegral_mul _ hdens hfy,
      ← lintegral_const_mul _ (hdens.mul hfy)]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hm.le, mul_div_cancel₀ _ hm.ne',
      Fbar, ofReal_measureReal (measure_ne_top F _)]
  -- step 2: Tonelli
  have hjoint : Measurable (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (1 : ℝ → ℝ≥0∞) p.2 *
      f (y + p.1)) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
    have : (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (1 : ℝ → ℝ≥0∞) p.2) =
        {p : ℝ × ℝ | p.1 < p.2}.indicator 1 := by
      funext p
      by_cases hp : p.1 < p.2
      · rw [Set.indicator_of_mem (show p.2 ∈ Set.Ioi p.1 from hp),
          Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < p.2} from hp)]
        rfl
      · rw [Set.indicator_of_notMem (show p.2 ∉ Set.Ioi p.1 from hp),
          Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < p.2} from hp)]
    have hind : Measurable (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (1 : ℝ → ℝ≥0∞) p.2) := by
      rw [this]; exact measurable_one.indicator hset
    exact hind.mul (hfy.comp measurable_fst)
  have h2 : ∫⁻ t in Set.Ioi 0, F (Set.Ioi t) * f (y + t) =
      ∫⁻ x, (∫⁻ t in Set.Ioi 0, (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) x * f (y + t)) ∂F := by
    have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := F)
      (f := fun t x => (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) x * f (y + t)) hjoint.aemeasurable
    refine Eq.trans ?_ hswap
    refine lintegral_congr fun t => ?_
    rw [lintegral_mul_const _ (measurable_one.indicator measurableSet_Ioi),
      lintegral_indicator_one measurableSet_Ioi]
  -- step 3: pointwise in `x ≥ 0`
  have h3 : ∀ x : ℝ, 0 ≤ x →
      (∫⁻ t in Set.Ioi 0, (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) x * f (y + t)) +
        ∫⁻ u in Set.Ioi (y + x), f u = ∫⁻ u in Set.Ioi y, f u := by
    intro x hx
    have hK : ∫⁻ t in Set.Ioi 0, (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) x * f (y + t) =
        ∫⁻ t in Set.Ioc 0 x, f (y + t) := by
      have hpt : (fun t => (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) x * f (y + t)) =
          (Set.Iio x).indicator (fun t => f (y + t)) := by
        funext t
        by_cases ht : t < x
        · rw [Set.indicator_of_mem (show x ∈ Set.Ioi t from ht),
            Set.indicator_of_mem (show t ∈ Set.Iio x from ht), Pi.one_apply, one_mul]
        · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi t from ht),
            Set.indicator_of_notMem (show t ∉ Set.Iio x from ht), zero_mul]
      rw [hpt, setLIntegral_indicator measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio]
      exact setLIntegral_congr Ioo_ae_eq_Ioc
    refine (congrArg (fun z => z + ∫⁻ u in Set.Ioi (y + x), f u) hK).trans ?_
    rw [setLIntegral_Ioi_add f y x, ← lintegral_union measurableSet_Ioi
      Set.Ioc_disjoint_Ioi_same, Set.Ioc_union_Ioi_eq_Ioi hx]
    have := setLIntegral_Ioi_add f y 0
    rw [add_zero] at this
    exact this.symm
  -- step 4: integrate in `x`
  have hnn : ∀ᵐ x ∂F, 0 ≤ x := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => Set.mem_Iio.2 (not_le.1 hx)) h0
  have hBm : Measurable (fun x : ℝ => ∫⁻ u in Set.Ioi (y + x), f u) :=
    (tail_antitone f).measurable.comp (measurable_const_add y)
  rw [h1, h2]
  calc _ = ∫⁻ x, ((∫⁻ t in Set.Ioi 0, (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) x * f (y + t)) +
        ∫⁻ u in Set.Ioi (y + x), f u) ∂F := (lintegral_add_right _ hBm).symm
    _ = ∫⁻ _x, (∫⁻ u in Set.Ioi y, f u) ∂F :=
        lintegral_congr_ae (by filter_upwards [hnn] with x hx; exact h3 x hx)
    _ = ∫⁻ u in Set.Ioi y, f u := by rw [lintegral_const, measure_univ, mul_one]

section Source0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem lintegral_indep_pair [IsProbabilityMeasure P] {U V : Ω → ℝ} (hU : Measurable U)
    (hV : Measurable V) (hUV : IndepFun U V P) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ u, (∫⁻ v, F (u, v) ∂(P.map V)) ∂(P.map U) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hUV
  rw [← lintegral_prod _ hF.aemeasurable, ← h, lintegral_map hF (hU.prodMk hV)]

/-- `I_F(v) = ∫ f(v + t) dF^{(0)}(t)` is measurable in `v`. -/
theorem measurable_shift_lintegral (ν : Measure ℝ) [SFinite ν] (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) : Measurable (fun v : ℝ => ∫⁻ t, f (v + t) ∂ν) :=
  (hf.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'

/-- **The equilibrium identity for the delay `T_0` of an ON/OFF source**
(hypothesis `hid` of `renewal_measure` with `c = 1/μ` and `F_Z = F_on ∗ F_off`, written as an
iterated integral). -/
theorem T0_identity [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff) {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) (y : ℝ) :
    ∫⁻ ω, f (y + s.T0 ω) ∂P +
      ∫⁻ w, (∫⁻ x, (ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ u in Set.Ioi (y + w + x), f u) ∂Fon)
        ∂Foff = ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ u in Set.Ioi y, f u := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  set c : ℝ≥0∞ := ENNReal.ofReal (mu Fon Foff)⁻¹ with hc
  set p1 : ℝ≥0∞ := ENNReal.ofReal (mean Fon / mu Fon Foff) with hp1
  set p0 : ℝ≥0∞ := ENNReal.ofReal (mean Foff / mu Fon Foff) with hp0
  have hcp1 : p1 = c * ENNReal.ofReal (mean Fon) := by
    rw [hp1, hc, ← ENNReal.ofReal_mul (inv_nonneg.2 hmu.le), div_eq_inv_mul]
  have hcp0 : p0 = c * ENNReal.ofReal (mean Foff) := by
    rw [hp0, hc, ← ENNReal.ofReal_mul (inv_nonneg.2 hmu.le), div_eq_inv_mul]
  have hBm : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0m : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hY0m : Measurable s.Y0 := hs.measurable (Sum.inl 2)
  have hYom : Measurable s.Yoff := hs.measurable (Sum.inl 3)
  have hi_pair : IndepFun (fun ω => (s.X0 ω, s.Yoff ω)) s.B P :=
    hs.indep.indepFun_prodMk hs.measurable (Sum.inl 1) (Sum.inl 3) (Sum.inl 0)
      (by decide) (by decide)
  have hi_BY0 : IndepFun s.B s.Y0 P := hs.indep.indepFun (i := Sum.inl 0) (j := Sum.inl 2)
    (by decide)
  have hi_YX : IndepFun s.Yoff s.X0 P := hs.indep.indepFun (i := Sum.inl 3) (j := Sum.inl 1)
    (by decide)
  -- B ∈ {0, 1} a.s.
  have hS : MeasurableSet (({0, 1} : Set ℝ)ᶜ) :=
    (measurableSet_insert.2 (measurableSet_singleton 1)).compl
  have hB01 : ∀ᵐ ω ∂P, s.B ω = 0 ∨ s.B ω = 1 := by
    have h1 : P.map s.B (({0, 1} : Set ℝ)ᶜ) = 0 := by
      rw [hs.law_B, bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hS, Measure.dirac_apply' _ hS]
      simp
    rw [Measure.map_apply hBm hS] at h1
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h1
    simpa using hω
  have hPB : ∀ a : ℝ, P (s.B ⁻¹' {a}) = bernoulliLaw Fon Foff {a} := fun a => by
    rw [← Measure.map_apply hBm (measurableSet_singleton a), hs.law_B]
  have hPB1 : P (s.B ⁻¹' {1}) = p1 := by
    rw [hPB, bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton 1),
      Measure.dirac_apply' _ (measurableSet_singleton 1)]
    simp [hp1]
  have hPB0 : P (s.B ⁻¹' {0}) = p0 := by
    rw [hPB, bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton 0),
      Measure.dirac_apply' _ (measurableSet_singleton 0)]
    simp [hp0]
  -- decomposition of `f (y + T0)`
  set g1 : Ω → ℝ≥0∞ := fun ω => ({1} : Set ℝ).indicator 1 (s.B ω) with hg1
  set g0 : Ω → ℝ≥0∞ := fun ω => ({0} : Set ℝ).indicator 1 (s.B ω) with hg0
  set k1 : Ω → ℝ≥0∞ := fun ω => f (y + (s.X0 ω + s.Yoff ω)) with hk1
  set k0 : Ω → ℝ≥0∞ := fun ω => f (y + s.Y0 ω) with hk0
  have hg1m : Measurable g1 := (measurable_one.indicator (measurableSet_singleton 1)).comp hBm
  have hg0m : Measurable g0 := (measurable_one.indicator (measurableSet_singleton 0)).comp hBm
  have hk1m : Measurable k1 :=
    hf.comp (measurable_const.add (hX0m.add hYom))
  have hk0m : Measurable k0 := hf.comp (measurable_const.add hY0m)
  have hdec : (fun ω => f (y + s.T0 ω)) =ᵐ[P] fun ω => g1 ω * k1 ω + g0 ω * k0 ω := by
    filter_upwards [hB01] with ω hω
    rcases hω with h | h
    · simp [hg1, hg0, hk0, Source.T0, h]
    · simp [hg1, hg0, hk1, Source.T0, h]
  have hI1 : ∫⁻ ω, g1 ω * k1 ω ∂P = p1 * ∫⁻ ω, k1 ω ∂P := by
    have hind : IndepFun g1 k1 P := by
      have := hi_pair.symm.comp (φ := fun b => ({1} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) b)
        (ψ := fun p : ℝ × ℝ => f (y + (p.1 + p.2)))
        (measurable_one.indicator (measurableSet_singleton 1))
        (hf.comp (measurable_const.add (measurable_fst.add measurable_snd)))
      exact this
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hg1m.aemeasurable
      hk1m.aemeasurable hind]
    congr 1
    rw [← hPB1, ← Measure.map_apply hBm (measurableSet_singleton 1),
      ← lintegral_indicator_one (measurableSet_singleton 1),
      lintegral_map (measurable_one.indicator (measurableSet_singleton 1)) hBm]
    try rfl
  have hI0 : ∫⁻ ω, g0 ω * k0 ω ∂P = p0 * ∫⁻ ω, k0 ω ∂P := by
    have hind : IndepFun g0 k0 P :=
      hi_BY0.comp (measurable_one.indicator (measurableSet_singleton 0))
        (hf.comp (measurable_const_add y))
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hg0m.aemeasurable
      hk0m.aemeasurable hind]
    congr 1
    rw [← hPB0, ← Measure.map_apply hBm (measurableSet_singleton 0),
      ← lintegral_indicator_one (measurableSet_singleton 0),
      lintegral_map (measurable_one.indicator (measurableSet_singleton 0)) hBm]
    try rfl
  -- the two expectations through the laws
  have hK1 : ∫⁻ ω, k1 ω ∂P = ∫⁻ w, (∫⁻ x, f ((y + w) + x) ∂(eqLaw Fon)) ∂Foff := by
    have := lintegral_indep_pair hYom hX0m hi_YX
      (F := fun p : ℝ × ℝ => f ((y + p.1) + p.2))
      (hf.comp ((measurable_const.add measurable_fst).add measurable_snd))
    rw [hs.law_X0, hs.law_Yoff] at this
    rw [← this, hk1]
    refine lintegral_congr fun ω => ?_
    simp only
    congr 1
    ring
  have hK0 : ∫⁻ ω, k0 ω ∂P = ∫⁻ t, f (y + t) ∂(eqLaw Foff) := by
    rw [← hs.law_Y0]
    exact (lintegral_map (f := fun t => f (y + t)) (hf.comp (measurable_const_add y)) hY0m).symm
  -- equilibrium identities
  have hA : ∀ w, ENNReal.ofReal (mean Fon) * (∫⁻ x, f ((y + w) + x) ∂(eqLaw Fon)) +
      ∫⁻ x, (∫⁻ u in Set.Ioi ((y + w) + x), f u) ∂Fon = ∫⁻ u in Set.Ioi (y + w), f u :=
    fun w => eqLaw_identity Fon hon0 hon f hf (y + w)
  have hB := eqLaw_identity Foff hoff0 hoff f hf y
  have : SFinite (eqLaw Fon) := by unfold eqLaw; infer_instance
  have hmI : Measurable (fun w : ℝ => ∫⁻ x, f ((y + w) + x) ∂(eqLaw Fon)) :=
    (measurable_shift_lintegral (eqLaw Fon) f hf).comp (measurable_const_add y)
  have hmT : Measurable (fun w : ℝ =>
      ∫⁻ x, (c * ∫⁻ u in Set.Ioi (y + w + x), f u) ∂Fon) := by
    have : Measurable (fun p : ℝ × ℝ => c * ∫⁻ u in Set.Ioi (y + p.1 + p.2), f u) :=
      ((tail_antitone f).measurable.comp
        ((measurable_const.add measurable_fst).add measurable_snd)).const_mul c
    exact this.lintegral_prod_right'
  rw [lintegral_congr_ae hdec, lintegral_add_left (f := fun ω => g1 ω * k1 ω) (hg1m.mul hk1m),
    hI1, hI0, hK1, hK0]
  -- combine
  have hstep : p1 * (∫⁻ w, (∫⁻ x, f ((y + w) + x) ∂(eqLaw Fon)) ∂Foff) +
      ∫⁻ w, (∫⁻ x, (c * ∫⁻ u in Set.Ioi (y + w + x), f u) ∂Fon) ∂Foff =
      ∫⁻ w, (c * ∫⁻ u in Set.Ioi (y + w), f u) ∂Foff := by
    rw [← lintegral_const_mul _ hmI, ← lintegral_add_left (hmI.const_mul p1)]
    refine lintegral_congr fun w => ?_
    rw [lintegral_const_mul (f := fun x => ∫⁻ u in Set.Ioi (y + w + x), f u) c
      ((tail_antitone f).measurable.comp (measurable_const_add (y + w))), ← hA w, mul_add,
      hcp1, mul_assoc]
  have hstep2 : ∫⁻ w, (c * ∫⁻ u in Set.Ioi (y + w), f u) ∂Foff + p0 * ∫⁻ t, f (y + t) ∂(eqLaw Foff)
      = c * ∫⁻ u in Set.Ioi y, f u := by
    rw [lintegral_const_mul (f := fun w => ∫⁻ u in Set.Ioi (y + w), f u) c
      ((tail_antitone f).measurable.comp (measurable_const_add y)),
      ← hB, hcp0, mul_add, mul_assoc, add_comm]
  calc p1 * (∫⁻ w, (∫⁻ x, f ((y + w) + x) ∂(eqLaw Fon)) ∂Foff) +
        p0 * (∫⁻ t, f (y + t) ∂(eqLaw Foff)) +
        ∫⁻ w, (∫⁻ x, (c * ∫⁻ u in Set.Ioi (y + w + x), f u) ∂Fon) ∂Foff
      = (p1 * (∫⁻ w, (∫⁻ x, f ((y + w) + x) ∂(eqLaw Fon)) ∂Foff) +
        ∫⁻ w, (∫⁻ x, (c * ∫⁻ u in Set.Ioi (y + w + x), f u) ∂Fon) ∂Foff) +
        p0 * (∫⁻ t, f (y + t) ∂(eqLaw Foff)) := by ring
    _ = c * ∫⁻ u in Set.Ioi y, f u := by rw [hstep, hstep2]

end Source0

end NetTraffic.OnOffFBM.Lib

/-! ### C2a step 3: the renewal measure of one ON/OFF source -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section SourceRen

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Sums over disjoint finite index sets of an independent family are independent. -/
theorem indepFun_finset_sum {ι : Type*} {f : ι → Ω → ℝ} (hind : iIndepFun f P)
    (hm : ∀ i, Measurable (f i)) (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun ω => ∑ j ∈ S, f j ω) (fun ω => ∑ j ∈ T, f j ω) P := by
  have h := (hind.indepFun_finset S T hST hm).comp
    (φ := fun x : S → ℝ => ∑ j : S, x j) (ψ := fun x : T → ℝ => ∑ j : T, x j)
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
  convert h using 1
  · funext ω
    exact (Finset.sum_coe_sort S (fun j => f j ω)).symm
  · funext ω
    exact (Finset.sum_coe_sort T (fun j => f j ω)).symm

/-- The cycle lengths `Z_n = X_n + Y_n` of a source. -/
def srcZ (s : Source Ω) (n : ℕ) (ω : Ω) : ℝ := s.X n ω + s.Y n ω

/-- Index set of the cycles `n ∈ S` inside `Source.family`. -/
def idxZ (S : Finset ℕ) : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := (∅ : Finset (Fin 4)).disjSum (S.disjSum S)

/-- Index set of the delay ingredients `B, X0, Y0, Yoff`. -/
def idx0 : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := (Finset.univ : Finset (Fin 4)).disjSum ∅

theorem sum_idxZ (s : Source Ω) (S : Finset ℕ) (ω : Ω) :
    ∑ j ∈ idxZ S, s.family j ω = ∑ i ∈ S, srcZ s i ω := by
  simp [idxZ, Finset.sum_disjSum, Source.family, srcZ, Finset.sum_add_distrib]

theorem disjoint_idxZ {S S' : Finset ℕ} (h : Disjoint S S') : Disjoint (idxZ S) (idxZ S') := by
  rw [Finset.disjoint_left]
  rintro (a | (a | a)) h1 h2
  · simp [idxZ] at h1
  · simp [idxZ] at h1 h2
    exact Finset.disjoint_left.1 h h1 h2
  · simp [idxZ] at h1 h2
    exact Finset.disjoint_left.1 h h1 h2

theorem disjoint_idxZ_idx0 (S : Finset ℕ) : Disjoint (idxZ S) idx0 := by
  rw [Finset.disjoint_left]
  rintro (a | (a | a)) h1 h2
  · simp [idxZ] at h1
  · simp [idx0] at h2
  · simp [idx0] at h2

theorem psum_srcZ_eq (s : Source Ω) (n : ℕ) (ω : Ω) :
    psum (srcZ s) n ω = ∑ j ∈ idxZ (range n), s.family j ω := by
  rw [sum_idxZ]; rfl

theorem srcZ_eq (s : Source Ω) (n : ℕ) (ω : Ω) :
    srcZ s n ω = ∑ j ∈ idxZ {n}, s.family j ω := by
  rw [sum_idxZ, Finset.sum_singleton]

theorem srcZ_measurable {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n : ℕ) : Measurable (srcZ s n) :=
  (hs.measurable (Sum.inr (Sum.inl n))).add (hs.measurable (Sum.inr (Sum.inr n)))

theorem T0_measurable {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Measurable s.T0 := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hY0 : Measurable s.Y0 := hs.measurable (Sum.inl 2)
  have hYo : Measurable s.Yoff := hs.measurable (Sum.inl 3)
  unfold Source.T0
  exact (hB.mul (hX0.add hYo)).add ((measurable_const.sub hB).mul hY0)

theorem indep_psum_T0 {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n : ℕ) : IndepFun (psum (srcZ s) n) s.T0 P := by
  have h := (hs.indep.indepFun_finset (idxZ (range n)) idx0 (disjoint_idxZ_idx0 _)
    hs.measurable).comp
    (φ := fun x : (idxZ (range n)) → ℝ => ∑ j : (idxZ (range n)), x j)
    (ψ := fun x : idx0 → ℝ =>
      x ⟨Sum.inl 0, by simp [idx0]⟩ * (x ⟨Sum.inl 1, by simp [idx0]⟩ +
        x ⟨Sum.inl 3, by simp [idx0]⟩) +
        (1 - x ⟨Sum.inl 0, by simp [idx0]⟩) * x ⟨Sum.inl 2, by simp [idx0]⟩)
    (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) (by fun_prop)
  convert h using 1
  · funext ω
    rw [psum_srcZ_eq]
    exact (Finset.sum_coe_sort _ (fun j => s.family j ω)).symm
  · funext ω
    simp [Source.T0, Source.family]

theorem indep_psum_srcZ {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n : ℕ) : IndepFun (psum (srcZ s) n) (srcZ s n) P := by
  have h := indepFun_finset_sum hs.indep hs.measurable (idxZ (range n)) (idxZ {n})
    (disjoint_idxZ (Finset.disjoint_singleton_right.2 (by simp)))
  convert h using 1
  · funext ω; exact psum_srcZ_eq s n ω
  · funext ω; exact srcZ_eq s n ω

theorem indep_srcZ_pair {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    {i j : ℕ} (hij : i ≠ j) : IndepFun (srcZ s i) (srcZ s j) P := by
  have h := indepFun_finset_sum hs.indep hs.measurable (idxZ {i}) (idxZ {j})
    (disjoint_idxZ (Finset.disjoint_singleton.2 hij))
  convert h using 1
  · funext ω; exact srcZ_eq s i ω
  · funext ω; exact srcZ_eq s j ω

/-- The law of a cycle: `Z_n ∼ (F_off ⊗ F_on) ∘ (w, x) ↦ x + w`. -/
theorem map_srcZ [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n : ℕ) : P.map (srcZ s n) = (Foff.prod Fon).map (fun p : ℝ × ℝ => p.2 + p.1) := by
  have hX : Measurable (s.X n) := hs.measurable (Sum.inr (Sum.inl n))
  have hY : Measurable (s.Y n) := hs.measurable (Sum.inr (Sum.inr n))
  have hYX : IndepFun (s.Y n) (s.X n) P :=
    hs.indep.indepFun (i := Sum.inr (Sum.inr n)) (j := Sum.inr (Sum.inl n)) (by simp)
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable).1 hYX
  rw [hs.law_X n, hs.law_Y n] at hpair
  rw [← hpair, Measure.map_map (by fun_prop) (hY.prodMk hX)]
  rfl

theorem source_hid [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff) {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) (y : ℝ) :
    ∫⁻ ω, f (y + s.T0 ω) ∂P +
      ∫⁻ z, tailInt (ENNReal.ofReal (mu Fon Foff)⁻¹) f (y + z)
        ∂((Foff.prod Fon).map (fun p : ℝ × ℝ => p.2 + p.1)) =
      tailInt (ENNReal.ofReal (mu Fon Foff)⁻¹) f y := by
  have hg : Measurable (fun z => tailInt (ENNReal.ofReal (mu Fon Foff)⁻¹) f (y + z)) :=
    (tailInt_measurable _ f).comp (measurable_const_add y)
  rw [lintegral_map hg (by fun_prop),
    lintegral_prod (fun a : ℝ × ℝ => tailInt (ENNReal.ofReal (mu Fon Foff)⁻¹) f (y + (a.2 + a.1)))
      (hg.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2 + p.1))).aemeasurable]
  have h := T0_identity hon0 hoff0 hon hoff hs f hf y
  unfold tailInt
  rw [← h]
  congr 1
  refine lintegral_congr fun w => lintegral_congr fun x => ?_
  simp only [Function.comp_apply]
  rw [show y + (x + w) = y + w + x by ring]

/-- **Renewal theorem for one ON/OFF source**: `Σ_n E f(T_n) = μ^{-1} ∫_0^∞ f`. -/
theorem source_renewal [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∑' n, ∫⁻ ω, f (s.Tn n ω) ∂P = ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ x in Set.Ioi 0, f x := by
  have hZm := srcZ_measurable hs
  have hX0m : Measurable (s.X 0) := hs.measurable (Sum.inr (Sum.inl 0))
  have hY0m : Measurable (s.Y 0) := hs.measurable (Sum.inr (Sum.inr 0))
  have hintX : Integrable (s.X 0) P :=
    (integrable_map_measure (g := fun x : ℝ => x) aestronglyMeasurable_id hX0m.aemeasurable).1
      (by rw [hs.law_X 0]; exact hion)
  have hintY : Integrable (s.Y 0) P :=
    (integrable_map_measure (g := fun x : ℝ => x) aestronglyMeasurable_id hY0m.aemeasurable).1
      (by rw [hs.law_Y 0]; exact hioff)
  have hEX : P[s.X 0] = mean Fon := by
    rw [mean, ← hs.law_X 0]
    exact (integral_map (φ := s.X 0) (f := fun x : ℝ => x) hX0m.aemeasurable
      measurable_id'.aestronglyMeasurable).symm
  have hEY : P[s.Y 0] = mean Foff := by
    rw [mean, ← hs.law_Y 0]
    exact (integral_map (φ := s.Y 0) (f := fun x : ℝ => x) hY0m.aemeasurable
      measurable_id'.aestronglyMeasurable).symm
  have hint : Integrable (srcZ s 0) P := hintX.add hintY
  have hpos : 0 < P[srcZ s 0] := by
    have : P[srcZ s 0] = P[s.X 0] + P[s.Y 0] := integral_add hintX hintY
    rw [this, hEX, hEY]; linarith
  have hident : ∀ i, IdentDistrib (srcZ s i) (srcZ s 0) P P := fun i =>
    ⟨(hZm i).aemeasurable, (hZm 0).aemeasurable, by rw [map_srcZ hs i, map_srcZ hs 0]⟩
  have htail := psum_tail_tendsto_zero (srcZ s) hZm hint
    (fun i j hij => indep_srcZ_pair hs hij) hident hpos
  have hmain := renewal_lintegral s.T0 (srcZ s) ((Foff.prod Fon).map (fun p : ℝ × ℝ => p.2 + p.1))
    (ENNReal.ofReal (mu Fon Foff)⁻¹) ENNReal.ofReal_ne_top (T0_measurable hs) hZm (map_srcZ hs)
    (fun g hg y => source_hid hon0 hoff0 hon hoff hs g hg y) (indep_psum_T0 hs)
    (indep_psum_srcZ hs) htail f hf
  rw [← hmain]
  refine tsum_congr fun n => lintegral_congr fun ω => ?_
  congr 1
  simp only [Source.Tn, psum, srcZ]
  ring

end SourceRen

end NetTraffic.OnOffFBM.Lib

/-! ### C2a step 4: `E W_t = μ_on/μ` (the mean of the ON/OFF process is constant) -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section MeanW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem Tn_measurable {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n : ℕ) : Measurable (s.Tn n) := by
  unfold Source.Tn
  exact (T0_measurable hs).add (Finset.measurable_sum _ fun i _ => srcZ_measurable hs i)

theorem Tn_eq_sum (s : Source Ω) (n : ℕ) (ω : Ω) :
    s.Tn n ω = (s.B ω * (s.X0 ω + s.Yoff ω) + (1 - s.B ω) * s.Y0 ω) +
      ∑ j ∈ idxZ (range n), s.family j ω := by
  rw [← psum_srcZ_eq]
  rfl

theorem indep_Tn_X {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n : ℕ) : IndepFun (s.Tn n) (s.X n) P := by
  have hdisj : Disjoint (idx0 ∪ idxZ (range n)) (idxZ {n}) :=
    Finset.disjoint_union_left.2 ⟨(disjoint_idxZ_idx0 {n}).symm,
      disjoint_idxZ (Finset.disjoint_singleton_right.2 (by simp))⟩
  have hmem : ∀ j ∈ idxZ (range n), j ∈ idx0 ∪ idxZ (range n) :=
    fun j hj => Finset.mem_union_right _ hj
  have h := (hs.indep.indepFun_finset _ _ hdisj hs.measurable).comp
    (φ := fun x : (idx0 ∪ idxZ (range n) : Finset _) → ℝ =>
      (x ⟨Sum.inl 0, by simp [idx0]⟩ * (x ⟨Sum.inl 1, by simp [idx0]⟩ +
        x ⟨Sum.inl 3, by simp [idx0]⟩) +
        (1 - x ⟨Sum.inl 0, by simp [idx0]⟩) * x ⟨Sum.inl 2, by simp [idx0]⟩) +
        ∑ j ∈ (idxZ (range n)).attach, x ⟨j.1, hmem j.1 j.2⟩)
    (ψ := fun x : (idxZ {n} : Finset _) → ℝ => x ⟨Sum.inr (Sum.inl n), by simp [idxZ]⟩)
    (Measurable.add (by fun_prop) (Finset.measurable_sum _ fun j _ => measurable_pi_apply _))
    (measurable_pi_apply _ : Measurable fun x : (idxZ {n} : Finset _) → ℝ =>
      x ⟨Sum.inr (Sum.inl n), by simp [idxZ]⟩)
  convert h using 1
  · funext ω
    rw [Tn_eq_sum]
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (range n)) (fun j => s.family j ω)]
    rfl
  · funext ω
    rfl

/-- Renewal formula with the ON-period mark: `Σ_n E k(T_n, X_n) = μ^{-1} ∫_0^∞ ∫ k(r, x) F_on(dx) dr`. -/
theorem source_renewal_X [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (k : ℝ × ℝ → ℝ≥0∞) (hk : Measurable k) :
    ∑' n, ∫⁻ ω, k (s.Tn n ω, s.X n ω) ∂P =
      ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ r in Set.Ioi 0, ∫⁻ x, k (r, x) ∂Fon := by
  have hg : Measurable (fun r => ∫⁻ x, k (r, x) ∂Fon) := hk.lintegral_prod_right'
  rw [← source_renewal hon0 hoff0 hon hoff hion hioff hs _ hg]
  refine tsum_congr fun n => ?_
  have hX : Measurable (s.X n) := hs.measurable (Sum.inr (Sum.inl n))
  rw [lintegral_indep_pair (Tn_measurable hs n) hX (indep_Tn_X hs n) hk, hs.law_X n,
    lintegral_map hg (Tn_measurable hs n)]

/-- The indicator kernel `k_t(r, x) = 1{r ≤ t < r + x}`. -/
noncomputable def kON (t : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  Set.indicator {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} 1

theorem kON_measurable (t : ℝ) : Measurable (kON t) := by
  refine Measurable.indicator measurable_const ?_
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))

theorem ofReal_ind_Ico (t a x : ℝ) :
    ENNReal.ofReal ((Set.Ico a (a + x)).indicator (fun _ => (1 : ℝ)) t) = kON t (a, x) := by
  by_cases h : a ≤ t ∧ t < a + x
  · have h' : t ∈ Set.Ico a (a + x) := h
    rw [Set.indicator_of_mem h', kON, Set.indicator_of_mem (show (a, x) ∈
      {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} from h)]
    simp
  · have h' : t ∉ Set.Ico a (a + x) := h
    rw [Set.indicator_of_notMem h', kON, Set.indicator_of_notMem (show (a, x) ∉
      {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} from h)]
    simp

theorem ofReal_Fbar (F : Measure ℝ) [IsFiniteMeasure F] (x : ℝ) :
    ENNReal.ofReal (Fbar F x) = F (Set.Ioi x) := by
  rw [Fbar, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem lintegral_kON (F : Measure ℝ) [IsFiniteMeasure F] (t r : ℝ) :
    ∫⁻ x, kON t (r, x) ∂F = (Set.Iic t).indicator (fun r => ENNReal.ofReal (Fbar F (t - r))) r := by
  by_cases hr : r ≤ t
  · rw [Set.indicator_of_mem (show r ∈ Set.Iic t from hr), ofReal_Fbar]
    have : (fun x => kON t (r, x)) = (Set.Ioi (t - r)).indicator 1 := by
      funext x
      by_cases hx : t - r < x
      · rw [Set.indicator_of_mem (show x ∈ Set.Ioi (t - r) from hx), kON,
          Set.indicator_of_mem (show (r, x) ∈ {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} from
            ⟨hr, show t < r + x by linarith⟩)]
        rfl
      · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi (t - r) from hx), kON,
          Set.indicator_of_notMem (show (r, x) ∉ {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} from
            fun h => hx (by have h2 : t < r + x := h.2; linarith))]
    rw [this, lintegral_indicator_one measurableSet_Ioi]
  · rw [Set.indicator_of_notMem (show r ∉ Set.Iic t from hr)]
    have : (fun x => kON t (r, x)) = fun _ => 0 := by
      funext x
      rw [kON, Set.indicator_of_notMem (show (r, x) ∉ {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} from
        fun h => hr h.1)]
    rw [this, lintegral_zero]

/-- Reflection `r ↦ t - r`: `∫_{(0,t]} φ(t - r) dr = ∫_{[0,t)} φ`. -/
theorem lintegral_reflect (φ : ℝ → ℝ≥0∞) (t : ℝ) :
    ∫⁻ r in Set.Ioi 0, (Set.Iic t).indicator (fun r => φ (t - r)) r =
      ∫⁻ v in Set.Ico 0 t, φ v := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ico,
    ← lintegral_sub_left_eq_self (μ := volume) ((Set.Ico 0 t).indicator φ) t]
  congr 1
  funext r
  by_cases h : 0 < r ∧ r ≤ t
  · rw [Set.indicator_of_mem (show r ∈ Set.Ioi 0 from h.1),
      Set.indicator_of_mem (show r ∈ Set.Iic t from h.2),
      Set.indicator_of_mem (show t - r ∈ Set.Ico 0 t from ⟨by linarith [h.2], by linarith [h.1]⟩)]
  · have h' : t - r ∉ Set.Ico 0 t := fun h2 => h ⟨by linarith [h2.2], by linarith [h2.1]⟩
    rw [Set.indicator_of_notMem h']
    by_cases h1 : 0 < r
    · rw [Set.indicator_of_mem (show r ∈ Set.Ioi 0 from h1),
        Set.indicator_of_notMem (show r ∉ Set.Iic t from fun h2 => h ⟨h1, h2⟩)]
    · rw [Set.indicator_of_notMem (show r ∉ Set.Ioi 0 from h1)]

/-- Layer cake: `∫_0^∞ F̄ = mean F`. -/
theorem lintegral_Fbar_eq_mean (F : Measure ℝ) [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) :
    ∫⁻ v in Set.Ioi 0, ENNReal.ofReal (Fbar F v) = ENNReal.ofReal (mean F) := by
  have hnn : 0 ≤ᵐ[F] (fun x : ℝ => x) := by
    rw [Filter.EventuallyLE, ae_iff]
    have : {a : ℝ | ¬ (0 : ℝ → ℝ) a ≤ a} = Set.Iio 0 := by
      ext a; simp
    rw [this, h0]
  rw [mean, ofReal_integral_eq_lintegral_ofReal hi hnn,
    lintegral_eq_lintegral_meas_lt F hnn measurable_id'.aemeasurable]
  refine lintegral_congr fun v => ?_
  rw [ofReal_Fbar]
  rfl

theorem lintegral_bernoulli (Fon Foff : Measure ℝ) :
    ∫⁻ b, ENNReal.ofReal b ∂(bernoulliLaw Fon Foff) = ENNReal.ofReal (mean Fon / mu Fon Foff) := by
  simp [bernoulliLaw, lintegral_add_measure, lintegral_smul_measure]

theorem eqLaw_Ioi (F : Measure ℝ) {t : ℝ} (ht : 0 ≤ t) :
    eqLaw F (Set.Ioi t) = ∫⁻ v in Set.Ioi t, ENNReal.ofReal (Fbar F v / mean F) := by
  rw [eqLaw, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi, sup_eq_left.2 ht]

theorem B_nonneg_ae {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    ∀ᵐ ω ∂P, 0 ≤ s.B ω := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  rw [ae_iff]
  have h1 : {a | ¬ 0 ≤ s.B a} = s.B ⁻¹' Set.Iio 0 := by ext a; simp
  rw [h1, ← Measure.map_apply hB measurableSet_Iio, hs.law_B]
  simp [bernoulliLaw]

/-- **`E W_t = μ_on / μ`** for every `t ≥ 0`. -/
theorem mean_W [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {t : ℝ} (ht : 0 ≤ t) :
    P[s.W t] = mean Fon / mu Fon Foff := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  set kB : ℝ → ℝ≥0∞ := (Set.Ioi t).indicator 1 with hkB
  have hkBm : Measurable kB := measurable_const.indicator measurableSet_Ioi
  set c : ℝ≥0∞ := ENNReal.ofReal (mu Fon Foff)⁻¹ with hc
  set φ : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (Fbar Fon v) with hφ
  -- the renewal part
  have hren : ∑' n, ∫⁻ ω, kON t (s.Tn n ω, s.X n ω) ∂P = c * ∫⁻ v in Set.Ico 0 t, φ v := by
    rw [source_renewal_X hon0 hoff0 hon hoff hion hioff hs _ (kON_measurable t)]
    congr 1
    simp_rw [lintegral_kON]
    exact lintegral_reflect φ t
  -- the initial ON-period
  have hBX : IndepFun s.B s.X0 P :=
    hs.indep.indepFun (i := Sum.inl 0) (j := Sum.inl 1) (by simp)
  have hinit : ∫⁻ ω, ENNReal.ofReal (s.B ω) * kB (s.X0 ω) ∂P = c * ∫⁻ v in Set.Ioi t, φ v := by
    have hF : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * kB p.2) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul (hkBm.comp measurable_snd)
    rw [lintegral_indep_pair hB hX0 hBX hF, hs.law_X0, hs.law_B]
    simp_rw [lintegral_const_mul _ hkBm]
    rw [lintegral_mul_const _ ENNReal.measurable_ofReal, lintegral_bernoulli, hkB,
      lintegral_indicator_one measurableSet_Ioi, eqLaw_Ioi Fon ht,
      ← lintegral_const_mul _ ((Fbar_measurable Fon).div_const _).ennreal_ofReal, hc,
      ← lintegral_const_mul _ (Fbar_measurable Fon).ennreal_ofReal]
    refine lintegral_congr fun v => ?_
    rw [← ENNReal.ofReal_mul (div_nonneg hon.le hmu.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hmu.le)]
    congr 1
    field_simp
  -- the function whose lintegral is computed
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (s.B ω) * kB (s.X0 ω) +
    ∑' n, kON t (s.Tn n ω, s.X n ω) with hg
  have hkm : ∀ n, Measurable (fun ω => kON t (s.Tn n ω, s.X n ω)) := fun n =>
    (kON_measurable t).comp ((Tn_measurable hs n).prodMk (hs.measurable (Sum.inr (Sum.inl n))))
  have hm1 : Measurable (fun ω => ENNReal.ofReal (s.B ω) * kB (s.X0 ω)) :=
    (ENNReal.measurable_ofReal.comp hB).mul (hkBm.comp hX0)
  have hgm : Measurable g := hm1.add (Measurable.ennreal_tsum hkm)
  have hgint : ∫⁻ ω, g ω ∂P = c * ENNReal.ofReal (mean Fon) := by
    show ∫⁻ ω, (ENNReal.ofReal (s.B ω) * kB (s.X0 ω) + ∑' n, kON t (s.Tn n ω, s.X n ω)) ∂P = _
    rw [lintegral_add_left hm1,
      lintegral_tsum (fun n => (hkm n).aemeasurable), hinit, hren, ← mul_add,
      ← lintegral_Fbar_eq_mean Fon hon0 hion]
    congr 1
    rw [setLIntegral_congr (Ioi_ae_eq_Ici (a := t)), add_comm,
      ← lintegral_union measurableSet_Ici (Set.disjoint_left.2 fun v h1 h2 => by
        simp only [Set.mem_Ico, Set.mem_Ici] at h1 h2; linarith [h1.2]),
      Set.Ico_union_Ici_eq_Ici ht]
    exact setLIntegral_congr Ioi_ae_eq_Ici.symm
  have hfin : ∫⁻ ω, g ω ∂P ≠ ∞ := by
    rw [hgint]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hglt := ae_lt_top' hgm.aemeasurable hfin
  -- `W t = (g).toReal` almost surely
  have hWae : s.W t =ᵐ[P] fun ω => (g ω).toReal := by
    filter_upwards [hglt, B_nonneg_ae hs] with ω hω hBω
    have hsum_ne : ∑' n, kON t (s.Tn n ω, s.X n ω) ≠ ∞ :=
      ne_top_of_le_ne_top hω.ne (le_add_self)
    have hsumm : Summable (fun n => (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator
        (fun _ => (1 : ℝ)) t) := by
      have := ENNReal.summable_toReal hsum_ne
      refine this.congr fun n => ?_
      rw [← ofReal_ind_Ico, ENNReal.toReal_ofReal (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
    have hnn1 : 0 ≤ s.B ω * (Set.Ico 0 (s.X0 ω)).indicator (fun _ => (1 : ℝ)) t :=
      mul_nonneg hBω (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hnn2 : 0 ≤ ∑' n : ℕ, (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator
        (fun _ => (1 : ℝ)) t := tsum_nonneg fun n => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hW : ENNReal.ofReal (s.W t ω) = g ω := by
      rw [Source.W, ENNReal.ofReal_add hnn1 hnn2, ENNReal.ofReal_mul hBω,
        ENNReal.ofReal_tsum_of_nonneg (fun n => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hsumm]
      simp_rw [ofReal_ind_Ico]
      congr 2
      by_cases hx : t < s.X0 ω
      · rw [Set.indicator_of_mem (show t ∈ Set.Ico 0 (s.X0 ω) from ⟨ht, hx⟩), hkB,
          Set.indicator_of_mem (show s.X0 ω ∈ Set.Ioi t from hx)]
        simp
      · rw [Set.indicator_of_notMem (show t ∉ Set.Ico 0 (s.X0 ω) from fun h => hx h.2), hkB,
          Set.indicator_of_notMem (show s.X0 ω ∉ Set.Ioi t from hx)]
        simp
    have hWnn : 0 ≤ s.W t ω := by rw [Source.W]; exact add_nonneg hnn1 hnn2
    rw [← hW, ENNReal.toReal_ofReal hWnn]
  rw [integral_congr_ae hWae, integral_toReal hgm.aemeasurable hglt, hgint, hc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hmu.le),
    ENNReal.toReal_ofReal hon.le, div_eq_inv_mul]

end MeanW

end NetTraffic.OnOffFBM.Lib

/-! ### C2a step 5 infrastructure: laws of cycle blocks and the almost-sure good set -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Sum of the cycles with index in `[a, a + j)`. -/
def blockSum (s : Source Ω) (a j : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Ico a (a + j), srcZ s k ω

theorem blockSum_measurable {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (a j : ℕ) : Measurable (blockSum s a j) :=
  Finset.measurable_sum _ fun k _ => srcZ_measurable hs k

theorem blockSum_eq (s : Source Ω) (a j : ℕ) (ω : Ω) :
    blockSum s a j ω = ∑ i ∈ idxZ (Ico a (a + j)), s.family i ω := by
  rw [sum_idxZ]; rfl

/-- The law of a block of `j` consecutive cycles is the law of the first `j` cycles. -/
theorem map_blockSum [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (a : ℕ) :
    ∀ j, P.map (blockSum s a j) = P.map (psum (srcZ s) j)
  | 0 => by
    have h1 : blockSum s a 0 = fun _ => 0 := by funext ω; simp [blockSum]
    have h2 : psum (srcZ s) 0 = fun _ => 0 := by funext ω; simp [psum]
    rw [h1, h2]
  | j + 1 => by
    have h1 : blockSum s a (j + 1) = blockSum s a j + srcZ s (a + j) := by
      funext ω
      simp only [blockSum, Pi.add_apply]
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h2 : psum (srcZ s) (j + 1) = psum (srcZ s) j + srcZ s j := by
      funext ω
      simp only [psum, Pi.add_apply]
      rw [Finset.sum_range_succ]
    have hi1 : IndepFun (blockSum s a j) (srcZ s (a + j)) P := by
      have h := indepFun_finset_sum hs.indep hs.measurable (idxZ (Ico a (a + j))) (idxZ {a + j})
        (disjoint_idxZ (Finset.disjoint_singleton_right.2 (by simp)))
      convert h using 1
      · funext ω; exact blockSum_eq s a j ω
      · funext ω; exact srcZ_eq s (a + j) ω
    rw [h1, h2, hi1.map_add_eq_map_conv_map (blockSum_measurable hs a j) (srcZ_measurable hs _),
      (indep_psum_srcZ hs j).map_add_eq_map_conv_map (psum_measurable (srcZ_measurable hs) j)
        (srcZ_measurable hs _),
      map_blockSum hs a j, map_srcZ hs, map_srcZ hs]

theorem nonneg_ae_of_map {f : Ω → ℝ} (hf : Measurable f) {F : Measure ℝ} (hlaw : P.map f = F)
    (h0 : F (Set.Iio 0) = 0) : ∀ᵐ ω ∂P, 0 ≤ f ω := by
  rw [ae_iff]
  have h1 : {a | ¬ 0 ≤ f a} = f ⁻¹' Set.Iio 0 := by ext a; simp
  rw [h1, ← Measure.map_apply hf measurableSet_Iio, hlaw, h0]

theorem eqLaw_Iio (F : Measure ℝ) : eqLaw F (Set.Iio 0) = 0 := by
  rw [eqLaw, withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false,
      iff_false, not_and, not_lt]; intro h; exact h.le
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

theorem B_zero_or_one_ae {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    ∀ᵐ ω ∂P, s.B ω = 0 ∨ s.B ω = 1 := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hset : MeasurableSet (({0, 1} : Set ℝ)ᶜ) :=
    ((measurableSet_singleton 1).insert 0).compl
  rw [ae_iff]
  have h1 : {a | ¬ (s.B a = 0 ∨ s.B a = 1)} = s.B ⁻¹' (({0, 1} : Set ℝ)ᶜ) := by
    ext a; simp
  rw [h1, ← Measure.map_apply hB hset, hs.law_B, bernoulliLaw]
  simp [Measure.dirac_apply' _ hset]

/-- The almost-sure good set of a source: `B ∈ {0, 1}` and all periods are non-negative. -/
theorem good_ae {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0) :
    ∀ᵐ ω ∂P, (s.B ω = 0 ∨ s.B ω = 1) ∧ 0 ≤ s.X0 ω ∧ 0 ≤ s.Y0 ω ∧ 0 ≤ s.Yoff ω ∧
      ∀ n, 0 ≤ s.X n ω ∧ 0 ≤ s.Y n ω := by
  have hX : ∀ᵐ ω ∂P, ∀ n, 0 ≤ s.X n ω := ae_all_iff.2 fun n =>
    nonneg_ae_of_map (hs.measurable (Sum.inr (Sum.inl n))) (hs.law_X n) hon0
  have hY : ∀ᵐ ω ∂P, ∀ n, 0 ≤ s.Y n ω := ae_all_iff.2 fun n =>
    nonneg_ae_of_map (hs.measurable (Sum.inr (Sum.inr n))) (hs.law_Y n) hoff0
  filter_upwards [B_zero_or_one_ae hs, hX, hY,
    nonneg_ae_of_map (hs.measurable (Sum.inl 1)) hs.law_X0 (eqLaw_Iio Fon),
    nonneg_ae_of_map (hs.measurable (Sum.inl 2)) hs.law_Y0 (eqLaw_Iio Foff),
    nonneg_ae_of_map (hs.measurable (Sum.inl 3)) hs.law_Yoff hoff0] with ω h1 h2 h3 h4 h5 h6
  exact ⟨h1, h4, h5, h6, fun n => ⟨h2 n, h3 n⟩⟩

end Block

end NetTraffic.OnOffFBM.Lib

/-! ### C2a step 5a: the law of the future after cycle `n` -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section Future

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem indep_blockSum_X {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (a j : ℕ) : IndepFun (blockSum s a j) (s.X (a + j)) P := by
  have hd : Disjoint (idxZ (Ico a (a + j))) {Sum.inr (Sum.inl (a + j))} := by
    rw [Finset.disjoint_singleton_right]; simp [idxZ]
  have h := indepFun_finset_sum hs.indep hs.measurable _ _ hd
  convert h using 1
  · funext ω; exact blockSum_eq s a j ω
  · funext ω; rw [Finset.sum_singleton]; rfl

theorem indep_Y_future {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n j : ℕ) :
    IndepFun (s.Y n) (fun ω => (blockSum s (n + 1) j ω, s.X (n + 1 + j) ω)) P := by
  set T : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := idxZ (Ico (n + 1) (n + 1 + j)) ∪ {Sum.inr (Sum.inl (n + 1 + j))}
    with hT
  have hd : Disjoint ({Sum.inr (Sum.inr n)} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) T := by
    rw [Finset.disjoint_singleton_left, hT]
    simp [idxZ]
  have hmem : ∀ i ∈ idxZ (Ico (n + 1) (n + 1 + j)), i ∈ T := fun i hi => Finset.mem_union_left _ hi
  have hmemX : Sum.inr (Sum.inl (n + 1 + j)) ∈ T := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have h := (hs.indep.indepFun_finset _ _ hd hs.measurable).comp
    (φ := fun x : ({Sum.inr (Sum.inr n)} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inr (Sum.inr n), Finset.mem_singleton_self _⟩)
    (ψ := fun x : T → ℝ =>
      (∑ i ∈ (idxZ (Ico (n + 1) (n + 1 + j))).attach, x ⟨i.1, hmem i.1 i.2⟩, x ⟨_, hmemX⟩))
    (measurable_pi_apply _ : Measurable fun x : ({Sum.inr (Sum.inr n)} :
      Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ => x ⟨Sum.inr (Sum.inr n), Finset.mem_singleton_self _⟩)
    (Measurable.prodMk (Finset.measurable_sum _ fun i _ => measurable_pi_apply _)
      (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, hmemX⟩))
  convert h using 1
  · funext ω
    rfl
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (Ico (n + 1) (n + 1 + j))) (fun i => s.family i ω), ← blockSum_eq]
    rfl

/-- **Law of the future after cycle `n`**: `(Y_n, Z_{n+1} + … + Z_{n+j}, X_{n+1+j}) ∼
F_off ⊗ (law(S_j) ⊗ F_on)`, independent of `n`. -/
theorem law_future [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (n j : ℕ) :
    P.map (fun ω => (s.Y n ω, blockSum s (n + 1) j ω, s.X (n + 1 + j) ω)) =
      Foff.prod ((P.map (psum (srcZ s) j)).prod Fon) := by
  have hY : Measurable (s.Y n) := hs.measurable (Sum.inr (Sum.inr n))
  have hX : Measurable (s.X (n + 1 + j)) := hs.measurable (Sum.inr (Sum.inl (n + 1 + j)))
  have hBm := blockSum_measurable hs (n + 1) j
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable
    (hBm.prodMk hX).aemeasurable).1 (indep_Y_future hs n j)
  have h2 := (indepFun_iff_map_prod_eq_prod_map_map hBm.aemeasurable hX.aemeasurable).1
    (indep_blockSum_X hs (n + 1) j)
  rw [h1, h2, hs.law_Y n, hs.law_X (n + 1 + j), map_blockSum hs (n + 1) j]

theorem lintegral_indep_gen [IsProbabilityMeasure P] {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (hUV : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ u, (∫⁻ v, F (u, v) ∂(P.map V)) ∂(P.map U) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hUV
  rw [← lintegral_prod _ hF.aemeasurable, ← h, lintegral_map hF (hU.prodMk hV)]

/-- The past `(T_n, X_n)` is independent of the future `(Y_n, Z_{n+1}+…+Z_{n+j}, X_{n+1+j})`. -/
theorem indep_past_future {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (n j : ℕ) :
    IndepFun (fun ω => (s.Tn n ω, s.X n ω))
      (fun ω => (s.Y n ω, blockSum s (n + 1) j ω, s.X (n + 1 + j) ω)) P := by
  set S : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := idx0 ∪ idxZ (range n) ∪ {Sum.inr (Sum.inl n)} with hS
  set T : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := ({Sum.inr (Sum.inr n)} ∪ idxZ (Ico (n + 1) (n + 1 + j))) ∪
    {Sum.inr (Sum.inl (n + 1 + j))} with hT
  have hd : Disjoint S T := by
    rw [hS, hT, Finset.disjoint_left]
    rintro (a | (a | a)) h1 h2 <;> simp [idx0, idxZ] at h1 h2 <;> omega
  have m0 : ∀ i : Fin 4, Sum.inl i ∈ S := fun i => by simp [hS, idx0]
  have mZ : ∀ i ∈ idxZ (range n), i ∈ S := fun i hi => by
    rw [hS]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have mX : Sum.inr (Sum.inl n) ∈ S := by rw [hS]; exact Finset.mem_union_right _ (by simp)
  have tY : Sum.inr (Sum.inr n) ∈ T := by simp [hT]
  have tZ : ∀ i ∈ idxZ (Ico (n + 1) (n + 1 + j)), i ∈ T := fun i hi => by
    rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have tX : Sum.inr (Sum.inl (n + 1 + j)) ∈ T := by rw [hT]; exact Finset.mem_union_right _ (by simp)
  have h := (hs.indep.indepFun_finset _ _ hd hs.measurable).comp
    (φ := fun x : S → ℝ =>
      ((x ⟨_, m0 0⟩ * (x ⟨_, m0 1⟩ + x ⟨_, m0 3⟩) + (1 - x ⟨_, m0 0⟩) * x ⟨_, m0 2⟩) +
        ∑ i ∈ (idxZ (range n)).attach, x ⟨i.1, mZ i.1 i.2⟩, x ⟨_, mX⟩))
    (ψ := fun x : T → ℝ =>
      (x ⟨_, tY⟩, ∑ i ∈ (idxZ (Ico (n + 1) (n + 1 + j))).attach, x ⟨i.1, tZ i.1 i.2⟩, x ⟨_, tX⟩))
    (Measurable.prodMk (Measurable.add (by fun_prop)
        (Finset.measurable_sum _ fun i _ => measurable_pi_apply _))
      (measurable_pi_apply _ : Measurable fun x : S → ℝ => x ⟨_, mX⟩))
    (Measurable.prodMk (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, tY⟩)
      (Measurable.prodMk (Finset.measurable_sum _ fun i _ => measurable_pi_apply _)
        (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, tX⟩)))
  convert h using 1
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (range n)) (fun i => s.family i ω), Tn_eq_sum]
    rfl
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (Ico (n + 1) (n + 1 + j))) (fun i => s.family i ω), ← blockSum_eq]
    rfl

end Future

end NetTraffic.OnOffFBM.Lib

/-! ### C2a step 5: the second moment `E[W_u W_v]` depends only on `v - u`

`E[W_u W_v] = μ⁻¹ ∫_0^∞ F̄_on(z) (1{v-u < z} + R(v-u-z)) dz` (`0 ≤ u ≤ v`), where
`R(e) = Σ_j P(Y + S_j ≤ e < Y + S_j + X)` is the ON-probability at time `e` of the renewal
process started at the beginning of an OFF-period. -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section Cov2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Future kernel `(e, (y, b, x)) ↦ 1{y + b ≤ e < y + b + x}`. -/
noncomputable def kFut : ℝ × (ℝ × ℝ × ℝ) → ℝ≥0∞ :=
  Set.indicator {p : ℝ × (ℝ × ℝ × ℝ) | p.2.1 + p.2.2.1 ≤ p.1 ∧ p.1 < p.2.1 + p.2.2.1 + p.2.2.2} 1

theorem kFut_measurable : Measurable kFut := by
  refine Measurable.indicator measurable_const ?_
  have h1 : Measurable fun p : ℝ × (ℝ × ℝ × ℝ) => p.2.1 + p.2.2.1 :=
    (measurable_fst.comp measurable_snd).add
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have h2 : Measurable fun p : ℝ × (ℝ × ℝ × ℝ) => p.2.1 + p.2.2.1 + p.2.2.2 :=
    h1.add (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact (measurableSet_le h1 measurable_fst).inter (measurableSet_lt measurable_fst h2)

theorem kON_shift (v c y b x : ℝ) : kON v (c + y + b, x) = kFut (v - c, (y, b, x)) := by
  simp only [kON, kFut, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  by_cases h : c + y + b ≤ v ∧ v < c + y + b + x
  · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
  · rw [if_neg h, if_neg (fun h2 => h ⟨by linarith [h2.1], by linarith [h2.2]⟩)]

/-- `R(e) = Σ_j P(Y + S_j ≤ e < Y + S_j + X)` with `Y ∼ F_off`, `S_j ∼ ν j`, `X ∼ F_on`. -/
noncomputable def Rfun (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (e : ℝ) : ℝ≥0∞ :=
  ∑' j, ∫⁻ w, kFut (e, w) ∂(Foff.prod ((ν j).prod Fon))

theorem Rfun_measurable (Fon Foff : Measure ℝ) [SFinite Fon] [SFinite Foff] (ν : ℕ → Measure ℝ)
    [∀ j, SFinite (ν j)] : Measurable (Rfun Fon Foff ν) :=
  Measurable.ennreal_tsum fun _ => kFut_measurable.lintegral_prod_right'

/-- `h_v(y) = 1{v < y} + R(v - y)`: the ON-indicator at `v` given an ON-period ending at `y`. -/
noncomputable def hfun (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (v y : ℝ) : ℝ≥0∞ :=
  (Set.Ioi v).indicator 1 y + Rfun Fon Foff ν (v - y)

theorem hfun_measurable (Fon Foff : Measure ℝ) [SFinite Fon] [SFinite Foff] (ν : ℕ → Measure ℝ)
    [∀ j, SFinite (ν j)] (v : ℝ) : Measurable (hfun Fon Foff ν v) := by
  show Measurable fun y => (Set.Ioi v).indicator (1 : ℝ → ℝ≥0∞) y + Rfun Fon Foff ν (v - y)
  exact (measurable_const.indicator measurableSet_Ioi).add
    ((Rfun_measurable Fon Foff ν).comp (measurable_const.sub measurable_id))

/-- The stationary second-moment kernel `K(d) = ∫_0^∞ F̄_on(z) (1{d < z} + R(d - z)) dz`. -/
noncomputable def Kfun (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (d : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (Fbar Fon z) * hfun Fon Foff ν d z

theorem Tn_succ_block (s : Source Ω) (n j : ℕ) (ω : Ω) :
    s.Tn (n + 1 + j) ω = s.Tn n ω + s.X n ω + s.Y n ω + blockSum s (n + 1) j ω := by
  simp only [Source.Tn, blockSum, srcZ]
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le n) (show n ≤ n + 1 + j by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show n < n + 1 + j by omega)]
  ring

/-- Renewal after cycle `n`: `Σ_j E[g(T_n, X_n) 1{T_{n+1+j} ≤ v < T_{n+1+j} + X_{n+1+j}}]
= E[g(T_n, X_n) R(v - T_n - X_n)]`. -/
theorem future_sum [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (n : ℕ)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) (v : ℝ) :
    ∑' j, ∫⁻ ω, g (s.Tn n ω, s.X n ω) * kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω) ∂P =
      ∫⁻ ω, g (s.Tn n ω, s.X n ω) *
        Rfun Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - (s.Tn n ω + s.X n ω)) ∂P := by
  have hU : Measurable (fun ω => (s.Tn n ω, s.X n ω)) :=
    (Tn_measurable hs n).prodMk (hs.measurable (Sum.inr (Sum.inl n)))
  have hE : Measurable (fun ω => v - (s.Tn n ω + s.X n ω)) :=
    measurable_const.sub ((Tn_measurable hs n).add (hs.measurable (Sum.inr (Sum.inl n))))
  have hj : ∀ j, ∫⁻ ω, g (s.Tn n ω, s.X n ω) * kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω) ∂P =
      ∫⁻ ω, g (s.Tn n ω, s.X n ω) * ∫⁻ w, kFut (v - (s.Tn n ω + s.X n ω), w)
        ∂(Foff.prod ((P.map (psum (srcZ s) j)).prod Fon)) ∂P := by
    intro j
    have hV : Measurable (fun ω => (s.Y n ω, blockSum s (n + 1) j ω, s.X (n + 1 + j) ω)) :=
      (hs.measurable (Sum.inr (Sum.inr n))).prodMk ((blockSum_measurable hs (n + 1) j).prodMk
        (hs.measurable (Sum.inr (Sum.inl (n + 1 + j)))))
    have hFm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
        g p.1 * kFut (v - (p.1.1 + p.1.2), p.2)) :=
      (hg.comp measurable_fst).mul (kFut_measurable.comp
        ((measurable_const.sub ((measurable_fst.comp measurable_fst).add
          (measurable_snd.comp measurable_fst))).prodMk measurable_snd))
    have h1 : ∀ ω, g (s.Tn n ω, s.X n ω) * kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω) =
        g (s.Tn n ω, s.X n ω) * kFut (v - (s.Tn n ω + s.X n ω),
          (s.Y n ω, blockSum s (n + 1) j ω, s.X (n + 1 + j) ω)) := by
      intro ω
      rw [Tn_succ_block, kON_shift]
    have key := lintegral_indep_gen hU hV (indep_past_future hs n j) hFm
    try simp only at key
    rw [lintegral_congr h1, key, law_future hs n j]
    have hG : Measurable (fun u : ℝ × ℝ => ∫⁻ w, g u * kFut (v - (u.1 + u.2), w)
        ∂(Foff.prod ((P.map (psum (srcZ s) j)).prod Fon))) := hFm.lintegral_prod_right'
    rw [lintegral_map hG hU]
    refine lintegral_congr fun ω => ?_
    exact lintegral_const_mul _ (kFut_measurable.comp measurable_prodMk_left)
  have hmj : ∀ j, Measurable (fun ω => g (s.Tn n ω, s.X n ω) *
      ∫⁻ w, kFut (v - (s.Tn n ω + s.X n ω), w)
        ∂(Foff.prod ((P.map (psum (srcZ s) j)).prod Fon))) := fun j =>
    (hg.comp hU).mul ((kFut_measurable.lintegral_prod_right').comp hE)
  rw [tsum_congr hj, ← lintegral_tsum (fun j => (hmj j).aemeasurable)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.tsum_mul_left]
  rfl

theorem indep_B_future {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (m : ℕ) :
    IndepFun (fun ω => (s.B ω, s.X0 ω)) (fun ω => (s.Yoff ω, psum (srcZ s) m ω, s.X m ω)) P := by
  set S : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := {Sum.inl 0, Sum.inl 1} with hS
  set T : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := ({Sum.inl 3} ∪ idxZ (range m)) ∪ {Sum.inr (Sum.inl m)}
    with hT
  have hd : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    rw [hS] at h1
    rw [hT] at h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with rfl | rfl <;> simp [idxZ] at h2
  have m0 : Sum.inl 0 ∈ S := by simp [hS]
  have m1 : Sum.inl 1 ∈ S := by simp [hS]
  have t3 : Sum.inl 3 ∈ T := by simp [hT]
  have tZ : ∀ i ∈ idxZ (range m), i ∈ T := fun i hi => by
    rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have tX : Sum.inr (Sum.inl m) ∈ T := by rw [hT]; exact Finset.mem_union_right _ (by simp)
  have h := (hs.indep.indepFun_finset _ _ hd hs.measurable).comp
    (φ := fun x : S → ℝ => (x ⟨_, m0⟩, x ⟨_, m1⟩))
    (ψ := fun x : T → ℝ =>
      (x ⟨_, t3⟩, ∑ i ∈ (idxZ (range m)).attach, x ⟨i.1, tZ i.1 i.2⟩, x ⟨_, tX⟩))
    (Measurable.prodMk (measurable_pi_apply _ : Measurable fun x : S → ℝ => x ⟨_, m0⟩)
      (measurable_pi_apply _ : Measurable fun x : S → ℝ => x ⟨_, m1⟩))
    (Measurable.prodMk (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, t3⟩)
      (Measurable.prodMk (Finset.measurable_sum _ fun i _ => measurable_pi_apply _)
        (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, tX⟩)))
  convert h using 1
  · funext ω
    rfl
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (range m)) (fun i => s.family i ω), ← psum_srcZ_eq]
    rfl

theorem indep_Yoff_future {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (m : ℕ) : IndepFun s.Yoff (fun ω => (psum (srcZ s) m ω, s.X m ω)) P := by
  set T : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := idxZ (range m) ∪ {Sum.inr (Sum.inl m)} with hT
  have hd : Disjoint ({Sum.inl 3} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) T := by
    rw [Finset.disjoint_singleton_left, hT]; simp [idxZ]
  have tZ : ∀ i ∈ idxZ (range m), i ∈ T := fun i hi => by
    rw [hT]; exact Finset.mem_union_left _ hi
  have tX : Sum.inr (Sum.inl m) ∈ T := by rw [hT]; exact Finset.mem_union_right _ (by simp)
  have h := (hs.indep.indepFun_finset _ _ hd hs.measurable).comp
    (φ := fun x : ({Sum.inl 3} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inl 3, Finset.mem_singleton_self _⟩)
    (ψ := fun x : T → ℝ => (∑ i ∈ (idxZ (range m)).attach, x ⟨i.1, tZ i.1 i.2⟩, x ⟨_, tX⟩))
    (measurable_pi_apply _ : Measurable fun x : ({Sum.inl 3} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inl 3, Finset.mem_singleton_self _⟩)
    (Measurable.prodMk (Finset.measurable_sum _ fun i _ => measurable_pi_apply _)
      (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, tX⟩))
  convert h using 1
  · funext ω
    rfl
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (range m)) (fun i => s.family i ω), ← psum_srcZ_eq]
    rfl

theorem law_B_future [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (m : ℕ) :
    P.map (fun ω => (s.Yoff ω, psum (srcZ s) m ω, s.X m ω)) =
      Foff.prod ((P.map (psum (srcZ s) m)).prod Fon) := by
  have hY : Measurable s.Yoff := hs.measurable (Sum.inl 3)
  have hX : Measurable (s.X m) := hs.measurable (Sum.inr (Sum.inl m))
  have hBm := psum_measurable (srcZ_measurable hs) m
  have hPX : IndepFun (psum (srcZ s) m) (s.X m) P := by
    have h0 := indep_blockSum_X hs 0 m
    rw [zero_add] at h0
    convert h0 using 1
    funext ω
    show ∑ i ∈ range m, srcZ s i ω = ∑ k ∈ Ico 0 (0 + m), srcZ s k ω
    rw [zero_add, Finset.range_eq_Ico]
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable
    (hBm.prodMk hX).aemeasurable).1 (indep_Yoff_future hs m)
  have h2 := (indepFun_iff_map_prod_eq_prod_map_map hBm.aemeasurable hX.aemeasurable).1 hPX
  rw [h1, h2, hs.law_Yoff, hs.law_X m]

/-- The future of the initial ON-period. -/
theorem B_future_sum [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) (v : ℝ) :
    ∑' m, ∫⁻ ω, g (s.B ω, s.X0 ω) * kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω) ∂P =
      ∫⁻ ω, g (s.B ω, s.X0 ω) *
        Rfun Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - s.X0 ω) ∂P := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hU : Measurable (fun ω => (s.B ω, s.X0 ω)) := hB.prodMk hX0
  have hj : ∀ m, ∫⁻ ω, g (s.B ω, s.X0 ω) *
        kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω) ∂P =
      ∫⁻ ω, g (s.B ω, s.X0 ω) * ∫⁻ w, kFut (v - s.X0 ω, w)
        ∂(Foff.prod ((P.map (psum (srcZ s) m)).prod Fon)) ∂P := by
    intro m
    have hV : Measurable (fun ω => (s.Yoff ω, psum (srcZ s) m ω, s.X m ω)) :=
      (hs.measurable (Sum.inl 3)).prodMk ((psum_measurable (srcZ_measurable hs) m).prodMk
        (hs.measurable (Sum.inr (Sum.inl m))))
    have hFm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => g p.1 * kFut (v - p.1.2, p.2)) :=
      (hg.comp measurable_fst).mul (kFut_measurable.comp
        ((measurable_const.sub (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
    have h1 : ∀ ω, g (s.B ω, s.X0 ω) * kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω) =
        g (s.B ω, s.X0 ω) * kFut (v - s.X0 ω, (s.Yoff ω, psum (srcZ s) m ω, s.X m ω)) :=
      fun ω => by rw [kON_shift]
    have key := lintegral_indep_gen hU hV (indep_B_future hs m) hFm
    try simp only at key
    rw [lintegral_congr h1, key, law_B_future hs m]
    have hG : Measurable (fun u : ℝ × ℝ => ∫⁻ w, g u * kFut (v - u.2, w)
        ∂(Foff.prod ((P.map (psum (srcZ s) m)).prod Fon))) := hFm.lintegral_prod_right'
    rw [lintegral_map hG hU]
    refine lintegral_congr fun ω => ?_
    exact lintegral_const_mul _ (kFut_measurable.comp measurable_prodMk_left)
  have hmj : ∀ m, Measurable (fun ω => g (s.B ω, s.X0 ω) * ∫⁻ w, kFut (v - s.X0 ω, w)
        ∂(Foff.prod ((P.map (psum (srcZ s) m)).prod Fon))) := fun m =>
    (hg.comp hU).mul ((kFut_measurable.lintegral_prod_right').comp (measurable_const.sub hX0))
  rw [tsum_congr hj, ← lintegral_tsum (fun m => (hmj m).aemeasurable)]
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.tsum_mul_left]
  rfl

/-! #### Pointwise structure on the almost-sure good set -/

/-- The almost-sure good set of a source (see `good_ae`). -/
def Good (s : Source Ω) (ω : Ω) : Prop :=
  (s.B ω = 0 ∨ s.B ω = 1) ∧ 0 ≤ s.X0 ω ∧ 0 ≤ s.Y0 ω ∧ 0 ≤ s.Yoff ω ∧
    ∀ n, 0 ≤ s.X n ω ∧ 0 ≤ s.Y n ω

theorem blockSum_nonneg {s : Source Ω} {ω : Ω} (hω : Good s ω) (a j : ℕ) :
    0 ≤ blockSum s a j ω :=
  Finset.sum_nonneg fun k _ => add_nonneg (hω.2.2.2.2 k).1 (hω.2.2.2.2 k).2

theorem psum_srcZ_nonneg {s : Source Ω} {ω : Ω} (hω : Good s ω) (m : ℕ) :
    0 ≤ psum (srcZ s) m ω :=
  Finset.sum_nonneg fun k _ => add_nonneg (hω.2.2.2.2 k).1 (hω.2.2.2.2 k).2

theorem Tn_add_X_le {s : Source Ω} {ω : Ω} (hω : Good s ω) {m n : ℕ} (h : m < n) :
    s.Tn m ω + s.X m ω ≤ s.Tn n ω := by
  obtain ⟨j, rfl⟩ : ∃ j, n = m + 1 + j := ⟨n - (m + 1), by omega⟩
  rw [Tn_succ_block]
  linarith [(hω.2.2.2.2 m).2, blockSum_nonneg hω (m + 1) j]

theorem Tn_of_B1 (s : Source Ω) {ω : Ω} (hB : s.B ω = 1) (n : ℕ) :
    s.Tn n ω = s.X0 ω + s.Yoff ω + psum (srcZ s) n ω := by
  simp only [Source.Tn, Source.T0, psum, srcZ, hB]
  ring

theorem kON_eq_zero {t r x : ℝ} (h : ¬ (r ≤ t ∧ t < r + x)) : kON t (r, x) = 0 :=
  Set.indicator_of_notMem (show (r, x) ∉ {p : ℝ × ℝ | p.1 ≤ t ∧ t < p.1 + p.2} from h) _

theorem kON_le_one (t : ℝ) (p : ℝ × ℝ) : kON t p ≤ 1 := by
  unfold kON
  exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)

theorem kON_disj {s : Source Ω} {ω : Ω} (hω : Good s ω) {m n : ℕ} (h : m < n) {u v : ℝ}
    (huv : u ≤ v) : kON u (s.Tn n ω, s.X n ω) * kON v (s.Tn m ω, s.X m ω) = 0 := by
  by_cases h1 : s.Tn n ω ≤ u
  · rw [kON_eq_zero (t := v) (fun h2 => by linarith [h2.2, Tn_add_X_le hω h]), mul_zero]
  · rw [kON_eq_zero (fun h2 => h1 h2.1), zero_mul]

theorem kON_same (t v r x : ℝ) (htv : t ≤ v) :
    kON t (r, x) * kON v (r, x) = kON t (r, x) * (Set.Ioi v).indicator 1 (r + x) := by
  by_cases h : r ≤ t ∧ t < r + x
  · congr 1
    simp only [kON, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioi, Pi.one_apply]
    by_cases h2 : v < r + x
    · rw [if_pos ⟨by linarith [h.1], h2⟩, if_pos h2]
    · rw [if_neg (fun h3 => h2 h3.2), if_neg h2]
  · rw [kON_eq_zero h, zero_mul, zero_mul]

theorem B_kON_zero {s : Source Ω} {ω : Ω} (hω : Good s ω) {u v : ℝ} (huv : u ≤ v) (n : ℕ) :
    kON u (s.Tn n ω, s.X n ω) * (ENNReal.ofReal (s.B ω) * (Set.Ioi v).indicator 1 (s.X0 ω)) =
      0 := by
  rcases hω.1 with hB | hB
  · simp [hB]
  · by_cases h1 : v < s.X0 ω
    · have hX := Tn_of_B1 s hB n
      rw [kON_eq_zero (fun h2 => by
        linarith [h2.1, hω.2.2.2.1, psum_srcZ_nonneg hω n]), zero_mul]
    · rw [Set.indicator_of_notMem (show s.X0 ω ∉ Set.Ioi v from h1), mul_zero, mul_zero]

theorem B_mul_B {s : Source Ω} {ω : Ω} (hω : Good s ω) :
    ENNReal.ofReal (s.B ω) * ENNReal.ofReal (s.B ω) = ENNReal.ofReal (s.B ω) := by
  rcases hω.1 with hB | hB <;> simp [hB]

theorem B_kON_eq {s : Source Ω} {ω : Ω} (hω : Good s ω) (v : ℝ) (n : ℕ) :
    ENNReal.ofReal (s.B ω) * kON v (s.Tn n ω, s.X n ω) =
      ENNReal.ofReal (s.B ω) * kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) n ω, s.X n ω) := by
  rcases hω.1 with hB | hB
  · simp [hB]
  · rw [Tn_of_B1 s hB n]

/-- `ofReal ∘ W_t`, written as an `ℝ≥0∞`-valued series. -/
noncomputable def gW (s : Source Ω) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (s.B ω) * (Set.Ioi t).indicator 1 (s.X0 ω) + ∑' n, kON t (s.Tn n ω, s.X n ω)

theorem gW_measurable {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (t : ℝ) : Measurable (gW s t) := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hkB : Measurable ((Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Ioi
  show Measurable fun ω => ENNReal.ofReal (s.B ω) * (Set.Ioi t).indicator 1 (s.X0 ω) +
    ∑' n, kON t (s.Tn n ω, s.X n ω)
  exact ((ENNReal.measurable_ofReal.comp hB).mul (hkB.comp hX0)).add
    (Measurable.ennreal_tsum fun n => (kON_measurable t).comp
      ((Tn_measurable hs n).prodMk (hs.measurable (Sum.inr (Sum.inl n)))))

theorem tsum_kON_le_one {s : Source Ω} {ω : Ω} (hω : Good s ω) (t : ℝ) :
    ∑' n, kON t (s.Tn n ω, s.X n ω) ≤ 1 := by
  by_cases h : ∃ n, kON t (s.Tn n ω, s.X n ω) ≠ 0
  · obtain ⟨n, hn⟩ := h
    rw [tsum_eq_single n (fun m hm => ?_)]
    · exact kON_le_one t _
    · rcases lt_or_gt_of_ne hm with h1 | h1
      · exact (mul_eq_zero.1 (kON_disj hω h1 (le_refl t))).resolve_left hn
      · exact (mul_eq_zero.1 (kON_disj hω h1 (le_refl t))).resolve_right hn
  · push_neg at h
    simp [h]

theorem ofReal_W {s : Source Ω} {ω : Ω} (hω : Good s ω) {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (s.W t ω) = gW s t ω ∧ 0 ≤ s.W t ω := by
  have hBω : 0 ≤ s.B ω := by rcases hω.1 with h | h <;> rw [h] <;> norm_num
  have hsum_ne : ∑' n, kON t (s.Tn n ω, s.X n ω) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_kON_le_one hω t)
  have hsumm : Summable (fun n => (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator
      (fun _ => (1 : ℝ)) t) := by
    have := ENNReal.summable_toReal hsum_ne
    refine this.congr fun n => ?_
    rw [← ofReal_ind_Ico, ENNReal.toReal_ofReal (Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
  have hnn1 : 0 ≤ s.B ω * (Set.Ico 0 (s.X0 ω)).indicator (fun _ => (1 : ℝ)) t :=
    mul_nonneg hBω (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hnn2 : 0 ≤ ∑' n : ℕ, (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator
      (fun _ => (1 : ℝ)) t := tsum_nonneg fun n => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  refine ⟨?_, by rw [Source.W]; exact add_nonneg hnn1 hnn2⟩
  rw [Source.W, ENNReal.ofReal_add hnn1 hnn2, ENNReal.ofReal_mul hBω,
    ENNReal.ofReal_tsum_of_nonneg (fun n => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hsumm,
    gW]
  simp_rw [ofReal_ind_Ico]
  congr 2
  by_cases hx : t < s.X0 ω
  · rw [Set.indicator_of_mem (show t ∈ Set.Ico 0 (s.X0 ω) from ⟨ht, hx⟩),
      Set.indicator_of_mem (show s.X0 ω ∈ Set.Ioi t from hx)]
    simp
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ico 0 (s.X0 ω) from fun h => hx h.2),
      Set.indicator_of_notMem (show s.X0 ω ∉ Set.Ioi t from hx)]
    simp

/-- Pointwise decomposition of `W_u W_v` (`u ≤ v`) by the ON-period covering `u`. -/
theorem gW_mul {s : Source Ω} {ω : Ω} (hω : Good s ω) {u v : ℝ} (huv : u ≤ v) :
    gW s u ω * gW s v ω =
      ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          ((Set.Ioi v).indicator 1 (s.X0 ω) +
            ∑' m, kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω)) +
        ∑' n, kON u (s.Tn n ω, s.X n ω) *
          ((Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
            ∑' j, kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω)) := by
  have hBB : ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
      (ENNReal.ofReal (s.B ω) * (Set.Ioi v).indicator 1 (s.X0 ω)) =
      ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
        (Set.Ioi v).indicator 1 (s.X0 ω) := by
    calc _ = (ENNReal.ofReal (s.B ω) * ENNReal.ofReal (s.B ω)) *
          (Set.Ioi u).indicator 1 (s.X0 ω) * (Set.Ioi v).indicator 1 (s.X0 ω) := by ring
      _ = _ := by rw [B_mul_B hω]
  have hBk : ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
      ∑' m, kON v (s.Tn m ω, s.X m ω) =
      ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
        ∑' m, kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [mul_right_comm, B_kON_eq hω v m, mul_right_comm]
  have hkB : (∑' n, kON u (s.Tn n ω, s.X n ω)) *
      (ENNReal.ofReal (s.B ω) * (Set.Ioi v).indicator 1 (s.X0 ω)) = 0 := by
    rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_eq_zero.2 fun n => B_kON_zero hω huv n
  have hkk : (∑' n, kON u (s.Tn n ω, s.X n ω)) * (∑' m, kON v (s.Tn m ω, s.X m ω)) =
      ∑' n, kON u (s.Tn n ω, s.X n ω) *
          ((Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
            ∑' j, kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω)) := by
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun n => ?_
    have hsplit : ∑' m, kON v (s.Tn m ω, s.X m ω) =
        ∑ m ∈ range (n + 1), kON v (s.Tn m ω, s.X m ω) +
          ∑' j, kON v (s.Tn (j + (n + 1)) ω, s.X (j + (n + 1)) ω) :=
      (ENNReal.summable.sum_add_tsum_nat_add').symm
    rw [hsplit, mul_add, mul_add, Finset.mul_sum, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun m hm => kON_disj hω (Finset.mem_range.1 hm) huv),
      zero_add, kON_same u v _ _ huv]
    congr 2
    exact tsum_congr fun j => by rw [Nat.add_comm j (n + 1)]
  rw [gW, gW, add_mul, mul_add, mul_add, hBB, hBk, hkB, hkk, zero_add, mul_add]

/-! #### The three integrals -/

theorem lintegral_B_X0 [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff) {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ ω, ENNReal.ofReal (s.B ω) * ψ (s.X0 ω) ∂P =
      ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ y in Set.Ioi 0, ENNReal.ofReal (Fbar Fon y) * ψ y := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hBX : IndepFun s.B s.X0 P :=
    hs.indep.indepFun (i := Sum.inl 0) (j := Sum.inl 1) (by simp)
  have hFb := Fbar_measurable Fon
  have hF : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ψ p.2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul (hψ.comp measurable_snd)
  rw [lintegral_indep_pair hB hX0 hBX hF, hs.law_X0, hs.law_B]
  simp_rw [lintegral_const_mul _ hψ]
  rw [lintegral_mul_const _ ENNReal.measurable_ofReal, lintegral_bernoulli, eqLaw,
    lintegral_withDensity_eq_lintegral_mul _ (hFb.div_const _).ennreal_ofReal hψ]
  simp only [Pi.mul_apply]
  have hd1 : Measurable fun y => ENNReal.ofReal (Fbar Fon y / mean Fon) * ψ y :=
    ((hFb.div_const _).ennreal_ofReal).mul hψ
  have hd2 : Measurable fun y => ENNReal.ofReal (Fbar Fon y) * ψ y := hFb.ennreal_ofReal.mul hψ
  rw [← lintegral_const_mul _ hd1, ← lintegral_const_mul _ hd2]
  refine lintegral_congr fun y => ?_
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hon.le hmu.le),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hmu.le)]
  congr 2
  field_simp

theorem lintegral_A_B [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          ((Set.Ioi v).indicator 1 (s.X0 ω) +
            ∑' m, kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω)) ∂P =
      ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ y in Set.Ioi u, ENNReal.ofReal (Fbar Fon y) *
        hfun Fon Foff (fun j => P.map (psum (srcZ s) j)) v y := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hYoff : Measurable s.Yoff := hs.measurable (Sum.inl 3)
  have hX : ∀ n, Measurable (s.X n) := fun n => hs.measurable (Sum.inr (Sum.inl n))
  have hkB : ∀ t : ℝ, Measurable ((Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞)) := fun t =>
    measurable_const.indicator measurableSet_Ioi
  have hR := Rfun_measurable Fon Foff (fun j => P.map (psum (srcZ s) j))
  have hH := hfun_measurable Fon Foff (fun j => P.map (psum (srcZ s) j)) v
  have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (Set.Ioi u).indicator 1 p.2) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul ((hkB u).comp measurable_snd)
  have h1 : ∀ ω, ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          ((Set.Ioi v).indicator 1 (s.X0 ω) +
            ∑' m, kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω)) =
      ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          (Set.Ioi v).indicator 1 (s.X0 ω) +
        ∑' m, ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω) := fun ω => by
    rw [mul_add, ENNReal.tsum_mul_left]
  have hm1 : Measurable (fun ω => ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
      (Set.Ioi v).indicator 1 (s.X0 ω)) :=
    ((ENNReal.measurable_ofReal.comp hB).mul ((hkB u).comp hX0)).mul ((hkB v).comp hX0)
  have hm2 : ∀ m, Measurable (fun ω => ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
      kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω)) := fun m =>
    ((ENNReal.measurable_ofReal.comp hB).mul ((hkB u).comp hX0)).mul ((kON_measurable v).comp
      (((hX0.add hYoff).add (psum_measurable (srcZ_measurable hs) m)).prodMk (hX m)))
  have key := B_future_sum hs
    (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * (Set.Ioi u).indicator 1 p.2) hg v
  try simp only at key
  rw [lintegral_congr h1, lintegral_add_left hm1, lintegral_tsum (fun m => (hm2 m).aemeasurable),
    key, ← lintegral_add_left hm1]
  have h2 : ∀ ω, ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
        (Set.Ioi v).indicator 1 (s.X0 ω) +
      ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
        Rfun Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - s.X0 ω) =
      ENNReal.ofReal (s.B ω) *
        (Set.Ioi u).indicator (hfun Fon Foff (fun j => P.map (psum (srcZ s) j)) v) (s.X0 ω) := by
    intro ω
    by_cases hx : u < s.X0 ω
    · rw [Set.indicator_of_mem (show s.X0 ω ∈ Set.Ioi u from hx),
        Set.indicator_of_mem (show s.X0 ω ∈ Set.Ioi u from hx), hfun, Pi.one_apply, mul_one,
        mul_add]
    · rw [Set.indicator_of_notMem (show s.X0 ω ∉ Set.Ioi u from hx),
        Set.indicator_of_notMem (show s.X0 ω ∉ Set.Ioi u from hx)]
      simp
  rw [lintegral_congr h2, lintegral_B_X0 hon hoff hs _ (hH.indicator measurableSet_Ioi)]
  congr 1
  have h3 : ∀ y, ENNReal.ofReal (Fbar Fon y) *
        (Set.Ioi u).indicator (hfun Fon Foff (fun j => P.map (psum (srcZ s) j)) v) y =
      (Set.Ioi u).indicator (fun y => ENNReal.ofReal (Fbar Fon y) *
        hfun Fon Foff (fun j => P.map (psum (srcZ s) j)) v y) y := by
    intro y
    by_cases hy : u < y
    · rw [Set.indicator_of_mem (show y ∈ Set.Ioi u from hy),
        Set.indicator_of_mem (show y ∈ Set.Ioi u from hy)]
    · rw [Set.indicator_of_notMem (show y ∉ Set.Ioi u from hy),
        Set.indicator_of_notMem (show y ∉ Set.Ioi u from hy), mul_zero]
  rw [lintegral_congr h3, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_eq_left.2 hu]

theorem lintegral_A_n [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (u v : ℝ) :
    ∑' n, ∫⁻ ω, kON u (s.Tn n ω, s.X n ω) *
          ((Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
            ∑' j, kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω)) ∂P =
      ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ r in Set.Ioi 0, ∫⁻ x, kON u (r, x) *
        hfun Fon Foff (fun j => P.map (psum (srcZ s) j)) v (r + x) ∂Fon := by
  have hX : ∀ n, Measurable (s.X n) := fun n => hs.measurable (Sum.inr (Sum.inl n))
  have hkB : ∀ t : ℝ, Measurable ((Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞)) := fun t =>
    measurable_const.indicator measurableSet_Ioi
  have hH := hfun_measurable Fon Foff (fun j => P.map (psum (srcZ s) j)) v
  have hk : Measurable (fun p : ℝ × ℝ => kON u p *
      hfun Fon Foff (fun j => P.map (psum (srcZ s) j)) v (p.1 + p.2)) :=
    (kON_measurable u).mul (hH.comp (measurable_fst.add measurable_snd))
  have key := source_renewal_X hon0 hoff0 hon hoff hion hioff hs _ hk
  try simp only at key
  rw [← key]
  refine tsum_congr fun n => ?_
  have h1 : ∀ ω, kON u (s.Tn n ω, s.X n ω) *
        ((Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
          ∑' j, kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω)) =
      kON u (s.Tn n ω, s.X n ω) * (Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
        ∑' j, kON u (s.Tn n ω, s.X n ω) * kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω) :=
    fun ω => by rw [mul_add, ENNReal.tsum_mul_left]
  have hm1 : Measurable (fun ω => kON u (s.Tn n ω, s.X n ω) *
      (Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω)) :=
    ((kON_measurable u).comp ((Tn_measurable hs n).prodMk (hX n))).mul
      ((hkB v).comp ((Tn_measurable hs n).add (hX n)))
  have hm2 : ∀ j, Measurable (fun ω => kON u (s.Tn n ω, s.X n ω) *
      kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω)) := fun j =>
    ((kON_measurable u).comp ((Tn_measurable hs n).prodMk (hX n))).mul
      ((kON_measurable v).comp ((Tn_measurable hs (n + 1 + j)).prodMk (hX (n + 1 + j))))
  rw [lintegral_congr h1, lintegral_add_left hm1, lintegral_tsum (fun j => (hm2 j).aemeasurable),
    future_sum hs n (kON u) (kON_measurable u) v, ← lintegral_add_left hm1]
  refine lintegral_congr fun ω => ?_
  rw [hfun, mul_add]

theorem ind_Ioi_measurable :
    Measurable fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (1 : ℝ → ℝ≥0∞) p.2 := by
  have : (fun p : ℝ × ℝ => (Set.Ioi p.1).indicator (1 : ℝ → ℝ≥0∞) p.2) =
      {p : ℝ × ℝ | p.1 < p.2}.indicator 1 := by
    funext p
    by_cases h : p.1 < p.2
    · rw [Set.indicator_of_mem (show p.2 ∈ Set.Ioi p.1 from h),
        Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < p.2} from h)]
      rfl
    · rw [Set.indicator_of_notMem (show p.2 ∉ Set.Ioi p.1 from h),
        Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < p.2} from h)]
  rw [this]
  exact measurable_const.indicator (measurableSet_lt measurable_fst measurable_snd)

/-- **Endpoint law of the ON-period covering `u`**: the initial ON-period (density `F̄`) and
the renewal ON-periods together give an endpoint `u + z` with density `F̄(z)`. -/
theorem combine_tail (F : Measure ℝ) [IsProbabilityMeasure F] (h : ℝ → ℝ≥0∞) (hh : Measurable h)
    {u : ℝ} (hu : 0 ≤ u) :
    (∫⁻ y in Set.Ioi u, ENNReal.ofReal (Fbar F y) * h y) +
        ∫⁻ r in Set.Ioi 0, ∫⁻ x, kON u (r, x) * h (r + x) ∂F =
      ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (Fbar F z) * h (z + u) := by
  have hI1 : ∀ y : ℝ, Measurable ((Set.Ioi y).indicator (1 : ℝ → ℝ≥0∞)) := fun y =>
    measurable_const.indicator measurableSet_Ioi
  have hA : ∫⁻ y in Set.Ioi u, ENNReal.ofReal (Fbar F y) * h y =
      ∫⁻ x, (∫⁻ y in Set.Ioo u x, h y) ∂F := by
    have e1 : ∀ y, ENNReal.ofReal (Fbar F y) * h y =
        ∫⁻ x, (Set.Ioi y).indicator 1 x * h y ∂F := by
      intro y
      rw [ofReal_Fbar, lintegral_mul_const _ (hI1 y), lintegral_indicator_one measurableSet_Ioi]
    simp_rw [e1]
    rw [lintegral_lintegral_swap (f := fun y x => (Set.Ioi y).indicator 1 x * h y)
      ((ind_Ioi_measurable.mul (hh.comp measurable_fst)).aemeasurable)]
    congr 1
    funext x
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun y => ?_
    by_cases h1 : u < y <;> by_cases h2 : y < x <;> simp [Set.indicator_apply, h1, h2]
  have hB : ∫⁻ r in Set.Ioi 0, ∫⁻ x, kON u (r, x) * h (r + x) ∂F =
      ∫⁻ x, (∫⁻ y in Set.Ioc (max x u) (x + u), h y) ∂F := by
    rw [lintegral_lintegral_swap (f := fun r x => kON u (r, x) * h (r + x))
      ((kON_measurable u).mul (hh.comp (measurable_fst.add measurable_snd))).aemeasurable]
    congr 1
    funext x
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc,
      ← lintegral_add_right_eq_self (μ := volume) ((Set.Ioc (max x u) (x + u)).indicator h) x]
    refine lintegral_congr fun r => ?_
    have e : r + x ≤ x + u ↔ r ≤ u := by constructor <;> intro <;> linarith
    by_cases h1 : 0 < r <;> by_cases h2 : r ≤ u <;> by_cases h3 : u < r + x <;>
      simp [Set.indicator_apply, kON, h1, h2, h3, e]
  have hC : ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (Fbar F z) * h (z + u) =
      ∫⁻ x, (∫⁻ y in Set.Ioo u (x + u), h y) ∂F := by
    have e1 : ∀ z, ENNReal.ofReal (Fbar F z) * h (z + u) =
        ∫⁻ x, (Set.Ioi z).indicator 1 x * h (z + u) ∂F := by
      intro z
      rw [ofReal_Fbar, lintegral_mul_const _ (hI1 z), lintegral_indicator_one measurableSet_Ioi]
    simp_rw [e1]
    rw [lintegral_lintegral_swap (f := fun z x => (Set.Ioi z).indicator 1 x * h (z + u))
      ((ind_Ioi_measurable.mul (hh.comp (measurable_fst.add_const u))).aemeasurable)]
    congr 1
    funext x
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo,
      ← lintegral_add_right_eq_self (μ := volume) ((Set.Ioo u (x + u)).indicator h) u]
    refine lintegral_congr fun z => ?_
    by_cases h1 : 0 < z <;> by_cases h2 : z < x <;> simp [Set.indicator_apply, h1, h2]
  have hmono : Monotone fun x => ∫⁻ y in Set.Ioo u x, h y :=
    fun a b hab => lintegral_mono_set (Set.Ioo_subset_Ioo_right hab)
  rw [hA, hB, hC, ← lintegral_add_left (f := fun x => ∫⁻ y in Set.Ioo u x, h y) hmono.measurable]
  refine lintegral_congr fun x => ?_
  rcases le_or_gt x u with hx | hx
  · rw [Set.Ioo_eq_empty (not_lt.2 hx), Measure.restrict_empty, lintegral_zero_measure, zero_add,
      max_eq_right hx, setLIntegral_congr Ioo_ae_eq_Ioc]
  · rw [max_eq_left hx.le, setLIntegral_congr Ioo_ae_eq_Ioc, setLIntegral_congr Ioo_ae_eq_Ioc,
      ← lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
      Set.Ioc_union_Ioc_eq_Ioc hx.le (by linarith)]

/-- **Second moment**: `∫⁻ W_u W_v = μ⁻¹ K(v - u)` for `0 ≤ u ≤ v`. -/
theorem lintegral_gW_mul [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫⁻ ω, gW s u ω * gW s v ω ∂P =
      ENNReal.ofReal (mu Fon Foff)⁻¹ *
        Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - u) := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hYoff : Measurable s.Yoff := hs.measurable (Sum.inl 3)
  have hX : ∀ n, Measurable (s.X n) := fun n => hs.measurable (Sum.inr (Sum.inl n))
  have hkB : ∀ t : ℝ, Measurable ((Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞)) := fun t =>
    measurable_const.indicator measurableSet_Ioi
  have hmB : Measurable (fun ω => ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          ((Set.Ioi v).indicator 1 (s.X0 ω) +
            ∑' m, kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω))) :=
    ((ENNReal.measurable_ofReal.comp hB).mul ((hkB u).comp hX0)).mul (((hkB v).comp hX0).add
      (Measurable.ennreal_tsum fun m => (kON_measurable v).comp
        (((hX0.add hYoff).add (psum_measurable (srcZ_measurable hs) m)).prodMk (hX m))))
  have hmn : ∀ n, Measurable (fun ω => kON u (s.Tn n ω, s.X n ω) *
          ((Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
            ∑' j, kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω))) := fun n =>
    ((kON_measurable u).comp ((Tn_measurable hs n).prodMk (hX n))).mul
      (((hkB v).comp ((Tn_measurable hs n).add (hX n))).add (Measurable.ennreal_tsum fun j =>
        (kON_measurable v).comp ((Tn_measurable hs (n + 1 + j)).prodMk (hX (n + 1 + j)))))
  have hcongr : ∀ᵐ ω ∂P, gW s u ω * gW s v ω =
      ENNReal.ofReal (s.B ω) * (Set.Ioi u).indicator 1 (s.X0 ω) *
          ((Set.Ioi v).indicator 1 (s.X0 ω) +
            ∑' m, kON v (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω)) +
        ∑' n, kON u (s.Tn n ω, s.X n ω) *
          ((Set.Ioi v).indicator 1 (s.Tn n ω + s.X n ω) +
            ∑' j, kON v (s.Tn (n + 1 + j) ω, s.X (n + 1 + j) ω)) := by
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    exact gW_mul hω huv
  rw [lintegral_congr_ae hcongr, lintegral_add_left hmB,
    lintegral_tsum (fun n => (hmn n).aemeasurable),
    lintegral_A_B hon hoff hs hu v, lintegral_A_n hon0 hoff0 hon hoff hion hioff hs u v, ← mul_add,
    combine_tail Fon _ (hfun_measurable Fon Foff _ v) hu, Kfun]
  congr 1
  refine lintegral_congr fun z => ?_
  congr 1
  rw [hfun, hfun]
  congr 1
  · by_cases hz : v < z + u
    · rw [Set.indicator_of_mem (show z + u ∈ Set.Ioi v from hz),
        Set.indicator_of_mem (show z ∈ Set.Ioi (v - u) from by
          simp only [Set.mem_Ioi]; linarith)]
      rfl
    · rw [Set.indicator_of_notMem (show z + u ∉ Set.Ioi v from hz),
        Set.indicator_of_notMem (show z ∉ Set.Ioi (v - u) from fun h2 => hz (by
          simp only [Set.mem_Ioi] at h2; linarith))]
  · congr 1
    ring

/-- **`E[W_u W_v] = μ⁻¹ K(v - u)`** for `0 ≤ u ≤ v`: the second moment depends only on `v - u`. -/
theorem second_moment_W [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫ ω, s.W u ω * s.W v ω ∂P = (ENNReal.ofReal (mu Fon Foff)⁻¹ *
      Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - u)).toReal := by
  have hv : 0 ≤ v := hu.trans huv
  have hae : ∀ᵐ ω ∂P, s.W u ω * s.W v ω = (gW s u ω).toReal * (gW s v ω).toReal ∧
      ENNReal.ofReal (s.W u ω * s.W v ω) = gW s u ω * gW s v ω ∧
      0 ≤ s.W u ω * s.W v ω := by
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    obtain ⟨h1, h1'⟩ := ofReal_W hω hu
    obtain ⟨h2, h2'⟩ := ofReal_W hω hv
    refine ⟨?_, ?_, mul_nonneg h1' h2'⟩
    · rw [← h1, ← h2, ENNReal.toReal_ofReal h1', ENNReal.toReal_ofReal h2']
    · rw [ENNReal.ofReal_mul h1', h1, h2]
  have hm : AEStronglyMeasurable (fun ω => s.W u ω * s.W v ω) P :=
    (((gW_measurable hs u).ennreal_toReal.mul
      (gW_measurable hs v).ennreal_toReal).aestronglyMeasurable).congr
      (by filter_upwards [hae] with ω hω; exact hω.1.symm)
  rw [integral_eq_lintegral_of_nonneg_ae (by filter_upwards [hae] with ω hω; exact hω.2.2) hm,
    lintegral_congr_ae (by filter_upwards [hae] with ω hω; exact hω.2.1),
    lintegral_gW_mul hon0 hoff0 hon hoff hion hioff hs hu huv]

end Cov2

end NetTraffic.OnOffFBM.Lib

/-! ### C2a step 6: stationary increments `Var(G_c - G_a) = Var(G_{c-a})`

`Var(G_c - G_a) = ∫_a^c ∫_a^c γ(v - u) dv du` with `γ(d) = μ⁻¹ K(|d|) - (μ_on/μ)²`, and the double
integral is translation invariant. -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section Cov3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem gW_le_one {s : Source Ω} {ω : Ω} (hω : Good s ω) (t : ℝ) : gW s t ω ≤ 1 := by
  by_cases ha : ENNReal.ofReal (s.B ω) * (Set.Ioi t).indicator 1 (s.X0 ω) = 0
  · rw [gW, ha, zero_add]; exact tsum_kON_le_one hω t
  · have hz : ∀ n, kON t (s.Tn n ω, s.X n ω) = 0 := fun n =>
      (mul_eq_zero.1 (B_kON_zero hω (le_refl t) n)).resolve_right ha
    rw [gW, ENNReal.tsum_eq_zero.2 hz, add_zero]
    have h1 : ENNReal.ofReal (s.B ω) ≤ 1 := by rcases hω.1 with h | h <;> simp [h]
    have h2 : (Set.Ioi t).indicator (1 : ℝ → ℝ≥0∞) (s.X0 ω) ≤ 1 :=
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)
    calc _ ≤ 1 * 1 := mul_le_mul' h1 h2
      _ = 1 := one_mul 1

/-- A bounded, jointly measurable version of `W` (equal to `W_t` for `t ≥ 0` a.s.). -/
noncomputable def What (s : Source Ω) (t : ℝ) (ω : Ω) : ℝ := (min (gW s t ω) 1).toReal

theorem What_nonneg (s : Source Ω) (t : ℝ) (ω : Ω) : 0 ≤ What s t ω := ENNReal.toReal_nonneg

theorem What_le_one (s : Source Ω) (t : ℝ) (ω : Ω) : What s t ω ≤ 1 := by
  unfold What
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact min_le_right _ _)

theorem W_eq_What {s : Source Ω} {ω : Ω} (hω : Good s ω) {t : ℝ} (ht : 0 ≤ t) :
    s.W t ω = What s t ω := by
  obtain ⟨h1, h2⟩ := ofReal_W hω ht
  rw [What, min_eq_left (gW_le_one hω t), ← h1, ENNReal.toReal_ofReal h2]

theorem kON_measurable2 : Measurable fun q : ℝ × ℝ × ℝ => kON q.1 q.2 := by
  have : (fun q : ℝ × ℝ × ℝ => kON q.1 q.2) =
      {q : ℝ × ℝ × ℝ | q.2.1 ≤ q.1 ∧ q.1 < q.2.1 + q.2.2}.indicator 1 := by
    funext q
    simp only [kON, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [this]
  exact measurable_const.indicator ((measurableSet_le (measurable_fst.comp measurable_snd)
    measurable_fst).inter (measurableSet_lt measurable_fst
      ((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd))))

theorem gW_measurable2 {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Measurable (fun p : ℝ × Ω => gW s p.1 p.2) := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  show Measurable fun p : ℝ × Ω => ENNReal.ofReal (s.B p.2) * (Set.Ioi p.1).indicator 1 (s.X0 p.2) +
    ∑' n, kON p.1 (s.Tn n p.2, s.X n p.2)
  exact ((ENNReal.measurable_ofReal.comp (hB.comp measurable_snd)).mul
      (ind_Ioi_measurable.comp (measurable_fst.prodMk (hX0.comp measurable_snd)))).add
    (Measurable.ennreal_tsum fun n => kON_measurable2.comp (measurable_fst.prodMk
      (((Tn_measurable hs n).comp measurable_snd).prodMk
        ((hs.measurable (Sum.inr (Sum.inl n))).comp measurable_snd))))

theorem What_measurable2 {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Measurable (fun p : ℝ × Ω => What s p.1 p.2) :=
  ((gW_measurable2 hs).min measurable_const).ennreal_toReal

theorem What_measurable {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (t : ℝ) : Measurable (What s t) :=
  ((gW_measurable hs t).min measurable_const).ennreal_toReal

theorem What_integrable [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (t : ℝ) : Integrable (What s t) P :=
  Integrable.of_bound (What_measurable hs t).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (What_nonneg s t ω)]; exact What_le_one s t ω)

theorem mean_What [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, What s t ω ∂P = mean Fon / mu Fon Foff := by
  rw [← mean_W hon0 hoff0 hon hoff hion hioff hs ht]
  refine integral_congr_ae ?_
  filter_upwards [good_ae hs hon0 hoff0] with ω hω
  exact (W_eq_What hω ht).symm

theorem moment2_What [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, What s u ω * What s v ω ∂P = (ENNReal.ofReal (mu Fon Foff)⁻¹ *
      Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal := by
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonneg (sub_nonneg.2 huv),
      ← second_moment_W hon0 hoff0 hon hoff hion hioff hs hu huv]
    refine integral_congr_ae ?_
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    rw [W_eq_What hω hu, W_eq_What hω hv]
  · rw [abs_of_nonpos (sub_nonpos.2 hvu), neg_sub,
      ← second_moment_W hon0 hoff0 hon hoff hion hioff hs hv hvu]
    refine integral_congr_ae ?_
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    rw [W_eq_What hω hu, W_eq_What hω hv, mul_comm]

/-- The covariance function of the stationary ON/OFF process: `γ(d) = μ⁻¹ K(|d|) - (μ_on/μ)²`. -/
noncomputable def gamS (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (d : ℝ) : ℝ :=
  (ENNReal.ofReal (mu Fon Foff)⁻¹ * Kfun Fon Foff ν |d|).toReal - (mean Fon / mu Fon Foff) ^ 2

theorem moment_Y [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∫ ω, (What s u ω - mean Fon / mu Fon Foff) * (What s v ω - mean Fon / mu Fon Foff) ∂P =
      gamS Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - u) := by
  have hII : Integrable (fun ω => What s u ω * What s v ω) P :=
    Integrable.of_bound ((What_measurable hs u).mul (What_measurable hs v)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (What_nonneg s u ω) (What_nonneg s v ω))]
        exact mul_le_one₀ (What_le_one s u ω) (What_nonneg s v ω) (What_le_one s v ω))
  have e : (fun ω => (What s u ω - mean Fon / mu Fon Foff) * (What s v ω - mean Fon / mu Fon Foff)) =
      fun ω => What s u ω * What s v ω - (mean Fon / mu Fon Foff) * What s v ω -
        (mean Fon / mu Fon Foff) * What s u ω + (mean Fon / mu Fon Foff) ^ 2 := by
    funext ω; ring
  have i1 : Integrable (fun ω => What s u ω * What s v ω - (mean Fon / mu Fon Foff) * What s v ω) P :=
    hII.sub ((What_integrable hs v).const_mul _)
  have i2 : Integrable (fun ω => What s u ω * What s v ω - (mean Fon / mu Fon Foff) * What s v ω -
      (mean Fon / mu Fon Foff) * What s u ω) P :=
    i1.sub ((What_integrable hs u).const_mul _)
  have i3 : Integrable (fun ω => (mean Fon / mu Fon Foff) * What s u ω) P :=
    (What_integrable hs u).const_mul _
  have i4 : Integrable (fun ω => (mean Fon / mu Fon Foff) * What s v ω) P :=
    (What_integrable hs v).const_mul _
  rw [e, integral_add i2 (integrable_const _), integral_sub i1 i3, integral_sub hII i4,
    integral_const_mul, integral_const_mul,
    mean_What hon0 hoff0 hon hoff hion hioff hs hu, mean_What hon0 hoff0 hon hoff hion hioff hs hv,
    moment2_What hon0 hoff0 hon hoff hion hioff hs hu hv, integral_const]
  simp only [gamS, probReal_univ, one_smul]
  ring

/-- Variance of `∫_a^c Y_u du` for a bounded, jointly measurable, centred process `Y`. -/
theorem var_intervalIntegral [IsProbabilityMeasure P] (Y : ℝ → Ω → ℝ)
    (hY : Measurable (fun p : ℝ × Ω => Y p.1 p.2)) (hb : ∀ u ω, |Y u ω| ≤ 1) {a c : ℝ}
    (hac : a ≤ c) (h0 : ∀ u, a < u → ∫ ω, Y u ω ∂P = 0) (Γ : ℝ → ℝ → ℝ)
    (hΓ : ∀ u v, a < u → a < v → ∫ ω, Y u ω * Y v ω ∂P = Γ u v) :
    Var[fun ω => ∫ u in a..c, Y u ω; P] = ∫ u in a..c, ∫ v in a..c, Γ u v := by
  simp only [intervalIntegral.integral_of_le hac]
  set μ : Measure ℝ := volume.restrict (Set.Ioc a c) with hμ
  have hYs : Measurable (fun p : Ω × ℝ => Y p.2 p.1) := hY.comp measurable_swap
  have hYint : Integrable (fun p : Ω × ℝ => Y p.2 p.1) (P.prod μ) :=
    Integrable.of_bound hYs.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hb _ _)
  have hXm : StronglyMeasurable (fun ω => ∫ u, Y u ω ∂μ) :=
    hYs.stronglyMeasurable.integral_prod_right'
  have hmean : ∫ ω, (∫ u, Y u ω ∂μ) ∂P = 0 := by
    rw [integral_integral_swap (f := fun ω u => Y u ω) hYint]
    have : ∀ᵐ u ∂μ, ∫ ω, Y u ω ∂P = 0 := by
      rw [hμ]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact h0 u hu.1
    rw [integral_congr_ae this, integral_zero]
  rw [variance_of_integral_eq_zero hXm.measurable.aemeasurable hmean]
  have hsq : ∀ ω, (∫ u, Y u ω ∂μ) ^ 2 = ∫ p, Y p.1 ω * Y p.2 ω ∂(μ.prod μ) := by
    intro ω
    rw [pow_two, integral_prod_mul (fun u => Y u ω) (fun v => Y v ω)]
  simp_rw [hsq]
  have hYY : Measurable (fun q : Ω × (ℝ × ℝ) => Y q.2.1 q.1 * Y q.2.2 q.1) :=
    (hY.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).mul
      (hY.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
  have hbb : ∀ u v ω, ‖Y u ω * Y v ω‖ ≤ 1 := fun u v ω => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (hb _ _) (abs_nonneg _) (hb _ _)
  have hYYint : Integrable (fun q : Ω × (ℝ × ℝ) => Y q.2.1 q.1 * Y q.2.2 q.1)
      (P.prod (μ.prod μ)) :=
    Integrable.of_bound hYY.aestronglyMeasurable 1 (Eventually.of_forall fun q => hbb _ _ _)
  rw [integral_integral_swap (f := fun ω (p : ℝ × ℝ) => Y p.1 ω * Y p.2 ω) hYYint]
  have hae : ∀ᵐ p ∂(μ.prod μ), ∫ ω, Y p.1 ω * Y p.2 ω ∂P = Γ p.1 p.2 := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact hΓ p.1 p.2 hp.1.1 hp.2.1
  have hGm : StronglyMeasurable (fun p : ℝ × ℝ => ∫ ω, Y p.1 ω * Y p.2 ω ∂P) :=
    (hYY.comp measurable_swap).stronglyMeasurable.integral_prod_right'
  have hGint : Integrable (fun p : ℝ × ℝ => ∫ ω, Y p.1 ω * Y p.2 ω ∂P) (μ.prod μ) :=
    Integrable.of_bound hGm.aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      calc ‖∫ ω, Y p.1 ω * Y p.2 ω ∂P‖ ≤ 1 * P.real Set.univ :=
            norm_integral_le_of_norm_le_const (Eventually.of_forall fun ω => hbb _ _ _)
        _ = 1 := by simp)
  exact (integral_congr_ae hae).trans (integral_prod (fun p : ℝ × ℝ => Γ p.1 p.2) (hGint.congr hae))

theorem double_integral_translate (f : ℝ → ℝ) (a c : ℝ) :
    ∫ u in a..c, ∫ v in a..c, f (v - u) = ∫ u in (0 : ℝ)..(c - a), ∫ v in (0 : ℝ)..(c - a), f (v - u) := by
  calc ∫ u in a..c, ∫ v in a..c, f (v - u)
        = ∫ u in (0 + a)..(c - a + a), ∫ v in a..c, f (v - u) := by rw [zero_add, sub_add_cancel]
    _ = ∫ u in (0 : ℝ)..(c - a), ∫ v in a..c, f (v - (u + a)) :=
        (intervalIntegral.integral_comp_add_right (fun u => ∫ v in a..c, f (v - u)) a).symm
    _ = ∫ u in (0 : ℝ)..(c - a), ∫ v in (0 : ℝ)..(c - a), f (v - u) := by
        congr 1
        funext u
        calc ∫ v in a..c, f (v - (u + a))
              = ∫ v in (0 + a)..(c - a + a), f (v - (u + a)) := by rw [zero_add, sub_add_cancel]
          _ = ∫ v in (0 : ℝ)..(c - a), f ((v + a) - (u + a)) :=
              (intervalIntegral.integral_comp_add_right (fun v => f (v - (u + a))) a).symm
          _ = _ := by
              congr 1
              funext v
              congr 1
              ring

/-- **`Var(G_c - G_a) = ∫_a^c ∫_a^c γ(v - u)`** for `0 ≤ a ≤ c`. -/
theorem var_G_sub [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    Var[fun ω => s.G P c ω - s.G P a ω; P] =
      ∫ u in a..c, ∫ v in a..c, gamS Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - u) := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hm0 : 0 ≤ mean Fon / mu Fon Foff := div_nonneg hon.le hmu.le
  have hm1 : mean Fon / mu Fon Foff ≤ 1 := (div_le_one hmu).2 (by unfold mu; linarith)
  have hYm : Measurable (fun p : ℝ × Ω => What s p.1 p.2 - mean Fon / mu Fon Foff) :=
    (What_measurable2 hs).sub measurable_const
  have hb : ∀ u ω, |What s u ω - mean Fon / mu Fon Foff| ≤ 1 := fun u ω =>
    abs_le.2 ⟨by linarith [What_nonneg s u ω], by linarith [What_le_one s u ω]⟩
  have hGeq : (fun ω => s.G P c ω - s.G P a ω) =ᵐ[P]
      fun ω => ∫ u in a..c, (What s u ω - mean Fon / mu Fon Foff) := by
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    have hG : ∀ T, 0 ≤ T → s.G P T ω = ∫ u in (0 : ℝ)..T, (What s u ω - mean Fon / mu Fon Foff) := by
      intro T hT
      unfold Source.G
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hT] at hu
      rw [W_eq_What hω hu.1, mean_W hon0 hoff0 hon hoff hion hioff hs hu.1]
    have hII : ∀ T, 0 ≤ T → IntervalIntegrable
        (fun u => What s u ω - mean Fon / mu Fon Foff) volume 0 T := by
      intro T hT
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ?_
      exact Integrable.of_bound
        ((hYm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
        (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hb u ω)
    rw [hG c (ha.trans hac), hG a ha,
      intervalIntegral.integral_interval_sub_left (hII c (ha.trans hac)) (hII a ha)]
  rw [variance_congr hGeq]
  refine var_intervalIntegral (fun u ω => What s u ω - mean Fon / mu Fon Foff) hYm hb hac
    (fun u hu => ?_) _ (fun u v hu hv => ?_)
  · rw [integral_sub (What_integrable hs u) (integrable_const _),
      mean_What hon0 hoff0 hon hoff hion hioff hs (ha.trans hu.le), integral_const]
    simp
  · exact moment_Y hon0 hoff0 hon hoff hion hioff hs (ha.trans hu.le) (ha.trans hv.le)

/-- **C2a (stationary increments)**: `Var(G_c - G_a) = Var(G_{c-a})` for `0 ≤ a ≤ c`. -/
theorem stat_increments [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    Var[fun ω => s.G P c ω - s.G P a ω; P] = Var[s.G P (c - a); P] := by
  have h0 : s.G P (c - a) = fun ω => s.G P (c - a) ω - s.G P 0 ω := by
    funext ω; simp [Source.G]
  rw [var_G_sub hon0 hoff0 hon hoff hion hioff hs ha hac, h0,
    var_G_sub hon0 hoff0 hon hoff hion hioff hs le_rfl (sub_nonneg.2 hac)]
  exact double_integral_translate _ a c

end Cov3

end NetTraffic.OnOffFBM.Lib

/-! ### C2b step 1: the covariance through the OFF-started process

`E[B gW_h] = μ⁻¹ K(h)` and `E[(1 - B) gW_h] = (μ_off/μ) R_off(h)`, where `R_off(h)` is the
ON-probability at time `h` of the process started at the beginning of an equilibrium OFF-period.
Hence `μ⁻¹ K(h) + (μ_off/μ) R_off(h) = μ_on/μ`. -/

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM Finset

section Var1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem indep_B_offfuture {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (m : ℕ) :
    IndepFun s.B (fun ω => (s.Y0 ω, psum (srcZ s) m ω, s.X m ω)) P := by
  set T : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := ({Sum.inl 2} ∪ idxZ (range m)) ∪ {Sum.inr (Sum.inl m)}
    with hT
  have hd : Disjoint ({Sum.inl 0} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) T := by
    rw [Finset.disjoint_singleton_left, hT]; simp [idxZ]
  have t2 : Sum.inl 2 ∈ T := by simp [hT]
  have tZ : ∀ i ∈ idxZ (range m), i ∈ T := fun i hi => by
    rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have tX : Sum.inr (Sum.inl m) ∈ T := by rw [hT]; exact Finset.mem_union_right _ (by simp)
  have h := (hs.indep.indepFun_finset _ _ hd hs.measurable).comp
    (φ := fun x : ({Sum.inl 0} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inl 0, Finset.mem_singleton_self _⟩)
    (ψ := fun x : T → ℝ =>
      (x ⟨_, t2⟩, ∑ i ∈ (idxZ (range m)).attach, x ⟨i.1, tZ i.1 i.2⟩, x ⟨_, tX⟩))
    (measurable_pi_apply _ : Measurable fun x : ({Sum.inl 0} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inl 0, Finset.mem_singleton_self _⟩)
    (Measurable.prodMk (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, t2⟩)
      (Measurable.prodMk (Finset.measurable_sum _ fun i _ => measurable_pi_apply _)
        (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, tX⟩)))
  convert h using 1
  · funext ω
    rfl
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (range m)) (fun i => s.family i ω), ← psum_srcZ_eq]
    rfl

theorem indep_Y0_future {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (m : ℕ) : IndepFun s.Y0 (fun ω => (psum (srcZ s) m ω, s.X m ω)) P := by
  set T : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ)) := idxZ (range m) ∪ {Sum.inr (Sum.inl m)} with hT
  have hd : Disjoint ({Sum.inl 2} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) T := by
    rw [Finset.disjoint_singleton_left, hT]; simp [idxZ]
  have tZ : ∀ i ∈ idxZ (range m), i ∈ T := fun i hi => by
    rw [hT]; exact Finset.mem_union_left _ hi
  have tX : Sum.inr (Sum.inl m) ∈ T := by rw [hT]; exact Finset.mem_union_right _ (by simp)
  have h := (hs.indep.indepFun_finset _ _ hd hs.measurable).comp
    (φ := fun x : ({Sum.inl 2} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inl 2, Finset.mem_singleton_self _⟩)
    (ψ := fun x : T → ℝ => (∑ i ∈ (idxZ (range m)).attach, x ⟨i.1, tZ i.1 i.2⟩, x ⟨_, tX⟩))
    (measurable_pi_apply _ : Measurable fun x : ({Sum.inl 2} : Finset (Fin 4 ⊕ (ℕ ⊕ ℕ))) → ℝ =>
      x ⟨Sum.inl 2, Finset.mem_singleton_self _⟩)
    (Measurable.prodMk (Finset.measurable_sum _ fun i _ => measurable_pi_apply _)
      (measurable_pi_apply _ : Measurable fun x : T → ℝ => x ⟨_, tX⟩))
  convert h using 1
  · funext ω
    rfl
  · funext ω
    simp only [Function.comp_apply]
    rw [Finset.sum_attach (idxZ (range m)) (fun i => s.family i ω), ← psum_srcZ_eq]
    rfl

theorem law_off_future [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (m : ℕ) :
    P.map (fun ω => (s.Y0 ω, psum (srcZ s) m ω, s.X m ω)) =
      (eqLaw Foff).prod ((P.map (psum (srcZ s) m)).prod Fon) := by
  have hY : Measurable s.Y0 := hs.measurable (Sum.inl 2)
  have hX : Measurable (s.X m) := hs.measurable (Sum.inr (Sum.inl m))
  have hBm := psum_measurable (srcZ_measurable hs) m
  have hPX : IndepFun (psum (srcZ s) m) (s.X m) P := by
    have h0 := indep_blockSum_X hs 0 m
    rw [zero_add] at h0
    convert h0 using 1
    funext ω
    show ∑ i ∈ range m, srcZ s i ω = ∑ k ∈ Ico 0 (0 + m), srcZ s k ω
    rw [zero_add, Finset.range_eq_Ico]
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable
    (hBm.prodMk hX).aemeasurable).1 (indep_Y0_future hs m)
  have h2 := (indepFun_iff_map_prod_eq_prod_map_map hBm.aemeasurable hX.aemeasurable).1 hPX
  rw [h1, h2, hs.law_Y0, hs.law_X m]

theorem Tn_of_B0 (s : Source Ω) {ω : Ω} (hB : s.B ω = 0) (n : ℕ) :
    s.Tn n ω = s.Y0 ω + psum (srcZ s) n ω := by
  simp only [Source.Tn, Source.T0, psum, srcZ, hB]
  ring

theorem eqLaw_Iic_zero (F : Measure ℝ) : eqLaw F (Set.Iic 0) = 0 := by
  unfold eqLaw
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have : Set.Iic (0 : ℝ) ∩ Set.Ioi 0 = ∅ := Set.ext fun x => by
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    exact id
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

theorem X0_pos_ae {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    ∀ᵐ ω ∂P, 0 < s.X0 ω := by
  have hX0 : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have h : P (s.X0 ⁻¹' Set.Iic 0) = 0 := by
    rw [← Measure.map_apply hX0 measurableSet_Iic, hs.law_X0, eqLaw_Iic_zero]
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  simpa using hω

theorem lintegral_bernoulli_compl (Fon Foff : Measure ℝ) :
    ∫⁻ b, ENNReal.ofReal (1 - b) ∂(bernoulliLaw Fon Foff) =
      ENNReal.ofReal (mean Foff / mu Fon Foff) := by
  simp [bernoulliLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

theorem lintegral_gW [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ ω, gW s h ω ∂P = ENNReal.ofReal (mean Fon / mu Fon Foff) := by
  have e1 : (fun ω => gW s h ω) =ᵐ[P] fun ω => ENNReal.ofReal (What s h ω) := by
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    rw [← W_eq_What hω hh, (ofReal_W hω hh).1]
  rw [lintegral_congr_ae e1, ← ofReal_integral_eq_lintegral_ofReal (What_integrable hs h)
    (Eventually.of_forall fun ω => What_nonneg s h ω),
    mean_What hon0 hoff0 hon hoff hion hioff hs hh]

theorem lintegral_B_gW [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (h : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (s.B ω) * gW s h ω ∂P =
      ENNReal.ofReal (mu Fon Foff)⁻¹ * Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) h := by
  have e : (fun ω => ENNReal.ofReal (s.B ω) * gW s h ω) =ᵐ[P] fun ω =>
      ENNReal.ofReal (s.B ω) * (Set.Ioi 0).indicator 1 (s.X0 ω) *
        ((Set.Ioi h).indicator 1 (s.X0 ω) +
          ∑' m, kON h (s.X0 ω + s.Yoff ω + psum (srcZ s) m ω, s.X m ω)) := by
    filter_upwards [good_ae hs hon0 hoff0, X0_pos_ae hs] with ω hω hx
    rcases hω.1 with hB | hB
    · simp [hB]
    · simp only [gW, hB, ENNReal.ofReal_one, one_mul,
        Set.indicator_of_mem (show s.X0 ω ∈ Set.Ioi 0 from hx), Pi.one_apply, Tn_of_B1 s hB]
  rw [lintegral_congr_ae e, lintegral_A_B hon hoff hs le_rfl h]
  rfl

/-- ON-probability at time `t` of the process started at the beginning of an equilibrium
OFF-period: `R_off(t) = Σ_m P(Y⁰ + S_m ≤ t < Y⁰ + S_m + X_m)`. -/
noncomputable def Roff (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∑' m, ∫⁻ p, kON t (p.1 + p.2.1, p.2.2) ∂((eqLaw Foff).prod ((ν m).prod Fon))

theorem lintegral_offB_gW [IsProbabilityMeasure P] {Fon Foff : Measure ℝ}
    [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (h : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (1 - s.B ω) * gW s h ω ∂P =
      ENNReal.ofReal (mean Foff / mu Fon Foff) *
        Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) h := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  have hY0 : Measurable s.Y0 := hs.measurable (Sum.inl 2)
  have hX : ∀ n, Measurable (s.X n) := fun n => hs.measurable (Sum.inr (Sum.inl n))
  have hk : Measurable (fun p : ℝ × ℝ × ℝ => kON h (p.1 + p.2.1, p.2.2)) :=
    (kON_measurable h).comp ((measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have e : (fun ω => ENNReal.ofReal (1 - s.B ω) * gW s h ω) =ᵐ[P] fun ω =>
      ∑' m, ENNReal.ofReal (1 - s.B ω) *
        kON h (s.Y0 ω + psum (srcZ s) m ω, s.X m ω) := by
    filter_upwards [good_ae hs hon0 hoff0] with ω hω
    rcases hω.1 with hB0 | hB0
    · simp only [gW, hB0, sub_zero, ENNReal.ofReal_one, ENNReal.ofReal_zero, zero_mul, zero_add,
        one_mul, Tn_of_B0 s hB0]
    · simp [hB0]
  have hV : ∀ m, Measurable (fun ω => (s.Y0 ω, psum (srcZ s) m ω, s.X m ω)) := fun m =>
    hY0.prodMk ((psum_measurable (srcZ_measurable hs) m).prodMk (hX m))
  have hF : Measurable (fun q : ℝ × (ℝ × ℝ × ℝ) =>
      ENNReal.ofReal (1 - q.1) * kON h (q.2.1 + q.2.2.1, q.2.2.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_fst)).mul
      (hk.comp measurable_snd)
  have hterm : ∀ m, ∫⁻ ω, ENNReal.ofReal (1 - s.B ω) *
      kON h (s.Y0 ω + psum (srcZ s) m ω, s.X m ω) ∂P =
      ENNReal.ofReal (mean Foff / mu Fon Foff) *
        ∫⁻ p, kON h (p.1 + p.2.1, p.2.2) ∂((eqLaw Foff).prod
          ((P.map (psum (srcZ s) m)).prod Fon)) := by
    intro m
    have := lintegral_indep_gen hB (hV m) (indep_B_offfuture hs m) hF
    simp only at this
    rw [this, law_off_future hs m, hs.law_B]
    simp_rw [lintegral_const_mul _ hk]
    rw [lintegral_mul_const (f := fun u : ℝ => ENNReal.ofReal (1 - u)) _
      (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)),
      lintegral_bernoulli_compl]
  have hm : ∀ m, Measurable (fun ω => ENNReal.ofReal (1 - s.B ω) *
      kON h (s.Y0 ω + psum (srcZ s) m ω, s.X m ω)) := fun m =>
    (ENNReal.measurable_ofReal.comp (measurable_const.sub hB)).mul (hk.comp (hV m))
  rw [lintegral_congr_ae e, lintegral_tsum (fun m => (hm m).aemeasurable)]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left]
  rfl

/-- **`μ⁻¹ K(h) + (μ_off/μ) R_off(h) = μ_on/μ`** for `h ≥ 0`. -/
theorem K_add_Roff [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (mu Fon Foff)⁻¹ * Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) h +
      ENNReal.ofReal (mean Foff / mu Fon Foff) *
        Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) h =
      ENNReal.ofReal (mean Fon / mu Fon Foff) := by
  have hB : Measurable s.B := hs.measurable (Sum.inl 0)
  rw [← lintegral_B_gW hon0 hoff0 hon hoff hs h, ← lintegral_offB_gW hon0 hoff0 hs h,
    ← lintegral_add_left (f := fun ω => ENNReal.ofReal (s.B ω) * gW s h ω)
      ((ENNReal.measurable_ofReal.comp hB).mul (gW_measurable hs h)),
    ← lintegral_gW hon0 hoff0 hon hoff hion hioff hs hh]
  refine lintegral_congr_ae ?_
  filter_upwards [good_ae hs hon0 hoff0] with ω hω
  rcases hω.1 with hB0 | hB0 <;> simp [hB0]

end Var1

section Var2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem Roff_measurable (Fon Foff : Measure ℝ) [SFinite Fon] (ν : ℕ → Measure ℝ)
    [∀ j, SFinite (ν j)] : Measurable (Roff Fon Foff ν) := by
  have : SFinite (eqLaw Foff) := by unfold eqLaw; infer_instance
  have hk : Measurable (fun q : ℝ × (ℝ × ℝ × ℝ) => kON q.1 (q.2.1 + q.2.2.1, q.2.2.2)) :=
    kON_measurable2.comp (measurable_fst.prodMk
      (((measurable_fst.comp measurable_snd).add
        (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  show Measurable fun t => ∑' m, ∫⁻ p, kON t (p.1 + p.2.1, p.2.2) ∂((eqLaw Foff).prod
    ((ν m).prod Fon))
  exact Measurable.ennreal_tsum fun m => hk.lintegral_prod_right'

theorem Roff_le [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {h : ℝ} (hh : 0 ≤ h) :
    Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) h ≤
      ENNReal.ofReal ((mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff)) := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hq : 0 < mean Foff / mu Fon Foff := div_pos hoff hmu
  have h1 := le_of_le_of_eq le_add_self (K_add_Roff hon0 hoff0 hon hoff hion hioff hs hh)
  rw [ENNReal.ofReal_div_of_pos hq, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.2 hq).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h1

/-- `γ(d) = (μ_on/μ)(μ_off/μ) - (μ_off/μ) R_off(|d|)`. -/
theorem gamS_eq [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (d : ℝ) :
    gamS Fon Foff (fun j => P.map (psum (srcZ s) j)) d =
      (mean Fon / mu Fon Foff) * (mean Foff / mu Fon Foff) -
        (mean Foff / mu Fon Foff) *
          (Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |d|).toReal := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hK := K_add_Roff hon0 hoff0 hon hoff hion hioff hs (abs_nonneg d)
  have hRt : Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |d| ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (Roff_le hon0 hoff0 hon hoff hion hioff hs (abs_nonneg d))
  have hA : ENNReal.ofReal (mu Fon Foff)⁻¹ *
      Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) |d| ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_of_le_of_eq le_self_add hK)
  have hB : ENNReal.ofReal (mean Foff / mu Fon Foff) *
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |d| ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hRt
  have h2 := congrArg ENNReal.toReal hK
  rw [ENNReal.toReal_add hA hB, ENNReal.toReal_mul (a := ENNReal.ofReal (mean Foff / mu Fon Foff)),
    ENNReal.toReal_ofReal (div_nonneg hoff.le hmu.le),
    ENNReal.toReal_ofReal (div_nonneg hon.le hmu.le)] at h2
  have hpq : mean Foff / mu Fon Foff = 1 - mean Fon / mu Fon Foff := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hmu.ne']
    unfold mu; ring
  unfold gamS
  rw [show (ENNReal.ofReal (mu Fon Foff)⁻¹ *
      Kfun Fon Foff (fun j => P.map (psum (srcZ s) j)) |d|).toReal =
      mean Fon / mu Fon Foff - mean Foff / mu Fon Foff *
        (Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |d|).toReal by linarith]
  rw [hpq]; ring

theorem lintegral_Ioc_reflect (g : ℝ → ℝ≥0∞) (u : ℝ) :
    ∫⁻ v in Set.Ioc 0 u, g (u - v) = ∫⁻ h in Set.Ico 0 u, g h := by
  rw [← lintegral_reflect g u, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Set.inter_comm, Set.Ioi_inter_Iic]

theorem lintegral_Ioc_translate (g : ℝ → ℝ≥0∞) (u T : ℝ) :
    ∫⁻ v in Set.Ioc u T, g (v - u) = ∫⁻ h in Set.Ioc 0 (T - u), g h := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  refine Eq.trans ?_ (lintegral_add_right_eq_self _ (-u))
  refine lintegral_congr fun v => ?_
  show (Set.Ioc u T).indicator (fun v => g (v - u)) v = (Set.Ioc 0 (T - u)).indicator g (v + -u)
  have hiff : v ∈ Set.Ioc u T ↔ v + -u ∈ Set.Ioc 0 (T - u) := by
    simp only [Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hv : v ∈ Set.Ioc u T
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hiff.1 hv), ← sub_eq_add_neg]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv (hiff.2 h))]

theorem lintegral_Ioc_tri1 (g : ℝ → ℝ≥0∞) (hg : Measurable g) (T : ℝ) :
    ∫⁻ u in Set.Ioc 0 T, ∫⁻ h in Set.Ico 0 u, g h =
      ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * g h := by
  set S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ T ∧ 0 ≤ p.2 ∧ p.2 < p.1} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_fst)))
  have hF : Measurable (S.indicator (fun p : ℝ × ℝ => g p.2)) :=
    (hg.comp measurable_snd).indicator hS
  have h1 : ∀ u, (Set.Ioc 0 T).indicator (fun u => ∫⁻ h in Set.Ico 0 u, g h) u =
      ∫⁻ h, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) := by
    intro u
    by_cases hu : u ∈ Set.Ioc 0 T
    · rw [Set.indicator_of_mem hu, ← lintegral_indicator measurableSet_Ico]
      refine lintegral_congr fun h => ?_
      by_cases hh : h ∈ Set.Ico 0 u
      · rw [Set.indicator_of_mem hh,
          Set.indicator_of_mem (show (u, h) ∈ S from ⟨hu.1, hu.2, hh.1, hh.2⟩)]
      · rw [Set.indicator_of_notMem hh,
          Set.indicator_of_notMem (fun hm : (u, h) ∈ S => hh ⟨hm.2.2.1, hm.2.2.2⟩)]
    · rw [Set.indicator_of_notMem hu]
      symm
      rw [lintegral_congr fun h =>
        Set.indicator_of_notMem (fun hm : (u, h) ∈ S => hu ⟨hm.1, hm.2.1⟩) _]
      exact lintegral_zero
  have h2 : ∀ h, ∫⁻ u, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) =
      (Set.Ici 0).indicator (fun h => ENNReal.ofReal (T - h) * g h) h := by
    intro h
    by_cases h0 : 0 ≤ h
    · rw [Set.indicator_of_mem (show h ∈ Set.Ici 0 from h0)]
      have : ∀ u, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) =
          (Set.Ioc h T).indicator (fun _ => g h) u := by
        intro u
        by_cases hu : u ∈ Set.Ioc h T
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
            (show (u, h) ∈ S from ⟨by linarith [hu.1], hu.2, h0, hu.1⟩)]
        · rw [Set.indicator_of_notMem hu,
            Set.indicator_of_notMem (fun hm : (u, h) ∈ S => hu ⟨hm.2.2.2, hm.2.1⟩)]
      rw [lintegral_congr this, lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc,
        mul_comm]
    · rw [Set.indicator_of_notMem (show h ∉ Set.Ici 0 from h0)]
      rw [lintegral_congr fun u =>
        Set.indicator_of_notMem (fun hm : (u, h) ∈ S => h0 hm.2.2.1) _]
      exact lintegral_zero
  calc ∫⁻ u in Set.Ioc 0 T, ∫⁻ h in Set.Ico 0 u, g h
      = ∫⁻ u, ∫⁻ h, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) := by
        rw [← lintegral_indicator measurableSet_Ioc]; exact lintegral_congr h1
    _ = ∫⁻ h, ∫⁻ u, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ h, (Set.Ici 0).indicator (fun h => ENNReal.ofReal (T - h) * g h) h :=
        lintegral_congr h2
    _ = ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * g h := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_congr_set Ioi_ae_eq_Ici.symm]

theorem lintegral_Ioc_tri2 (g : ℝ → ℝ≥0∞) (hg : Measurable g) (T : ℝ) :
    ∫⁻ u in Set.Ioc 0 T, ∫⁻ h in Set.Ioc 0 (T - u), g h =
      ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * g h := by
  set S : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ T ∧ 0 < p.2 ∧ p.2 ≤ T - p.1} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_fst measurable_const).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))))
  have hF : Measurable (S.indicator (fun p : ℝ × ℝ => g p.2)) :=
    (hg.comp measurable_snd).indicator hS
  have h1 : ∀ u, (Set.Ioc 0 T).indicator (fun u => ∫⁻ h in Set.Ioc 0 (T - u), g h) u =
      ∫⁻ h, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) := by
    intro u
    by_cases hu : u ∈ Set.Ioc 0 T
    · rw [Set.indicator_of_mem hu, ← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun h => ?_
      by_cases hh : h ∈ Set.Ioc 0 (T - u)
      · rw [Set.indicator_of_mem hh,
          Set.indicator_of_mem (show (u, h) ∈ S from ⟨hu.1, hu.2, hh.1, hh.2⟩)]
      · rw [Set.indicator_of_notMem hh,
          Set.indicator_of_notMem (fun hm : (u, h) ∈ S => hh ⟨hm.2.2.1, hm.2.2.2⟩)]
    · rw [Set.indicator_of_notMem hu]
      symm
      rw [lintegral_congr fun h =>
        Set.indicator_of_notMem (fun hm : (u, h) ∈ S => hu ⟨hm.1, hm.2.1⟩) _]
      exact lintegral_zero
  have h2 : ∀ h, ∫⁻ u, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) =
      (Set.Ioi 0).indicator (fun h => ENNReal.ofReal (T - h) * g h) h := by
    intro h
    by_cases h0 : 0 < h
    · rw [Set.indicator_of_mem (show h ∈ Set.Ioi 0 from h0)]
      have : ∀ u, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) =
          (Set.Ioc 0 (T - h)).indicator (fun _ => g h) u := by
        intro u
        by_cases hu : u ∈ Set.Ioc 0 (T - h)
        · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
            (show (u, h) ∈ S from ⟨hu.1, by linarith [hu.2], h0, by linarith [hu.2]⟩)]
        · rw [Set.indicator_of_notMem hu,
            Set.indicator_of_notMem (fun hm : (u, h) ∈ S => hu ⟨hm.1, by linarith [hm.2.2.2]⟩)]
      rw [lintegral_congr this, lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc,
        sub_zero, mul_comm]
    · rw [Set.indicator_of_notMem (show h ∉ Set.Ioi 0 from h0)]
      rw [lintegral_congr fun u =>
        Set.indicator_of_notMem (fun hm : (u, h) ∈ S => h0 hm.2.2.1) _]
      exact lintegral_zero
  calc ∫⁻ u in Set.Ioc 0 T, ∫⁻ h in Set.Ioc 0 (T - u), g h
      = ∫⁻ u, ∫⁻ h, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) := by
        rw [← lintegral_indicator measurableSet_Ioc]; exact lintegral_congr h1
    _ = ∫⁻ h, ∫⁻ u, S.indicator (fun p : ℝ × ℝ => g p.2) (u, h) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ h, (Set.Ioi 0).indicator (fun h => ENNReal.ofReal (T - h) * g h) h :=
        lintegral_congr h2
    _ = ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * g h := by
        rw [lintegral_indicator measurableSet_Ioi]

/-- `∫∫_{(0,T]²} g(|v - u|) = 2 ∫_0^∞ (T - h)₊ g(h) dh`. -/
theorem lintegral_Ioc_abs_sub (g : ℝ → ℝ≥0∞) (hg : Measurable g) (T : ℝ) :
    ∫⁻ u in Set.Ioc 0 T, ∫⁻ v in Set.Ioc 0 T, g |v - u| =
      2 * ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * g h := by
  have hin : ∀ u ∈ Set.Ioc 0 T, ∫⁻ v in Set.Ioc 0 T, g |v - u| =
      (∫⁻ h in Set.Ico 0 u, g h) + ∫⁻ h in Set.Ioc 0 (T - u), g h := by
    intro u hu
    have e1 : ∫⁻ v in Set.Ioc 0 u, g |v - u| = ∫⁻ v in Set.Ioc 0 u, g (u - v) :=
      setLIntegral_congr_fun measurableSet_Ioc (fun v hv => by
        rw [abs_of_nonpos (by linarith [hv.2]), neg_sub])
    have e2 : ∫⁻ v in Set.Ioc u T, g |v - u| = ∫⁻ v in Set.Ioc u T, g (v - u) :=
      setLIntegral_congr_fun measurableSet_Ioc (fun v hv => by
        rw [abs_of_nonneg (by linarith [hv.1])])
    rw [← Set.Ioc_union_Ioc_eq_Ioc hu.1.le hu.2,
      lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl), e1, e2,
      lintegral_Ioc_reflect, lintegral_Ioc_translate]
  have hm1 : Measurable fun u : ℝ => ∫⁻ h in Set.Ico 0 u, g h :=
    Monotone.measurable fun a b hab => lintegral_mono_set (Set.Ico_subset_Ico_right hab)
  rw [setLIntegral_congr_fun measurableSet_Ioc hin, lintegral_add_left hm1,
    lintegral_Ioc_tri1 g hg T, lintegral_Ioc_tri2 g hg T, two_mul]

/-- **`Var G_T = (μ_on/μ)(μ_off/μ) T² - (μ_off/μ) · 2 ∫_0^∞ (T-h)₊ R_off(h) dh`**. -/
theorem var_G_formula [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {T : ℝ} (hT : 0 ≤ T) :
    Var[s.G P T; P] = (mean Fon / mu Fon Foff) * (mean Foff / mu Fon Foff) * T ^ 2 -
      (mean Foff / mu Fon Foff) * (2 * ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) *
        Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) h).toReal := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hq0 : 0 ≤ mean Foff / mu Fon Foff := div_nonneg hoff.le hmu.le
  have hC0 : 0 ≤ (mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff) :=
    div_nonneg (div_nonneg hon.le hmu.le) hq0
  have hRm := Roff_measurable Fon Foff (fun j => P.map (psum (srcZ s) j))
  have hR2 : Measurable (fun p : ℝ × ℝ =>
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |p.2 - p.1|) :=
    hRm.comp ((measurable_snd.sub measurable_fst).abs)
  have hRle : ∀ d : ℝ, Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |d| ≤
      ENNReal.ofReal ((mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff)) :=
    fun d => Roff_le hon0 hoff0 hon hoff hion hioff hs (abs_nonneg d)
  have hRne : ∀ d : ℝ, Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |d| ≠ ∞ :=
    fun d => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hRle d)
  have hRv : ∀ u : ℝ, Measurable (fun v : ℝ =>
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|) := fun u =>
    hRm.comp ((measurable_id.sub measurable_const).abs)
  have hLu : ∀ u : ℝ, ∫⁻ v in Set.Ioc 0 T,
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u| ≤
      ENNReal.ofReal ((mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff)) *
        volume (Set.Ioc (0 : ℝ) T) := fun u =>
    (setLIntegral_mono measurable_const (fun v _ => hRle (v - u))).trans_eq
      (setLIntegral_const _ _)
  have hLm : Measurable (fun u : ℝ => ∫⁻ v in Set.Ioc 0 T,
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|) :=
    hR2.lintegral_prod_right'
  have hLne : ∀ u : ℝ, (∫⁻ v in Set.Ioc 0 T,
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|) ≠ ∞ := fun u =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_Ioc_lt_top.ne) (hLu u)
  have hin : ∀ u : ℝ, ∫ v in (0 : ℝ)..T,
      (Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal =
      (∫⁻ v in Set.Ioc 0 T, Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal := by
    intro u
    rw [intervalIntegral.integral_of_le hT]
    exact integral_toReal (hRv u).aemeasurable (Eventually.of_forall fun v => (hRne (v - u)).lt_top)
  have hout : ∫ u in (0 : ℝ)..T, (∫⁻ v in Set.Ioc 0 T,
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal =
      (∫⁻ u in Set.Ioc 0 T, ∫⁻ v in Set.Ioc 0 T,
        Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_toReal hLm.aemeasurable (Eventually.of_forall fun u => (hLne u).lt_top)
  have hII : ∀ u : ℝ, IntervalIntegrable (fun v : ℝ =>
      (Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal) volume 0 T := by
    intro u
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ?_
    refine Integrable.of_bound (hRv u).ennreal_toReal.aestronglyMeasurable
      ((mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff)) (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal hC0 (hRle (v - u))
  have hIIo : IntervalIntegrable (fun u : ℝ => (∫⁻ v in Set.Ioc 0 T,
      Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal) volume 0 T := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ?_
    refine Integrable.of_bound hLm.ennreal_toReal.aestronglyMeasurable
      ((mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff) * T)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 hT) ((hLu u).trans_eq ?_)
    rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hC0]
  have h0 : s.G P T = fun ω => s.G P T ω - s.G P 0 ω := by
    funext ω; simp [Source.G]
  rw [h0, var_G_sub hon0 hoff0 hon hoff hion hioff hs le_rfl hT]
  simp_rw [gamS_eq hon0 hoff0 hon hoff hion hioff hs]
  calc _ = ∫ u in (0 : ℝ)..T, ((mean Fon / mu Fon Foff) * (mean Foff / mu Fon Foff) * T -
        (mean Foff / mu Fon Foff) * (∫⁻ v in Set.Ioc 0 T,
          Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        rw [intervalIntegral.integral_sub intervalIntegrable_const ((hII u).const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hin u,
          smul_eq_mul, sub_zero]
        ring
    _ = (mean Fon / mu Fon Foff) * (mean Foff / mu Fon Foff) * T * T -
        (mean Foff / mu Fon Foff) * (∫⁻ u in Set.Ioc 0 T, ∫⁻ v in Set.Ioc 0 T,
          Roff Fon Foff (fun j => P.map (psum (srcZ s) j)) |v - u|).toReal := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const (hIIo.const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hout,
          smul_eq_mul, sub_zero]
        ring
    _ = _ := by rw [lintegral_Ioc_abs_sub _ hRm T]; ring

end Var2

section Var3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `ψ_T(c) = ∫_0^∞ (T - c - r)₊ F̄(r) dr`. -/
noncomputable def psiT (F : Measure ℝ) (T c : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (T - c - r) * ENNReal.ofReal (Fbar F r)

theorem psiT_measurable (F : Measure ℝ) [IsFiniteMeasure F] (T : ℝ) : Measurable (psiT F T) := by
  have : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (T - q.1 - q.2) * ENNReal.ofReal (Fbar F q.2) :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_fst).sub measurable_snd)).mul
      ((Fbar_measurable F).comp measurable_snd).ennreal_ofReal
  exact this.lintegral_prod_right'

/-- `A_GF(T) = Σ_m ∫ ψ_T(y + b) d(F_off⁰ ⊗ ν_m)(y, b)`. -/
noncomputable def AGF (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∑' m, ∫⁻ p, psiT Fon T (p.1 + p.2) ∂((eqLaw Foff).prod (ν m))

theorem kernel_psi (F : Measure ℝ) [IsProbabilityMeasure F] (T : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x, (∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * kON h (c, x)) ∂F = psiT F T c := by
  have hk2 : Measurable fun q : ℝ × ℝ × ℝ => kON q.1 q.2 := kON_measurable2
  have hm : Measurable (Function.uncurry fun (x h : ℝ) => ENNReal.ofReal (T - h) * kON h (c, x)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_snd)).mul
      (hk2.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst)))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have e1 : ∀ h : ℝ, ∫⁻ x, ENNReal.ofReal (T - h) * kON h (c, x) ∂F =
      ENNReal.ofReal (T - h) * (Set.Iic h).indicator (fun r => ENNReal.ofReal (Fbar F (h - r))) c :=
    fun h => by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_kON F h c]
  simp_rw [e1]
  have hne : ∀ᵐ h ∂(volume.restrict (Set.Ioi (0 : ℝ))), h ∈ ({c} : Set ℝ)ᶜ :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton c))
  have e2 : (fun h => ENNReal.ofReal (T - h) *
      (Set.Iic h).indicator (fun r => ENNReal.ofReal (Fbar F (h - r))) c) =ᵐ[volume.restrict
        (Set.Ioi (0 : ℝ))] (Set.Ioi c).indicator (fun h =>
          ENNReal.ofReal (T - c - (h - c)) * ENNReal.ofReal (Fbar F (h - c))) := by
    filter_upwards [hne] with h hh
    have hh' : h ≠ c := hh
    by_cases hlt : c < h
    · rw [Set.indicator_of_mem (show c ∈ Set.Iic h from hlt.le),
        Set.indicator_of_mem (show h ∈ Set.Ioi c from hlt)]
      congr 2; ring
    · have hlt2 : h < c := lt_of_le_of_ne (not_lt.1 hlt) hh'
      rw [Set.indicator_of_notMem (show c ∉ Set.Iic h from fun h1 => absurd h1 (not_le.2 hlt2)),
        Set.indicator_of_notMem (show h ∉ Set.Ioi c from hlt), mul_zero]
  rw [lintegral_congr_ae e2, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi, sup_eq_left.2 hc]
  have := setLIntegral_Ioi_add (fun u => ENNReal.ofReal (T - c - (u - c)) *
    ENNReal.ofReal (Fbar F (u - c))) c 0
  simp only [add_zero, add_sub_cancel_left] at this
  rw [this]
  rfl

theorem eqLaw_Iio_zero (F : Measure ℝ) : eqLaw F (Set.Iio 0) = 0 :=
  measure_mono_null Set.Iio_subset_Iic_self (eqLaw_Iic_zero F)

theorem nu_Iio_zero [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (m : ℕ) : P.map (psum (srcZ s) m) (Set.Iio 0) = 0 := by
  rw [Measure.map_apply (psum_measurable (srcZ_measurable hs) m) measurableSet_Iio]
  rw [← compl_mem_ae_iff]
  filter_upwards [good_ae hs hon0 hoff0] with ω hω
  exact not_lt.2 (psum_srcZ_nonneg hω m)

/-- **`∫_0^∞ (T - h)₊ R_off(h) dh = A_GF(T)`**. -/
theorem lintegral_Roff_eq (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)]
    (hν : ∀ j, ν j (Set.Iio 0) = 0) (T : ℝ) :
    ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * Roff Fon Foff ν h = AGF Fon Foff ν T := by
  have : SFinite (eqLaw Foff) := by unfold eqLaw; infer_instance
  have hk2 : Measurable fun q : ℝ × ℝ × ℝ => kON q.1 q.2 := kON_measurable2
  have hk : Measurable (fun q : ℝ × (ℝ × ℝ × ℝ) => kON q.1 (q.2.1 + q.2.2.1, q.2.2.2)) :=
    hk2.comp (measurable_fst.prodMk
      (((measurable_fst.comp measurable_snd).add
        (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  have hTk : Measurable (fun q : ℝ × (ℝ × ℝ × ℝ) =>
      ENNReal.ofReal (T - q.1) * kON q.1 (q.2.1 + q.2.2.1, q.2.2.2)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_fst)).mul hk
  have hI : ∀ m, Measurable fun h : ℝ => ENNReal.ofReal (T - h) *
      ∫⁻ p, kON h (p.1 + p.2.1, p.2.2) ∂((eqLaw Foff).prod ((ν m).prod Fon)) := fun m =>
    (ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)).mul
      hk.lintegral_prod_right'
  unfold Roff AGF
  simp_rw [← ENNReal.tsum_mul_left]
  rw [lintegral_tsum fun m => (hI m).aemeasurable]
  refine tsum_congr fun m => ?_
  have hG0 : ∀ᵐ y ∂(eqLaw Foff), 0 ≤ y := by
    rw [ae_iff]
    exact measure_mono_null (fun a (ha : ¬ 0 ≤ a) => (not_le.1 ha : a < 0)) (eqLaw_Iio_zero Foff)
  have hνm : ∀ᵐ b ∂(ν m), 0 ≤ b := by
    rw [ae_iff]
    exact measure_mono_null (fun a (ha : ¬ 0 ≤ a) => (not_le.1 ha : a < 0)) (hν m)
  calc ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) *
        ∫⁻ p, kON h (p.1 + p.2.1, p.2.2) ∂((eqLaw Foff).prod ((ν m).prod Fon))
      = ∫⁻ h in Set.Ioi 0, ∫⁻ p, ENNReal.ofReal (T - h) * kON h (p.1 + p.2.1, p.2.2)
          ∂((eqLaw Foff).prod ((ν m).prod Fon)) := by
        refine lintegral_congr fun h => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ p, (∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * kON h (p.1 + p.2.1, p.2.2))
          ∂((eqLaw Foff).prod ((ν m).prod Fon)) :=
        lintegral_lintegral_swap hTk.aemeasurable
    _ = ∫⁻ y, ∫⁻ b, ∫⁻ x, (∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * kON h (y + b, x)) ∂Fon
          ∂(ν m) ∂(eqLaw Foff) := by
        have hJ : Measurable fun p : ℝ × ℝ × ℝ =>
            ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * kON h (p.1 + p.2.1, p.2.2) :=
          hTk.lintegral_prod_left'
        have hJy : ∀ y : ℝ, Measurable fun q : ℝ × ℝ =>
            ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * kON h (y + q.1, q.2) := fun y =>
          hJ.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_prod _ hJ.aemeasurable]
        refine lintegral_congr fun y => ?_
        exact lintegral_prod _ (hJy y).aemeasurable
    _ = ∫⁻ y, ∫⁻ b, psiT Fon T (y + b) ∂(ν m) ∂(eqLaw Foff) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hG0] with y hy
        refine lintegral_congr_ae ?_
        filter_upwards [hνm] with b hb
        exact kernel_psi Fon T (add_nonneg hy hb)
    _ = ∫⁻ p, psiT Fon T (p.1 + p.2) ∂((eqLaw Foff).prod (ν m)) :=
        (lintegral_prod _ ((psiT_measurable Fon T).comp
          (measurable_fst.add measurable_snd)).aemeasurable).symm

end Var3

section Var4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Law of the delay: `E g(T₀) = (μ_on/μ) ∫∫ g(w + x) dF_on⁰(x) dF_off(w) + (μ_off/μ) ∫ g dF_off⁰`. -/
theorem lintegral_T0 [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, g (s.T0 ω) ∂P =
      ENNReal.ofReal (mean Fon / mu Fon Foff) * ∫⁻ w, (∫⁻ x, g (w + x) ∂(eqLaw Fon)) ∂Foff +
      ENNReal.ofReal (mean Foff / mu Fon Foff) * ∫⁻ y, g y ∂(eqLaw Foff) := by
  have hBm : Measurable s.B := hs.measurable (Sum.inl 0)
  have hX0m : Measurable s.X0 := hs.measurable (Sum.inl 1)
  have hY0m : Measurable s.Y0 := hs.measurable (Sum.inl 2)
  have hYom : Measurable s.Yoff := hs.measurable (Sum.inl 3)
  have hi_pair : IndepFun (fun ω => (s.X0 ω, s.Yoff ω)) s.B P :=
    hs.indep.indepFun_prodMk hs.measurable (Sum.inl 1) (Sum.inl 3) (Sum.inl 0)
      (by decide) (by decide)
  have hi_BY0 : IndepFun s.B s.Y0 P := hs.indep.indepFun (i := Sum.inl 0) (j := Sum.inl 2)
    (by decide)
  have hi_YX : IndepFun s.Yoff s.X0 P := hs.indep.indepFun (i := Sum.inl 3) (j := Sum.inl 1)
    (by decide)
  have hS : MeasurableSet (({0, 1} : Set ℝ)ᶜ) :=
    (measurableSet_insert.2 (measurableSet_singleton 1)).compl
  have hB01 : ∀ᵐ ω ∂P, s.B ω = 0 ∨ s.B ω = 1 := by
    have h1 : P.map s.B (({0, 1} : Set ℝ)ᶜ) = 0 := by
      rw [hs.law_B, bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hS, Measure.dirac_apply' _ hS]
      simp
    rw [Measure.map_apply hBm hS] at h1
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h1
    simpa using hω
  have hPB : ∀ a : ℝ, P (s.B ⁻¹' {a}) = bernoulliLaw Fon Foff {a} := fun a => by
    rw [← Measure.map_apply hBm (measurableSet_singleton a), hs.law_B]
  have hPB1 : P (s.B ⁻¹' {1}) = ENNReal.ofReal (mean Fon / mu Fon Foff) := by
    rw [hPB, bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton 1),
      Measure.dirac_apply' _ (measurableSet_singleton 1)]
    simp
  have hPB0 : P (s.B ⁻¹' {0}) = ENNReal.ofReal (mean Foff / mu Fon Foff) := by
    rw [hPB, bernoulliLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton 0),
      Measure.dirac_apply' _ (measurableSet_singleton 0)]
    simp
  set g1 : Ω → ℝ≥0∞ := fun ω => ({1} : Set ℝ).indicator 1 (s.B ω) with hg1
  set g0 : Ω → ℝ≥0∞ := fun ω => ({0} : Set ℝ).indicator 1 (s.B ω) with hg0
  set k1 : Ω → ℝ≥0∞ := fun ω => g (s.X0 ω + s.Yoff ω) with hk1
  set k0 : Ω → ℝ≥0∞ := fun ω => g (s.Y0 ω) with hk0
  have hg1m : Measurable g1 := (measurable_one.indicator (measurableSet_singleton 1)).comp hBm
  have hg0m : Measurable g0 := (measurable_one.indicator (measurableSet_singleton 0)).comp hBm
  have hk1m : Measurable k1 := hg.comp (hX0m.add hYom)
  have hk0m : Measurable k0 := hg.comp hY0m
  have hdec : (fun ω => g (s.T0 ω)) =ᵐ[P] fun ω => g1 ω * k1 ω + g0 ω * k0 ω := by
    filter_upwards [hB01] with ω hω
    rcases hω with h | h
    · simp [hg1, hg0, hk0, Source.T0, h]
    · simp [hg1, hg0, hk1, Source.T0, h]
  have hI1 : ∫⁻ ω, g1 ω * k1 ω ∂P = ENNReal.ofReal (mean Fon / mu Fon Foff) * ∫⁻ ω, k1 ω ∂P := by
    have hind : IndepFun g1 k1 P := by
      have := hi_pair.symm.comp (φ := fun b => ({1} : Set ℝ).indicator (1 : ℝ → ℝ≥0∞) b)
        (ψ := fun p : ℝ × ℝ => g (p.1 + p.2))
        (measurable_one.indicator (measurableSet_singleton 1))
        (hg.comp (measurable_fst.add measurable_snd))
      exact this
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hg1m.aemeasurable
      hk1m.aemeasurable hind]
    congr 1
    rw [← hPB1, ← Measure.map_apply hBm (measurableSet_singleton 1),
      ← lintegral_indicator_one (measurableSet_singleton 1),
      lintegral_map (measurable_one.indicator (measurableSet_singleton 1)) hBm]
    try rfl
  have hI0 : ∫⁻ ω, g0 ω * k0 ω ∂P = ENNReal.ofReal (mean Foff / mu Fon Foff) * ∫⁻ ω, k0 ω ∂P := by
    have hind : IndepFun g0 k0 P :=
      hi_BY0.comp (measurable_one.indicator (measurableSet_singleton 0)) hg
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hg0m.aemeasurable
      hk0m.aemeasurable hind]
    congr 1
    rw [← hPB0, ← Measure.map_apply hBm (measurableSet_singleton 0),
      ← lintegral_indicator_one (measurableSet_singleton 0),
      lintegral_map (measurable_one.indicator (measurableSet_singleton 0)) hBm]
    try rfl
  have hK1 : ∫⁻ ω, k1 ω ∂P = ∫⁻ w, (∫⁻ x, g (w + x) ∂(eqLaw Fon)) ∂Foff := by
    have := lintegral_indep_pair hYom hX0m hi_YX
      (F := fun p : ℝ × ℝ => g (p.1 + p.2)) (hg.comp (measurable_fst.add measurable_snd))
    rw [hs.law_X0, hs.law_Yoff] at this
    rw [← this, hk1]
    refine lintegral_congr fun ω => ?_
    simp only
    rw [add_comm]
  have hK0 : ∫⁻ ω, k0 ω ∂P = ∫⁻ t, g t ∂(eqLaw Foff) := by
    rw [← hs.law_Y0]
    exact (lintegral_map hg hY0m).symm
  rw [lintegral_congr_ae hdec, lintegral_add_left (f := fun ω => g1 ω * k1 ω) (hg1m.mul hk1m),
    hI1, hI0, hK1, hK0]

/-- **Renewal identity split along the delay**: for `f ≥ 0` measurable,
`Σ_n ∫ [(μ_on/μ) ∫∫ f(w + x + b) dF_on⁰ dF_off + (μ_off/μ) ∫ f(y + b) dF_off⁰] dν_n(b) = μ⁻¹ ∫_0^∞ f`. -/
theorem renewal_split [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∑' n, ∫⁻ b, (ENNReal.ofReal (mean Fon / mu Fon Foff) *
        ∫⁻ w, (∫⁻ x, f (w + x + b) ∂(eqLaw Fon)) ∂Foff +
      ENNReal.ofReal (mean Foff / mu Fon Foff) * ∫⁻ y, f (y + b) ∂(eqLaw Foff))
        ∂(P.map (psum (srcZ s) n)) =
    ENNReal.ofReal (mu Fon Foff)⁻¹ * ∫⁻ x in Set.Ioi 0, f x := by
  rw [← source_renewal hon0 hoff0 hon hoff hion hioff hs f hf]
  refine tsum_congr fun n => ?_
  symm
  have hT0 := T0_measurable hs
  have hS := psum_measurable (srcZ_measurable hs) n
  have e : ∀ ω, s.Tn n ω = s.T0 ω + psum (srcZ s) n ω := fun ω => rfl
  rw [lintegral_congr fun ω => congrArg f (e ω)]
  have := lintegral_indep_pair hS hT0 (indep_psum_T0 hs n)
    (F := fun p : ℝ × ℝ => f (p.2 + p.1)) (hf.comp (measurable_snd.add measurable_fst))
  simp only at this
  rw [this]
  refine lintegral_congr fun b => ?_
  rw [lintegral_map (f := fun v => f (v + b)) (hf.comp (measurable_id.add measurable_const)) hT0,
    lintegral_T0 hs (fun t => f (t + b)) (hf.comp (measurable_id.add measurable_const))]

end Var4

section Var5

/-! Exact decomposition: with `p = μ_on/μ`, `q = μ_off/μ`,
`p·aFG + q·aG + p·E1 = aGF + q·Main + p·E2` (all `ℝ≥0∞`). -/

theorem ofReal_sub_add_min {t w : ℝ} (hw : 0 ≤ w) :
    ENNReal.ofReal (t - w) + ENNReal.ofReal (min w t) = ENNReal.ofReal t := by
  rcases le_total t 0 with ht | ht
  · rw [ENNReal.ofReal_of_nonpos (by linarith), ENNReal.ofReal_of_nonpos ((min_le_right _ _).trans ht),
      ENNReal.ofReal_of_nonpos ht, add_zero]
  · rcases le_total w t with hwt | hwt
    · rw [min_eq_left hwt, ← ENNReal.ofReal_add (by linarith) hw, sub_add_cancel]
    · rw [min_eq_right hwt, ENNReal.ofReal_of_nonpos (by linarith), zero_add]

theorem eqLaw_isProb (F : Measure ℝ) [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (hm : 0 < mean F) : IsProbabilityMeasure (eqLaw F) := by
  constructor
  rw [eqLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h1 : ∀ x, ENNReal.ofReal (Fbar F x / mean F) =
      ENNReal.ofReal (Fbar F x) * ENNReal.ofReal (mean F)⁻¹ := fun x => by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul' (inv_nonneg.2 hm.le)]
  simp_rw [h1]
  rw [lintegral_mul_const _ (Fbar_measurable F).ennreal_ofReal, lintegral_Fbar_eq_mean F h0 hi,
    ← ENNReal.ofReal_mul hm.le, mul_inv_cancel₀ hm.ne', ENNReal.ofReal_one]

theorem meas_iter (μ1 μ2 : Measure ℝ) [SFinite μ1] [SFinite μ2] (k : ℝ → ℝ → ℝ → ℝ≥0∞)
    (hk : Measurable fun q : ℝ × ℝ × ℝ => k q.1 q.2.1 q.2.2) :
    Measurable fun b => ∫⁻ w, (∫⁻ x, k w x b ∂μ2) ∂μ1 := by
  have h1 : Measurable fun q : (ℝ × ℝ) × ℝ => k q.1.1 q.2 q.1.2 :=
    hk.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have h2 : Measurable fun p : ℝ × ℝ => ∫⁻ x, k p.1 x p.2 ∂μ2 := h1.lintegral_prod_right'
  exact h2.lintegral_prod_left'

theorem iter_add (μ1 μ2 : Measure ℝ) [SFinite μ2] (a c : ℝ → ℝ → ℝ≥0∞)
    (ha : Measurable fun q : ℝ × ℝ => a q.1 q.2) :
    ∫⁻ w, (∫⁻ x, a w x ∂μ2) ∂μ1 + ∫⁻ w, (∫⁻ x, c w x ∂μ2) ∂μ1 =
      ∫⁻ w, (∫⁻ x, (a w x + c w x) ∂μ2) ∂μ1 := by
  rw [← lintegral_add_left (f := fun w => ∫⁻ x, a w x ∂μ2) ha.lintegral_prod_right']
  refine lintegral_congr fun w => ?_
  exact (lintegral_add_left (f := fun x => a w x)
    (ha.comp (measurable_const.prodMk measurable_id)) _).symm

/-- ae nonnegativity from `μ (Iio 0) = 0`. -/
theorem ae_nonneg_of_Iio (μ : Measure ℝ) (h : μ (Set.Iio 0) = 0) : ∀ᵐ y ∂μ, 0 ≤ y := by
  rw [ae_iff]
  exact measure_mono_null (fun a (ha : ¬ 0 ≤ a) => (not_le.1 ha : a < 0)) h

variable (Fon Foff : Measure ℝ) (ν : ℕ → Measure ℝ) (T : ℝ)

noncomputable def aGk : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff)) ∂(ν n)

noncomputable def aFGk : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff) ∂(ν n)

noncomputable def aGFk : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff)) ∂(ν n)

noncomputable def MainK : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon))
    ∂(eqLaw Foff)) ∂(ν n)

noncomputable def E1K : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff) ∂(ν n)

noncomputable def E2K : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon))
    ∂(eqLaw Foff)) ∂(ν n)

variable {Fon Foff ν T}

theorem decomp_ident [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    [∀ n, SFinite (ν n)]
    (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {p q : ℝ≥0∞} (hpq : p + q = 1) :
    p * aFGk Fon Foff ν T + q * aGk Foff ν T + p * E1K Fon Foff ν T =
      aGFk Fon Foff ν T + q * MainK Fon Foff ν T + p * E2K Fon Foff ν T := by
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  have : IsProbabilityMeasure (eqLaw Foff) := eqLaw_isProb Foff hoff0 hioff hoff
  have hp : p ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hpq ▸ le_self_add)
  have hq : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hpq ▸ le_add_self)
  have hF0 := ae_nonneg_of_Iio (eqLaw Fon) (eqLaw_Iio_zero Fon)
  have hG0 := ae_nonneg_of_Iio (eqLaw Foff) (eqLaw_Iio_zero Foff)
  have hG := ae_nonneg_of_Iio Foff hoff0
  have mo : Measurable fun t : ℝ => ENNReal.ofReal t := ENNReal.measurable_ofReal
  -- measurability of the inner functions of `b`
  have mFG := meas_iter Foff (eqLaw Fon) (fun w x b => ENNReal.ofReal (T - (w + x + b)))
    (mo.comp (measurable_const.sub ((measurable_fst.add (measurable_fst.comp measurable_snd)).add
      (measurable_snd.comp measurable_snd))))
  have mGF := meas_iter (eqLaw Foff) (eqLaw Fon) (fun y x b => ENNReal.ofReal (T - (y + b) - x))
    (mo.comp ((measurable_const.sub (measurable_fst.add (measurable_snd.comp measurable_snd))).sub
      (measurable_fst.comp measurable_snd)))
  have mMain := meas_iter (eqLaw Foff) (eqLaw Fon)
    (fun y x b => ENNReal.ofReal (min x (T - (y + b))))
    (mo.comp ((measurable_fst.comp measurable_snd).min
      (measurable_const.sub (measurable_fst.add (measurable_snd.comp measurable_snd)))))
  have mG : Measurable fun b => ∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff) := by
    have : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (T - (q.2 + q.1)) :=
      mo.comp (measurable_const.sub (measurable_snd.add measurable_fst))
    exact this.lintegral_prod_right'
  -- the pointwise identities
  have L1 : ∀ b, ∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff +
      ∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff =
      ∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon) := by
    intro b
    rw [iter_add Foff (eqLaw Fon) _ _ (mo.comp (measurable_const.sub
      ((measurable_fst.add measurable_snd).add measurable_const)))]
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)) ?_,
      lintegral_const, measure_univ, mul_one]
    filter_upwards [hG] with w hw
    refine lintegral_congr fun x => ?_
    rw [show T - (w + x + b) = (T - (x + b)) - w by ring, ofReal_sub_add_min hw]
  have L2 : ∀ b, ∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
      ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff) =
      ∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon) := by
    intro b
    rw [iter_add (eqLaw Foff) (eqLaw Fon) _ _ (mo.comp ((measurable_const.sub
      (measurable_fst.add measurable_const)).sub measurable_snd))]
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)) ?_,
      lintegral_const, measure_univ, mul_one]
    filter_upwards [hG0] with y hy
    refine lintegral_congr fun x => ?_
    rw [show T - (y + b) - x = (T - (x + b)) - y by ring, ofReal_sub_add_min hy]
  have L3 : ∀ b, ∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
      ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff) =
      ∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff) := by
    intro b
    rw [iter_add (eqLaw Foff) (eqLaw Fon) _ _ (mo.comp ((measurable_const.sub
      (measurable_fst.add measurable_const)).sub measurable_snd))]
    refine lintegral_congr fun y => ?_
    rw [lintegral_congr_ae (g := fun _ => ENNReal.ofReal (T - (y + b))) ?_,
      lintegral_const, measure_univ, mul_one]
    filter_upwards [hF0] with x hx
    exact ofReal_sub_add_min hx
  -- assemble per `b`
  have hb : ∀ b, p * ∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff +
      q * ∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff) +
      p * ∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff =
      ∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
      q * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
      p * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff) := by
    intro b
    calc _ = p * (∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff +
          ∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff) +
          q * ∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff) := by ring
      _ = p * (∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
          ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff)) +
          q * (∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
          ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff)) := by
        rw [L1, L2, L3]
      _ = (p + q) * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
          q * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
          p * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff) := by
        ring
      _ = _ := by rw [hpq, one_mul]
  -- integrate in `b` and sum over `n`
  have hn : ∀ n, p * ∫⁻ b, (∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff)
        ∂(ν n) + q * ∫⁻ b, (∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff)) ∂(ν n) +
      p * ∫⁻ b, (∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff) ∂(ν n) =
      ∫⁻ b, (∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff)) ∂(ν n) +
      q * ∫⁻ b, (∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon))
        ∂(eqLaw Foff)) ∂(ν n) +
      p * ∫⁻ b, (∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon))
        ∂(eqLaw Foff)) ∂(ν n) := by
    intro n
    rw [← lintegral_const_mul' _ _ hp, ← lintegral_const_mul' _ _ hq, ← lintegral_const_mul' _ _ hp,
      ← lintegral_const_mul' _ _ hq, ← lintegral_const_mul' _ _ hp,
      ← lintegral_add_left ((mFG).const_mul p), ← lintegral_add_left
        (f := fun b => p * ∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff +
          q * ∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff))
        (((mFG).const_mul p).add ((mG).const_mul q)),
      ← lintegral_add_left mGF, ← lintegral_add_left
        (f := fun b => ∫⁻ y, (∫⁻ x, ENNReal.ofReal (T - (y + b) - x) ∂(eqLaw Fon)) ∂(eqLaw Foff) +
          q * ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff))
        (mGF.add ((mMain).const_mul q))]
    exact lintegral_congr hb
  unfold aFGk aGk E1K aGFk MainK E2K
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add,
    ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  exact tsum_congr hn

end Var5

section Var6

theorem psiT_eq (F : Measure ℝ) [IsProbabilityMeasure F] (hm : 0 < mean F) (T c : ℝ) :
    psiT F T c = ENNReal.ofReal (mean F) * ∫⁻ x, ENNReal.ofReal (T - c - x) ∂(eqLaw F) := by
  have hFb := Fbar_measurable F
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (T - c - x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)
  rw [eqLaw, lintegral_withDensity_eq_lintegral_mul _ (hFb.div_const _).ennreal_ofReal hg,
    ← lintegral_const_mul _ (((hFb.div_const _).ennreal_ofReal).mul hg)]
  unfold psiT
  refine lintegral_congr fun r => ?_
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hm.le,
    show mean F * (Fbar F r / mean F) = Fbar F r by field_simp]
  ring

theorem AGF_eq (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (ν : ℕ → Measure ℝ) [∀ j, SFinite (ν j)] (hon : 0 < mean Fon) (T : ℝ) :
    AGF Fon Foff ν T = ENNReal.ofReal (mean Fon) * aGFk Fon Foff ν T := by
  have : SFinite (eqLaw Foff) := by unfold eqLaw; infer_instance
  unfold AGF aGFk
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hm : Measurable fun p : ℝ × ℝ => psiT Fon T (p.1 + p.2) :=
    (psiT_measurable Fon T).comp (measurable_fst.add measurable_snd)
  rw [lintegral_prod _ hm.aemeasurable]
  dsimp only
  rw [lintegral_lintegral_swap (f := fun y b => psiT Fon T (y + b)) hm.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun b => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  exact psiT_eq Fon hon T (y + b)

theorem lintegral_ramp {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (T - x) = ENNReal.ofReal (T ^ 2 / 2) := by
  have h1 : ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (T - x) =
      ∫⁻ x in Set.Ioi 0, (Set.Iic T).indicator (fun x => ENNReal.ofReal (T - x)) x := by
    refine lintegral_congr fun x => ?_
    by_cases hx : x ≤ T
    · rw [Set.indicator_of_mem (show x ∈ Set.Iic T from hx)]
    · rw [Set.indicator_of_notMem (show x ∉ Set.Iic T from hx),
        ENNReal.ofReal_of_nonpos (by linarith [not_le.1 hx])]
  rw [h1, lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Set.inter_comm, Set.Ioi_inter_Iic, ← ofReal_integral_eq_lintegral_ofReal (f := fun x => T - x)
      ((continuous_const.sub continuous_id').integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => sub_nonneg.2 hx.2)),
    ← intervalIntegral.integral_of_le hT, intervalIntegral.integral_sub intervalIntegrable_const
      (continuous_id'.intervalIntegrable 0 T), intervalIntegral.integral_const, integral_id,
    smul_eq_mul]
  congr 1; ring

variable {Fon Foff : Measure ℝ} {ν : ℕ → Measure ℝ} {T : ℝ}

theorem rs_split_eq [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff] [∀ n, SFinite (ν n)]
    {p q : ℝ≥0∞} (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∑' n, ∫⁻ b, (p * ∫⁻ w, (∫⁻ x, ENNReal.ofReal (T - (w + x + b)) ∂(eqLaw Fon)) ∂Foff +
      q * ∫⁻ y, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Foff)) ∂(ν n) =
    p * aFGk Fon Foff ν T + q * aGk Foff ν T := by
  have : SFinite (eqLaw Fon) := by unfold eqLaw; infer_instance
  have mo : Measurable fun t : ℝ => ENNReal.ofReal t := ENNReal.measurable_ofReal
  have mFG := meas_iter Foff (eqLaw Fon) (fun w x b => ENNReal.ofReal (T - (w + x + b)))
    (mo.comp (measurable_const.sub ((measurable_fst.add (measurable_fst.comp measurable_snd)).add
      (measurable_snd.comp measurable_snd))))
  unfold aFGk aGk
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [lintegral_add_left (mFG.const_mul p), lintegral_const_mul' _ _ hp,
    lintegral_const_mul' _ _ hq]

end Var6

end NetTraffic.OnOffFBM.Lib

end F05Part1

-- ==== part Karamata.lean ====
section F05Part2

/-! Karamata's theorems for antitone regularly varying functions (C2b, step A4).
Potter bounds from `f(2x)/f(x) → 2^{-ρ}` plus monotonicity, then dominated convergence. -/

open MeasureTheory Filter Topology Set

namespace NetTraffic.OnOffFBM.Lib

theorem two_rpow_pow (e : ℝ) (k : ℕ) : ((2:ℝ) ^ e) ^ k = ((2:ℝ) ^ k) ^ e := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

theorem potter_step {f : ℝ → ℝ} (hpos : ∀ x, 0 < f x) {ρ : ℝ}
    (hrv : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 ((2:ℝ) ^ (-ρ)))) {ε : ℝ} (hε : 0 < ε) :
    ∃ x0 : ℝ, 0 < x0 ∧ ∀ x, x0 ≤ x →
      f (2 * x) ≤ (2:ℝ) ^ (-ρ + ε) * f x ∧ f x ≤ (2:ℝ) ^ (ρ + ε) * f (2 * x) := by
  have h1 : (2:ℝ) ^ (-ρ) < (2:ℝ) ^ (-ρ + ε) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h2 : (2:ℝ) ^ (-ρ - ε) < (2:ℝ) ^ (-ρ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨x0, hx0⟩ := eventually_atTop.1
    ((hrv.eventually (gt_mem_nhds h1)).and (hrv.eventually (lt_mem_nhds h2)))
  refine ⟨max x0 1, by positivity, fun x hx => ?_⟩
  obtain ⟨ha, hb⟩ := hx0 x (le_trans (le_max_left _ _) hx)
  have hfx := hpos x
  rw [div_lt_iff₀ hfx] at ha
  rw [lt_div_iff₀ hfx] at hb
  refine ⟨ha.le, ?_⟩
  have hAB : (2:ℝ) ^ (ρ + ε) * (2:ℝ) ^ (-ρ - ε) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    have : ρ + ε + (-ρ - ε) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hA : 0 < (2:ℝ) ^ (ρ + ε) := Real.rpow_pos_of_pos (by norm_num) _
  calc f x = (2:ℝ) ^ (ρ + ε) * ((2:ℝ) ^ (-ρ - ε) * f x) := by rw [← mul_assoc, hAB, one_mul]
    _ ≤ (2:ℝ) ^ (ρ + ε) * f (2 * x) := by gcongr

theorem potter_iter {f : ℝ → ℝ} {x0 a b : ℝ} (hx0 : 0 < x0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ x, x0 ≤ x → f (2 * x) ≤ a * f x ∧ f x ≤ b * f (2 * x)) :
    ∀ k : ℕ, ∀ x, x0 ≤ x → f (2 ^ k * x) ≤ a ^ k * f x ∧ f x ≤ b ^ k * f (2 ^ k * x) := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    obtain ⟨ih1, ih2⟩ := ih x hx
    have hk : x0 ≤ 2 ^ k * x := by
      have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    obtain ⟨h1, h2⟩ := h _ hk
    have e : (2:ℝ) ^ (k + 1) * x = 2 * (2 ^ k * x) := by ring
    rw [e]
    constructor
    · calc f (2 * (2 ^ k * x)) ≤ a * f (2 ^ k * x) := h1
        _ ≤ a * (a ^ k * f x) := by gcongr
        _ = a ^ (k + 1) * f x := by ring
    · calc f x ≤ b ^ k * f (2 ^ k * x) := ih2
        _ ≤ b ^ k * (b * f (2 * (2 ^ k * x))) := by gcongr
        _ = b ^ (k + 1) * f (2 * (2 ^ k * x)) := by ring

/-- Potter bounds for an antitone positive function with `f(2x)/f(x) → 2^{-ρ}`. -/
theorem potter_antitone {f : ℝ → ℝ} (hf : Antitone f) (hpos : ∀ x, 0 < f x) {ρ : ℝ}
    (hrv : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 ((2:ℝ) ^ (-ρ)))) {ε : ℝ} (hε : 0 < ε)
    (hερ : ε < ρ) :
    ∃ C x0 : ℝ, 0 < x0 ∧ 0 < C ∧ ∀ x y, x0 ≤ x → x ≤ y →
      f y ≤ C * (y / x) ^ (-ρ + ε) * f x ∧ f x ≤ C * (y / x) ^ (ρ + ε) * f y := by
  obtain ⟨x0, hx0, hstep⟩ := potter_step hpos hrv hε
  have hit := potter_iter hx0 (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-ρ + ε)).le
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (ρ + ε)).le hstep
  set C1 : ℝ := (2:ℝ) ^ (ρ - ε)
  set C2 : ℝ := (2:ℝ) ^ (ρ + ε)
  have hC1 : 0 < C1 := Real.rpow_pos_of_pos (by norm_num) _
  have hC2 : 0 < C2 := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C1 + C2, x0, hx0, by positivity, fun x y hx hxy => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  have hr : 1 ≤ y / x := by rw [le_div_iff₀ hxpos]; linarith
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hr (by norm_num : (1:ℝ) < 2)
  have hk1' : (2:ℝ) ^ k * x ≤ y := by rwa [le_div_iff₀ hxpos] at hk1
  have hk2' : y < (2:ℝ) ^ (k + 1) * x := by rwa [div_lt_iff₀ hxpos] at hk2
  obtain ⟨i1, -⟩ := hit k x hx
  obtain ⟨-, i2⟩ := hit (k + 1) x hx
  have hfy := hpos y
  have hfx := hpos x
  have hyx : 0 < y / x := by linarith
  constructor
  · have hmono : f y ≤ f (2 ^ k * x) := hf hk1'
    have hpow : ((2:ℝ) ^ (-ρ + ε)) ^ k ≤ C1 * (y / x) ^ (-ρ + ε) := by
      rw [two_rpow_pow]
      have hlow : y / x / 2 ≤ (2:ℝ) ^ k := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        have : (2:ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        linarith
      calc ((2:ℝ) ^ k) ^ (-ρ + ε) ≤ (y / x / 2) ^ (-ρ + ε) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
        _ = C1 * (y / x) ^ (-ρ + ε) := by
            rw [Real.div_rpow hyx.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            have : -(-ρ + ε) = ρ - ε := by ring
            rw [this]; ring
    calc f y ≤ ((2:ℝ) ^ (-ρ + ε)) ^ k * f x := hmono.trans i1
      _ ≤ (C1 * (y / x) ^ (-ρ + ε)) * f x := by gcongr
      _ ≤ (C1 + C2) * (y / x) ^ (-ρ + ε) * f x := by
          gcongr
          linarith
  · have hmono : f (2 ^ (k + 1) * x) ≤ f y := hf hk2'.le
    have hpow : ((2:ℝ) ^ (ρ + ε)) ^ (k + 1) ≤ C2 * (y / x) ^ (ρ + ε) := by
      rw [two_rpow_pow]
      have hup : (2:ℝ) ^ (k + 1) ≤ 2 * (y / x) := by
        have : (2:ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        linarith
      calc ((2:ℝ) ^ (k + 1)) ^ (ρ + ε) ≤ (2 * (y / x)) ^ (ρ + ε) :=
            Real.rpow_le_rpow (by positivity) hup (by linarith)
        _ = C2 * (y / x) ^ (ρ + ε) := Real.mul_rpow (by norm_num) hyx.le
    have hb0 : 0 ≤ ((2:ℝ) ^ (ρ + ε)) ^ (k + 1) := by positivity
    calc f x ≤ ((2:ℝ) ^ (ρ + ε)) ^ (k + 1) * f (2 ^ (k + 1) * x) := i2
      _ ≤ ((2:ℝ) ^ (ρ + ε)) ^ (k + 1) * f y := by gcongr
      _ ≤ (C2 * (y / x) ^ (ρ + ε)) * f y := by gcongr
      _ ≤ (C1 + C2) * (y / x) ^ (ρ + ε) * f y := by
          gcongr
          linarith

/-- Karamata, tail form: `∫_x^∞ f / (x f(x)) → 1/(ρ-1)` for `ρ > 1`. -/
theorem karamata_tail {f : ℝ → ℝ} (hf : Antitone f) (hpos : ∀ x, 0 < f x) {ρ : ℝ} (hρ : 1 < ρ)
    (hrv : ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ (-ρ)))) :
    Tendsto (fun x => (∫ v in Ioi x, f v) / (x * f x)) atTop (𝓝 (1 / (ρ - 1))) := by
  set ε : ℝ := (ρ - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, x0, hx0, hC, hpot⟩ := potter_antitone hf hpos (hrv 2 two_pos) hε (by linarith)
  have hfm : Measurable f := hf.measurable
  have hrep : ∀ x, 0 < x → (∫ v in Ioi x, f v) / (x * f x) = ∫ w in Ioi (1:ℝ), f (x * w) / f x := by
    intro x hx
    rw [integral_div, integral_comp_mul_left_Ioi f 1 hx, mul_one, smul_eq_mul]
    have := hpos x
    field_simp
  have hlim : Tendsto (fun x => ∫ w in Ioi (1:ℝ), f (x * w) / f x) atTop
      (𝓝 (∫ w in Ioi (1:ℝ), w ^ (-ρ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => C * w ^ (-ρ + ε)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        ((hfm.comp (measurable_const_mul x)).div_const _).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop x0] with x hx
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
      have hw1 : (1:ℝ) < w := hw
      have hxp : 0 < x := lt_of_lt_of_le hx0 hx
      have hxw : x ≤ x * w := by nlinarith
      have h1 := (hpot x (x * w) hx hxw).1
      rw [mul_div_cancel_left₀ w hxp.ne'] at h1
      have hfx := hpos x
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (hpos _) hfx), div_le_iff₀ hfx]
      exact h1
    · exact (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
      have hw0 : (0:ℝ) < w := lt_trans one_pos hw
      simpa [mul_comm] using hrv w hw0
  have hval : ∫ w in Ioi (1:ℝ), w ^ (-ρ) = 1 / (ρ - 1) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -ρ + 1 = -(ρ - 1) by ring, div_neg, neg_div, neg_neg]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (hrep x hx).symm

/-- Karamata, head form with kernel `T - u`, for `0 < ρ < 1`. -/
theorem karamata_head {f : ℝ → ℝ} (hf : Antitone f) (hpos : ∀ x, 0 < f x) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1)
    (hrv : ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ (-ρ)))) :
    Tendsto (fun T => (∫ u in (0:ℝ)..T, f u * (T - u)) / (T ^ 2 * f T)) atTop
      (𝓝 (∫ v in (0:ℝ)..1, v ^ (-ρ) * (1 - v))) := by
  set ε : ℝ := min (ρ / 2) ((1 - ρ) / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ ρ / 2 := min_le_left _ _
  have hε2 : ε ≤ (1 - ρ) / 2 := min_le_right _ _
  obtain ⟨C, x0, hx0, hC, hpot⟩ := potter_antitone hf hpos (hrv 2 two_pos) hε (by linarith)
  have hfm : Measurable f := hf.measurable
  set C' : ℝ := C * (1 + f 0 / f x0) with hC'
  have hC'0 : 0 < C' := by
    have := hpos 0; have := hpos x0; positivity
  have hrep : ∀ T, 0 < T → (∫ u in (0:ℝ)..T, f u * (T - u)) / (T ^ 2 * f T) =
      ∫ v in (0:ℝ)..1, f (T * v) / f T * (1 - v) := by
    intro T hT
    have e1 : ∀ v, f (T * v) / f T * (1 - v) = (fun u => f u * (T - u)) (T * v) / (T * f T) := by
      intro v
      have := hpos T
      simp only
      field_simp
    simp_rw [e1]
    have hcv := intervalIntegral.integral_comp_mul_left (fun u => f u * (T - u)) hT.ne'
      (a := 0) (b := 1)
    rw [intervalIntegral.integral_div, hcv, mul_zero, mul_one, smul_eq_mul]
    have := hpos T
    field_simp
  have hlim : Tendsto (fun T => ∫ v in (0:ℝ)..1, f (T * v) / f T * (1 - v)) atTop
      (𝓝 (∫ v in (0:ℝ)..1, v ^ (-ρ) * (1 - v))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun v => C' * v ^ (-(ρ + ε))) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun T =>
        (((hfm.comp (measurable_const_mul T)).div_const _).mul
          (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop x0] with T hT
      refine Eventually.of_forall fun v hv => ?_
      rw [Set.uIoc_of_le zero_le_one] at hv
      obtain ⟨hv0, hv1⟩ := hv
      have hTp : 0 < T := lt_of_lt_of_le hx0 hT
      have hfT := hpos T
      have hq : 0 ≤ f (T * v) / f T := (div_pos (hpos _) hfT).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq (by linarith))]
      have hvpow : 1 ≤ v ^ (-(ρ + ε)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv0 hv1 (by linarith)
      have key : f (T * v) / f T ≤ C' * v ^ (-(ρ + ε)) := by
        rw [div_le_iff₀ hfT]
        by_cases hTv : x0 ≤ T * v
        · have h2 := (hpot (T * v) T hTv (by nlinarith)).2
          have e : T / (T * v) = v⁻¹ := by field_simp
          rw [e, Real.inv_rpow hv0.le, ← Real.rpow_neg hv0.le] at h2
          calc f (T * v) ≤ C * v ^ (-(ρ + ε)) * f T := h2
            _ ≤ C' * v ^ (-(ρ + ε)) * f T := by
                gcongr
                rw [hC']
                have : 0 ≤ f 0 / f x0 := (div_pos (hpos 0) (hpos x0)).le
                nlinarith
        · push Not at hTv
          have h2 := (hpot x0 T le_rfl hT).2
          have hle0 : f (T * v) ≤ f 0 := hf (by positivity)
          have hTv' : T / x0 ≤ v⁻¹ := by
            rw [div_le_iff₀ hx0, inv_mul_eq_div, le_div_iff₀ hv0]; linarith
          have h3 : (T / x0) ^ (ρ + ε) ≤ v ^ (-(ρ + ε)) := by
            rw [Real.rpow_neg hv0.le, ← Real.inv_rpow hv0.le]
            exact Real.rpow_le_rpow (by positivity) hTv' (by linarith)
          have hfx0 := hpos x0
          calc f (T * v) ≤ f 0 := hle0
            _ = f 0 / f x0 * f x0 := by field_simp
            _ ≤ f 0 / f x0 * (C * (T / x0) ^ (ρ + ε) * f T) := by
                gcongr; exact (div_pos (hpos 0) hfx0).le
            _ ≤ f 0 / f x0 * (C * v ^ (-(ρ + ε)) * f T) := by
                gcongr; exact (div_pos (hpos 0) hfx0).le
            _ ≤ C' * v ^ (-(ρ + ε)) * f T := by
                rw [hC']
                have : 0 ≤ C * v ^ (-(ρ + ε)) * f T := by positivity
                nlinarith
      calc f (T * v) / f T * (1 - v) ≤ f (T * v) / f T * 1 := by gcongr; linarith
        _ ≤ C' * v ^ (-(ρ + ε)) := by rw [mul_one]; exact key
    · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C'
    · refine Eventually.of_forall fun v hv => ?_
      rw [Set.uIoc_of_le zero_le_one] at hv
      have hv0 : 0 < v := hv.1
      have := hrv v hv0
      simp only [mul_comm v] at this
      exact this.mul_const _
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (hrep T hT).symm

theorem integral_kernel {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∫ v in (0:ℝ)..1, v ^ (-ρ) * (1 - v) = 1 / ((1 - ρ) * (2 - ρ)) := by
  have e : ∀ v ∈ Set.uIcc (0:ℝ) 1, v ^ (-ρ) * (1 - v) = v ^ (-ρ) - v ^ (-ρ + 1) := by
    intro v hv
    rw [Set.uIcc_of_le zero_le_one] at hv
    rcases eq_or_lt_of_le hv.1 with h | h
    · subst h
      rw [Real.zero_rpow (by linarith : -ρ < 0).ne, Real.zero_rpow (by linarith : (0:ℝ) < -ρ + 1).ne']
      ring
    · rw [Real.rpow_add_one h.ne']; ring
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub
    (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)),
    integral_rpow (Or.inl (by linarith)), integral_rpow (Or.inl (by linarith))]
  have h1 : -ρ + 1 ≠ 0 := (by linarith : (0:ℝ) < -ρ + 1).ne'
  have h2 : -ρ + 1 + 1 ≠ 0 := (by linarith : (0:ℝ) < -ρ + 1 + 1).ne'
  have h3 : (1 - ρ) ≠ 0 := (by linarith : (0:ℝ) < 1 - ρ).ne'
  have h4 : (2 - ρ) ≠ 0 := (by linarith : (0:ℝ) < 2 - ρ).ne'
  simp only [Real.one_rpow]
  rw [Real.zero_rpow h1, Real.zero_rpow h2]
  field_simp
  ring

end NetTraffic.OnOffFBM.Lib

end F05Part2

-- ==== part C2b.lean ====
section F05Part3

/-! ### C2b step 7: the exact variance decomposition
`Var G_T = 2 q μon (q MainK + p (E2K - E1K))`, `p = μon/μ`, `q = μoff/μ`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Var7

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

noncomputable def aFk (Fon : Measure ℝ) (ν : ℕ → Measure ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∑' n, ∫⁻ b, (∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)) ∂(ν n)

theorem rs_ramp [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (mean Fon / mu Fon Foff) * aFGk Fon Foff (fun j => P.map (psum (srcZ s) j)) T +
      ENNReal.ofReal (mean Foff / mu Fon Foff) * aGk Foff (fun j => P.map (psum (srcZ s) j)) T =
    ENNReal.ofReal (mu Fon Foff)⁻¹ * ENNReal.ofReal (T ^ 2 / 2) := by
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (T - t) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_id)
  have h := renewal_split hon0 hoff0 hon hoff hion hioff hs (fun t => ENNReal.ofReal (T - t)) hf
  rw [lintegral_ramp hT] at h
  rw [← h, rs_split_eq ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]

theorem aFk_le (Fon Foff : Measure ℝ) [IsProbabilityMeasure Foff] (ν : ℕ → Measure ℝ)
    (T s : ℝ) : Foff (Set.Iic s) * aFk Fon ν T ≤ aFGk Fon Foff ν (T + s) := by
  unfold aFk aFGk
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_const_mul' _ _ (measure_ne_top _ _)]
  refine lintegral_mono fun b => ?_
  calc Foff (Set.Iic s) * ∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)
      = ∫⁻ w, (Set.Iic s).indicator (fun _ => ∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)) w
          ∂Foff := by
        rw [lintegral_indicator_const measurableSet_Iic, mul_comm]
    _ ≤ ∫⁻ w, (∫⁻ x, ENNReal.ofReal (T + s - (w + x + b)) ∂(eqLaw Fon)) ∂Foff := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ Set.Iic s
        · rw [Set.indicator_of_mem hw]
          refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
          have : w ≤ s := hw
          linarith
        · rw [Set.indicator_of_notMem hw]
          exact zero_le

theorem MainK_le (Fon Foff : Measure ℝ) [IsProbabilityMeasure (eqLaw Fon)] (ν : ℕ → Measure ℝ)
    (T : ℝ) : MainK Fon Foff ν T ≤ aGk Foff ν T := by
  unfold MainK aGk
  refine ENNReal.tsum_le_tsum fun n => lintegral_mono fun b => lintegral_mono fun y => ?_
  calc ∫⁻ x, ENNReal.ofReal (min x (T - (y + b))) ∂(eqLaw Fon)
      ≤ ∫⁻ _x, ENNReal.ofReal (T - (y + b)) ∂(eqLaw Fon) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ENNReal.ofReal (T - (y + b)) := by rw [lintegral_const, measure_univ, mul_one]

theorem E1K_le (Fon Foff : Measure ℝ) [IsProbabilityMeasure Foff] (ν : ℕ → Measure ℝ)
    (T : ℝ) : E1K Fon Foff ν T ≤ aFk Fon ν T := by
  unfold E1K aFk
  refine ENNReal.tsum_le_tsum fun n => lintegral_mono fun b => ?_
  calc ∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff
      ≤ ∫⁻ _w, (∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)) ∂Foff :=
        lintegral_mono fun w => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

theorem E2K_le (Fon Foff : Measure ℝ) [IsProbabilityMeasure (eqLaw Foff)] (ν : ℕ → Measure ℝ)
    (T : ℝ) : E2K Fon Foff ν T ≤ aFk Fon ν T := by
  unfold E2K aFk
  refine ENNReal.tsum_le_tsum fun n => lintegral_mono fun b => ?_
  calc ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff)
      ≤ ∫⁻ _y, (∫⁻ x, ENNReal.ofReal (T - (x + b)) ∂(eqLaw Fon)) ∂(eqLaw Foff) :=
        lintegral_mono fun w => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

theorem exists_Iic_pos (F : Measure ℝ) [IsProbabilityMeasure F] :
    ∃ s : ℝ, 0 ≤ s ∧ 0 < F (Set.Iic s) := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have h0 : ∀ n : ℕ, F (Set.Iic (n : ℝ)) = 0 := fun n =>
    le_antisymm (hcon n (Nat.cast_nonneg n)) (zero_le)
  have hU : (⋃ n : ℕ, Set.Iic (n : ℝ)) = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈x⌉₊, Set.mem_Iic.2 (Nat.le_ceil x)⟩
  have := measure_iUnion_null h0
  rw [hU, measure_univ] at this
  exact one_ne_zero this

theorem var_G_decomp [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {T : ℝ} (hT : 0 ≤ T) :
    Var[s.G P T; P] = 2 * (mean Foff / mu Fon Foff) * mean Fon *
      ((mean Foff / mu Fon Foff) * (MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal +
        (mean Fon / mu Fon Foff) * ((E2K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal -
          (E1K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal)) := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  have : IsProbabilityMeasure (eqLaw Foff) := eqLaw_isProb Foff hoff0 hioff hoff
  set ν : ℕ → Measure ℝ := fun j => P.map (psum (srcZ s) j) with hν
  have hp0 : 0 < mean Fon / mu Fon Foff := div_pos hon hmu
  have hq0 : 0 < mean Foff / mu Fon Foff := div_pos hoff hmu
  have hpq : mean Fon / mu Fon Foff + mean Foff / mu Fon Foff = 1 := by
    rw [← add_div]; exact div_self (ne_of_gt hmu)
  have hpqE : ENNReal.ofReal (mean Fon / mu Fon Foff) + ENNReal.ofReal (mean Foff / mu Fon Foff) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le hq0.le, hpq, ENNReal.ofReal_one]
  -- finiteness
  have hRfin : ∀ {T' : ℝ}, 0 ≤ T' → aFGk Fon Foff ν T' ≠ ∞ ∧ aGk Foff ν T' ≠ ∞ := by
    intro T' hT'
    have h := rs_ramp hon0 hoff0 hon hoff hion hioff hs hT'
    have hfin : ENNReal.ofReal (mu Fon Foff)⁻¹ * ENNReal.ofReal (T' ^ 2 / 2) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    rw [← h] at hfin
    have h1 := ENNReal.add_ne_top.1 hfin
    refine ⟨fun h2 => h1.1 ?_, fun h2 => h1.2 ?_⟩
    · rw [h2, ENNReal.mul_top (ENNReal.ofReal_pos.2 hp0).ne']
    · rw [h2, ENNReal.mul_top (ENNReal.ofReal_pos.2 hq0).ne']
  obtain ⟨hFG, hG⟩ := hRfin hT
  obtain ⟨s0, hs0, hpos⟩ := exists_Iic_pos Foff
  have hF : aFk Fon ν T ≠ ∞ := by
    intro htop
    have h := aFk_le Fon Foff ν T s0
    rw [htop, ENNReal.mul_top hpos.ne'] at h
    exact (hRfin (by linarith : 0 ≤ T + s0)).1 (top_le_iff.1 h)
  have hE1 : E1K Fon Foff ν T ≠ ∞ := ne_top_of_le_ne_top hF (E1K_le Fon Foff ν T)
  have hE2 : E2K Fon Foff ν T ≠ ∞ := ne_top_of_le_ne_top hF (E2K_le Fon Foff ν T)
  have hM : MainK Fon Foff ν T ≠ ∞ := ne_top_of_le_ne_top hG (MainK_le Fon Foff ν T)
  -- the AGF term
  have hAGF : ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * Roff Fon Foff ν h =
      ENNReal.ofReal (mean Fon) * aGFk Fon Foff ν T := by
    rw [lintegral_Roff_eq Fon Foff ν (nu_Iio_zero hs hon0 hoff0) T, AGF_eq Fon Foff ν hon T]
  have hGF : aGFk Fon Foff ν T ≠ ∞ := by
    intro htop
    have hle : ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * Roff Fon Foff ν h ≤
        ∫⁻ h in Set.Ioi 0, ENNReal.ofReal (T - h) * ENNReal.ofReal ((mean Fon / mu Fon Foff) / (mean Foff / mu Fon Foff)) := by
      refine setLIntegral_mono ((ENNReal.measurable_ofReal.comp
        (measurable_const.sub measurable_id)).mul_const _) fun h hh => ?_
      gcongr
      exact Roff_le hon0 hoff0 hon hoff hion hioff hs (le_of_lt hh)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ramp hT, hAGF, htop,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hon).ne'] at hle
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (top_le_iff.1 hle)
  -- real identities
  have hV := var_G_formula hon0 hoff0 hon hoff hion hioff hs hT
  rw [← hν, hAGF] at hV
  have hR0 := rs_ramp hon0 hoff0 hon hoff hion hioff hs hT
  rw [← hν] at hR0
  have hR := congrArg ENNReal.toReal hR0
  have hD := congrArg ENNReal.toReal
    (decomp_ident (ν := ν) (T := T) hon0 hoff0 hon hoff hion hioff hpqE)
  have m1 : ∀ {a : ℝ≥0∞} {r : ℝ}, a ≠ ∞ → ENNReal.ofReal r * a ≠ ∞ :=
    fun h => ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_add (m1 hFG) (m1 hG), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le,
    ENNReal.toReal_ofReal (inv_nonneg.2 hmu.le), ENNReal.toReal_ofReal (by positivity)] at hR
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨m1 hFG, m1 hG⟩) (m1 hE1),
    ENNReal.toReal_add (m1 hFG) (m1 hG),
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hGF, m1 hM⟩) (m1 hE2),
    ENNReal.toReal_add hGF (m1 hM)] at hD
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le] at hD
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hon.le] at hV
  simp only [ENNReal.toReal_ofNat] at hV
  rw [hV]
  have hmu' : mu Fon Foff ≠ 0 := ne_of_gt hmu
  linear_combination (2 * (mean Foff / mu Fon Foff) * mean Fon) * hD -
    (2 * (mean Foff / mu Fon Foff) * mean Fon) * hR

end Var7

end NetTraffic.OnOffFBM.Lib

/-! ### C2b step A1: elementary renewal bounds
`H(z) = Σ_n ∫ G(Iio(z-b)) dν_n` satisfies `|H(z) - z/μ| ≤ ε z + C_ε`, from the stationary
renewal identity `Σ_n ∫ R(z-b) dν_n = z/μ`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section RenB

theorem renewal_U_lower (ν : ℕ → Measure ℝ) (R : ℝ → ℝ≥0∞) (hR1 : ∀ z, R z ≤ 1)
    (hR0 : ∀ z, z ≤ 0 → R z = 0) {c : ℝ}
    (hid : ∀ z, 0 ≤ z → ∑' n, ∫⁻ b, R (z - b) ∂(ν n) = ENNReal.ofReal c * ENNReal.ofReal z)
    {z : ℝ} (hz : 0 ≤ z) :
    ENNReal.ofReal c * ENNReal.ofReal z ≤ ∑' n, ν n (Set.Iio z) := by
  rw [← hid z hz]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_indicator_one measurableSet_Iio]
  refine lintegral_mono fun b => ?_
  by_cases hb : b < z
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hb)]; exact hR1 _
  · rw [hR0 _ (by linarith)]; exact zero_le

theorem renewal_U_upper (ν : ℕ → Measure ℝ) (R : ℝ → ℝ≥0∞) (hRm : Monotone R) {c : ℝ}
    (hid : ∀ z, 0 ≤ z → ∑' n, ∫⁻ b, R (z - b) ∂(ν n) = ENNReal.ofReal c * ENNReal.ofReal z)
    {z s : ℝ} (hz : 0 ≤ z) (hs : 0 ≤ s) :
    R s * ∑' n, ν n (Set.Iio z) ≤ ENNReal.ofReal c * ENNReal.ofReal (z + s) := by
  rw [← hid (z + s) (by linarith), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_indicator_const measurableSet_Iio]
  refine lintegral_mono fun b => ?_
  by_cases hb : b < z
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hb)]; exact hRm (by linarith)
  · rw [Set.indicator_of_notMem (by simpa using hb)]; exact zero_le

theorem renewal_H_le_U (ν : ℕ → Measure ℝ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG0 : G (Set.Iio 0) = 0) (z : ℝ) :
    ∑' n, ∫⁻ b, G (Set.Iio (z - b)) ∂(ν n) ≤ ∑' n, ν n (Set.Iio z) := by
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_indicator_one measurableSet_Iio]
  refine lintegral_mono fun b => ?_
  by_cases hb : b < z
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hb)]; exact prob_le_one
  · rw [Set.indicator_of_notMem (by simpa using hb)]
    exact le_of_eq (measure_mono_null (Set.Iio_subset_Iio (by linarith)) hG0)

theorem renewal_H_ge (ν : ℕ → Measure ℝ) (G : Measure ℝ) (z s : ℝ) :
    G (Set.Iio s) * ∑' n, ν n (Set.Iio (z - s)) ≤ ∑' n, ∫⁻ b, G (Set.Iio (z - b)) ∂(ν n) := by
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_indicator_const measurableSet_Iio]
  refine lintegral_mono fun b => ?_
  by_cases hb : b < z - s
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hb)]
    exact measure_mono (Set.Iio_subset_Iio (by linarith))
  · rw [Set.indicator_of_notMem (by simpa using hb)]; exact zero_le

/-- The elementary renewal theorem in sandwich form. -/
theorem renewal_H_bound (ν : ℕ → Measure ℝ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG0 : G (Set.Iio 0) = 0) (R : ℝ → ℝ≥0∞) (hRm : Monotone R) (hR1 : ∀ z, R z ≤ 1)
    (hR0 : ∀ z, z ≤ 0 → R z = 0) {c : ℝ} (hc : 0 < c)
    (hid : ∀ z, 0 ≤ z → ∑' n, ∫⁻ b, R (z - b) ∂(ν n) = ENNReal.ofReal c * ENNReal.ofReal z)
    (hRlim : ∀ δ : ℝ, 0 < δ → ∃ s, 0 ≤ s ∧ ENNReal.ofReal (1 - δ) ≤ R s)
    {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, ∀ z, 0 ≤ z →
      (∑' n, ∫⁻ b, G (Set.Iio (z - b)) ∂(ν n)) ≠ ∞ ∧
      |(∑' n, ∫⁻ b, G (Set.Iio (z - b)) ∂(ν n)).toReal - c * z| ≤ ε * z + C := by
  set δ : ℝ := min (1 / 2) (ε / (2 * c)) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * c) := min_le_right _ _
  have hδc : 2 * c * δ ≤ ε := by
    have := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0:ℝ) ≤ 2 * c)
    rwa [mul_div_cancel₀ _ (by positivity : (2 * c) ≠ 0)] at this
  obtain ⟨s1, hs1, hR⟩ := hRlim δ hδ0
  have hGt : ∀ᶠ s in atTop, ENNReal.ofReal (1 - δ) < G (Set.Iic s) := by
    have h := tendsto_measure_Iic_atTop G
    rw [measure_univ] at h
    exact h.eventually_const_lt (ENNReal.ofReal_lt_one.2 (by linarith))
  obtain ⟨s2, hs2⟩ := (hGt.and (eventually_ge_atTop 0)).exists
  set s : ℝ := max s1 (s2 + 1) with hsdef
  have hs0 : 0 ≤ s := le_trans hs1 (le_max_left _ _)
  have hRs : ENNReal.ofReal (1 - δ) ≤ R s := hR.trans (hRm (le_max_left _ _))
  have hGs : ENNReal.ofReal (1 - δ) ≤ G (Set.Iio s) :=
    hs2.1.le.trans (measure_mono (Set.Iic_subset_Iio.2 (by
      have := le_max_right s1 (s2 + 1); linarith)))
  refine ⟨2 * c * s, fun z hz => ?_⟩
  set H := ∑' n, ∫⁻ b, G (Set.Iio (z - b)) ∂(ν n) with hH
  have h1δ : 0 < 1 - δ := by linarith
  -- upper bound
  have hU := renewal_U_upper ν R hRm hid hz hs0
  have hU' : ENNReal.ofReal (1 - δ) * ∑' n, ν n (Set.Iio z) ≤
      ENNReal.ofReal (c * (z + s)) := by
    rw [ENNReal.ofReal_mul hc.le]
    exact (by gcongr : ENNReal.ofReal (1 - δ) * ∑' n, ν n (Set.Iio z) ≤ R s * ∑' n, ν n (Set.Iio z)).trans hU
  have hUle : ∑' n, ν n (Set.Iio z) ≤ ENNReal.ofReal (c * (z + s) / (1 - δ)) := by
    rw [ENNReal.ofReal_div_of_pos h1δ, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.2 h1δ).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hU'
  have hHle := (renewal_H_le_U ν G hG0 z).trans hUle
  have hHfin : H ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHle
  refine ⟨hHfin, ?_⟩
  have hup : H.toReal ≤ c * (z + s) / (1 - δ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hHle
  have hup2 : c * (z + s) / (1 - δ) ≤ c * (z + s) * (1 + 2 * δ) := by
    rw [div_le_iff₀ h1δ]
    have h0 : 0 ≤ c * (z + s) := by positivity
    have k : 0 ≤ δ * (1 - 2 * δ) := mul_nonneg hδ0.le (by linarith)
    nlinarith [mul_nonneg h0 k]
  -- lower bound
  have hlow : (1 - δ) * (c * (z - s)) ≤ H.toReal := by
    by_cases hzs : s ≤ z
    · have hL := renewal_U_lower ν R hR1 hR0 hid (by linarith : 0 ≤ z - s)
      have hHg := renewal_H_ge ν G z s
      have h2 : ENNReal.ofReal ((1 - δ) * (c * (z - s))) ≤ H := by
        rw [ENNReal.ofReal_mul h1δ.le, ENNReal.ofReal_mul hc.le]
        exact (mul_le_mul' hGs hL).trans hHg
      exact (ENNReal.ofReal_le_iff_le_toReal hHfin).1 h2
    · have : (1 - δ) * (c * (z - s)) ≤ 0 := by
        have : c * (z - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)
        nlinarith
      exact this.trans ENNReal.toReal_nonneg
  have hcs : 0 ≤ c * s := by positivity
  have hcz : 0 ≤ c * z := by positivity
  have e1 : c * (z + s) * (1 + 2 * δ) = c * z + (2 * c * δ) * z + c * s * (1 + 2 * δ) := by ring
  have e2 : (1 - δ) * (c * (z - s)) = c * z - (2 * c * δ) * z / 2 - (1 - δ) * (c * s) := by ring
  have k1 : (2 * c * δ) * z ≤ ε * z := mul_le_mul_of_nonneg_right hδc hz
  have k2 : c * s * (1 + 2 * δ) ≤ 2 * c * s := by nlinarith
  have k3 : (1 - δ) * (c * s) ≤ 2 * c * s := by nlinarith
  have k4 : 0 ≤ (2 * c * δ) * z := by positivity
  rw [abs_le]
  constructor <;> linarith

noncomputable def Rk (Fon Foff : Measure ℝ) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (mean Fon / mu Fon Foff) *
      ∫⁻ w, (∫⁻ x, (Set.Iio z).indicator 1 (w + x) ∂(eqLaw Fon)) ∂Foff +
    ENNReal.ofReal (mean Foff / mu Fon Foff) * eqLaw Foff (Set.Iio z)

theorem Rk_mono (Fon Foff : Measure ℝ) : Monotone (Rk Fon Foff) := by
  intro z z' h
  unfold Rk
  refine add_le_add (mul_le_mul_right (lintegral_mono fun w => lintegral_mono fun x => ?_) _)
    (mul_le_mul_right (measure_mono (Set.Iio_subset_Iio h)) _)
  exact Set.indicator_le_indicator_of_subset (Set.Iio_subset_Iio h) (fun _ => zero_le) _

theorem ind_le_one (z t : ℝ) : (Set.Iio z).indicator (1 : ℝ → ℝ≥0∞) t ≤ 1 := by
  by_cases h : t ∈ Set.Iio z
  · rw [Set.indicator_of_mem h]; rfl
  · rw [Set.indicator_of_notMem h]; exact zero_le

theorem Rk_le_one {Fon Foff : Measure ℝ} [IsProbabilityMeasure Foff]
    [IsProbabilityMeasure (eqLaw Fon)] [IsProbabilityMeasure (eqLaw Foff)]
    (hpq : ENNReal.ofReal (mean Fon / mu Fon Foff) + ENNReal.ofReal (mean Foff / mu Fon Foff) = 1)
    (z : ℝ) : Rk Fon Foff z ≤ 1 := by
  unfold Rk
  calc _ ≤ ENNReal.ofReal (mean Fon / mu Fon Foff) * 1 +
        ENNReal.ofReal (mean Foff / mu Fon Foff) * 1 := by
        refine add_le_add (mul_le_mul_right ?_ _) (mul_le_mul_right prob_le_one _)
        calc ∫⁻ w, (∫⁻ x, (Set.Iio z).indicator 1 (w + x) ∂(eqLaw Fon)) ∂Foff
            ≤ ∫⁻ _w, (∫⁻ _x, (1 : ℝ≥0∞) ∂(eqLaw Fon)) ∂Foff :=
              lintegral_mono fun w => lintegral_mono fun x => ind_le_one z _
          _ = 1 := by simp
    _ = 1 := by rw [mul_one, mul_one, hpq]

theorem Rk_nonpos {Fon Foff : Measure ℝ} (hoff0 : Foff (Set.Iio 0) = 0) {z : ℝ} (hz : z ≤ 0) :
    Rk Fon Foff z = 0 := by
  unfold Rk
  have h1 : ∫⁻ w, (∫⁻ x, (Set.Iio z).indicator 1 (w + x) ∂(eqLaw Fon)) ∂Foff = 0 := by
    rw [← lintegral_zero (μ := Foff)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio Foff hoff0] with w hw
    rw [← lintegral_zero (μ := eqLaw Fon)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio (eqLaw Fon) (eqLaw_Iio_zero Fon)] with x hx
    rw [Set.indicator_of_notMem (by simp only [Set.mem_Iio, not_lt]; linarith)]
  have h2 : eqLaw Foff (Set.Iio z) = 0 :=
    measure_mono_null (Set.Iio_subset_Iio hz) (eqLaw_Iio_zero Foff)
  rw [h1, h2, mul_zero, mul_zero, add_zero]

theorem Rk_lower {Fon Foff : Measure ℝ} {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal (mean Fon / mu Fon Foff) * (eqLaw Fon (Set.Iic (z / 3)) * Foff (Set.Iic (z / 3))) +
      ENNReal.ofReal (mean Foff / mu Fon Foff) * eqLaw Foff (Set.Iic (z / 3)) ≤ Rk Fon Foff z := by
  unfold Rk
  refine add_le_add (mul_le_mul_right ?_ _)
    (mul_le_mul_right (measure_mono (Set.Iic_subset_Iio.2 (by linarith))) _)
  rw [← lintegral_indicator_const measurableSet_Iic]
  refine lintegral_mono fun w => ?_
  by_cases hw : w ∈ Set.Iic (z / 3)
  · rw [Set.indicator_of_mem hw, ← lintegral_indicator_one measurableSet_Iic]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Set.Iic (z / 3)
    · have h1 : w ≤ z / 3 := hw
      have h2 : x ≤ z / 3 := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show w + x ∈ Set.Iio z by
        rw [Set.mem_Iio]; linarith)]
      rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  · rw [Set.indicator_of_notMem hw]; exact zero_le

theorem Rk_lim {Fon Foff : Measure ℝ} [IsProbabilityMeasure Foff]
    [IsProbabilityMeasure (eqLaw Fon)] [IsProbabilityMeasure (eqLaw Foff)]
    (hpq : ENNReal.ofReal (mean Fon / mu Fon Foff) + ENNReal.ofReal (mean Foff / mu Fon Foff) = 1)
    {δ : ℝ} (hδ : 0 < δ) : ∃ s, 0 ≤ s ∧ ENNReal.ofReal (1 - δ) ≤ Rk Fon Foff s := by
  have hdiv : Tendsto (fun z : ℝ => z / 3) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have t1 := (tendsto_measure_Iic_atTop (eqLaw Fon)).comp hdiv
  have t2 := (tendsto_measure_Iic_atTop Foff).comp hdiv
  have t3 := (tendsto_measure_Iic_atTop (eqLaw Foff)).comp hdiv
  rw [measure_univ] at t1 t2 t3
  have t12 := ENNReal.Tendsto.mul t1 (Or.inr ENNReal.one_ne_top) t2 (Or.inr ENNReal.one_ne_top)
  have tl := (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (mean Fon / mu Fon Foff)) t12
    (Or.inr ENNReal.ofReal_ne_top)).add
    (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (mean Foff / mu Fon Foff)) t3
      (Or.inr ENNReal.ofReal_ne_top))
  rw [mul_one, mul_one, mul_one, hpq] at tl
  obtain ⟨z, hz1, hz2⟩ := ((tl.eventually_const_lt (ENNReal.ofReal_lt_one.2 (by linarith :
    1 - δ < 1))).and (eventually_gt_atTop (0:ℝ))).exists
  exact ⟨z, hz2.le, hz1.le.trans (Rk_lower hz2)⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem Rk_renewal [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {z : ℝ} (hz : 0 ≤ z) :
    ∑' n, ∫⁻ b, Rk Fon Foff (z - b) ∂(P.map (psum (srcZ s) n)) =
      ENNReal.ofReal (mu Fon Foff)⁻¹ * ENNReal.ofReal z := by
  have hf : Measurable ((Set.Iio z).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_Iio
  have h := renewal_split hon0 hoff0 hon hoff hion hioff hs _ hf
  have hshift : ∀ t b : ℝ, (Set.Iio z).indicator (1 : ℝ → ℝ≥0∞) (t + b) =
      (Set.Iio (z - b)).indicator 1 t := by
    intro t b
    simp only [Set.indicator_apply, Set.mem_Iio, lt_sub_iff_add_lt, Pi.one_apply]
  have hR : ∀ b, ENNReal.ofReal (mean Fon / mu Fon Foff) *
        ∫⁻ w, (∫⁻ x, (Set.Iio z).indicator 1 (w + x + b) ∂(eqLaw Fon)) ∂Foff +
      ENNReal.ofReal (mean Foff / mu Fon Foff) *
        ∫⁻ y, (Set.Iio z).indicator 1 (y + b) ∂(eqLaw Foff) = Rk Fon Foff (z - b) := by
    intro b
    unfold Rk
    simp_rw [hshift]
    rw [lintegral_indicator_one measurableSet_Iio]
  simp_rw [hR] at h
  rw [h, lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
    Set.Iio_inter_Ioi, Real.volume_Ioo, sub_zero]

theorem H_bound [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ z, 0 ≤ z →
      (∑' n, ∫⁻ b, eqLaw Foff (Set.Iio (z - b)) ∂(P.map (psum (srcZ s) n))) ≠ ∞ ∧
      |(∑' n, ∫⁻ b, eqLaw Foff (Set.Iio (z - b)) ∂(P.map (psum (srcZ s) n))).toReal -
        (mu Fon Foff)⁻¹ * z| ≤ ε * z + C := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  have : IsProbabilityMeasure (eqLaw Foff) := eqLaw_isProb Foff hoff0 hioff hoff
  have hp0 : 0 < mean Fon / mu Fon Foff := div_pos hon hmu
  have hq0 : 0 < mean Foff / mu Fon Foff := div_pos hoff hmu
  have hpqE : ENNReal.ofReal (mean Fon / mu Fon Foff) +
      ENNReal.ofReal (mean Foff / mu Fon Foff) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le hq0.le, ← add_div,
      show mean Fon + mean Foff = mu Fon Foff from rfl, div_self (ne_of_gt hmu), ENNReal.ofReal_one]
  exact renewal_H_bound _ (eqLaw Foff) (eqLaw_Iio_zero Foff) (Rk Fon Foff) (Rk_mono Fon Foff)
    (Rk_le_one hpqE) (fun z hz => Rk_nonpos hoff0 hz) (inv_pos.2 hmu)
    (fun z hz => Rk_renewal hon0 hoff0 hon hoff hion hioff hs hz) (fun δ hδ => Rk_lim hpqE hδ) hε

end RenB

end NetTraffic.OnOffFBM.Lib

/-! ### C2b: MainK through the renewal function `H`
`MainK(T) = ∫_{u>0} F̄0(u) H(T-u) du`, `H(z) = Σ_n ∫ G0(Iio(z-b)) dν_n`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section MainRep

theorem ofReal_min_eq (x t : ℝ) :
    ENNReal.ofReal (min x t) = ∫⁻ u in Set.Ioi 0, (Set.Iio (min x t)).indicator 1 u := by
  rw [lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
    Set.Iio_inter_Ioi, Real.volume_Ioo, sub_zero]

theorem Phi_rep (F : Measure ℝ) [SFinite F] (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (min x t) ∂F =
      ∫⁻ u in Set.Ioi 0, (Set.Iio t).indicator (fun u => F (Set.Ioi u)) u := by
  simp_rw [ofReal_min_eq]
  have hs : MeasurableSet {p : ℝ × ℝ | p.2 < min p.1 t} :=
    measurableSet_lt measurable_snd (measurable_fst.min measurable_const)
  have e : (Function.uncurry fun (x u : ℝ) => (Set.Iio (min x t)).indicator (1 : ℝ → ℝ≥0∞) u) =
      {p : ℝ × ℝ | p.2 < min p.1 t}.indicator 1 := by
    funext p
    simp only [Function.uncurry, Set.indicator_apply, Set.mem_Iio, Set.mem_setOf_eq, Pi.one_apply]
  have hm : Measurable (Function.uncurry fun (x u : ℝ) =>
      (Set.Iio (min x t)).indicator (1 : ℝ → ℝ≥0∞) u) := by
    rw [e]; exact measurable_const.indicator hs
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine lintegral_congr fun u => ?_
  by_cases hu : u < t
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hu), ← lintegral_indicator_one measurableSet_Ioi]
    refine lintegral_congr fun x => ?_
    simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi, lt_min_iff, hu, and_true,
      Pi.one_apply]
  · rw [Set.indicator_of_notMem (by simpa using hu), ← lintegral_zero (μ := F)]
    refine lintegral_congr fun x => ?_
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_Iio, not_lt]
    exact le_trans (min_le_right x t) (not_lt.1 hu)

theorem Iio_measure_measurable (G : Measure ℝ) : Measurable fun z : ℝ => G (Set.Iio z) :=
  (show Monotone fun z : ℝ => G (Set.Iio z) from
    fun _ _ h => measure_mono (Set.Iio_subset_Iio h)).measurable

theorem Ioi_measure_measurable (G : Measure ℝ) : Measurable fun z : ℝ => G (Set.Ioi z) :=
  (show Antitone fun z : ℝ => G (Set.Ioi z) from
    fun _ _ h => measure_mono (Set.Ioi_subset_Ioi h)).measurable

theorem MainK_rep (Fon Foff : Measure ℝ) [SFinite (eqLaw Fon)] [SFinite (eqLaw Foff)]
    (ν : ℕ → Measure ℝ) [∀ n, SFinite (ν n)] (T : ℝ) :
    MainK Fon Foff ν T = ∫⁻ u in Set.Ioi 0, eqLaw Fon (Set.Ioi u) *
      ∑' n, ∫⁻ b, eqLaw Foff (Set.Iio (T - u - b)) ∂(ν n) := by
  have hF := Ioi_measure_measurable (eqLaw Fon)
  have hG := Iio_measure_measurable (eqLaw Foff)
  -- joint measurability of `(b, u) ↦ G0(Iio(T-u-b))`
  have hGbu : Measurable fun p : ℝ × ℝ => eqLaw Foff (Set.Iio (T - p.2 - p.1)) :=
    hG.comp ((measurable_const.sub measurable_snd).sub measurable_fst)
  have hGub : Measurable fun p : ℝ × ℝ => eqLaw Foff (Set.Iio (T - p.1 - p.2)) :=
    hG.comp ((measurable_const.sub measurable_fst).sub measurable_snd)
  unfold MainK
  simp_rw [Phi_rep]
  have key : ∀ n, ∫⁻ b, (∫⁻ y, (∫⁻ u in Set.Ioi 0,
      (Set.Iio (T - (y + b))).indicator (fun u => eqLaw Fon (Set.Ioi u)) u) ∂(eqLaw Foff)) ∂(ν n) =
      ∫⁻ u in Set.Ioi 0, eqLaw Fon (Set.Ioi u) * ∫⁻ b, eqLaw Foff (Set.Iio (T - u - b)) ∂(ν n) := by
    intro n
    have step1 : ∀ b, ∫⁻ y, (∫⁻ u in Set.Ioi 0,
        (Set.Iio (T - (y + b))).indicator (fun u => eqLaw Fon (Set.Ioi u)) u) ∂(eqLaw Foff) =
        ∫⁻ u in Set.Ioi 0, eqLaw Fon (Set.Ioi u) * eqLaw Foff (Set.Iio (T - u - b)) := by
      intro b
      have hs : MeasurableSet {p : ℝ × ℝ | p.2 < T - (p.1 + b)} :=
        measurableSet_lt measurable_snd (measurable_const.sub (measurable_fst.add measurable_const))
      have e : (Function.uncurry fun (y u : ℝ) =>
          (Set.Iio (T - (y + b))).indicator (fun u => eqLaw Fon (Set.Ioi u)) u) =
          {p : ℝ × ℝ | p.2 < T - (p.1 + b)}.indicator (fun p => eqLaw Fon (Set.Ioi p.2)) := by
        funext p
        simp only [Function.uncurry, Set.indicator_apply, Set.mem_Iio, Set.mem_setOf_eq]
      have hm : Measurable (Function.uncurry fun (y u : ℝ) =>
          (Set.Iio (T - (y + b))).indicator (fun u => eqLaw Fon (Set.Ioi u)) u) := by
        rw [e]; exact (hF.comp measurable_snd).indicator hs
      rw [lintegral_lintegral_swap hm.aemeasurable]
      refine lintegral_congr fun u => ?_
      have e2 : (fun y => (Set.Iio (T - (y + b))).indicator (fun u => eqLaw Fon (Set.Ioi u)) u) =
          (Set.Iio (T - u - b)).indicator (fun _ => eqLaw Fon (Set.Ioi u)) := by
        funext y
        simp only [Set.indicator_apply, Set.mem_Iio]
        congr 1
        exact propext ⟨fun h => by linarith, fun h => by linarith⟩
      rw [e2, lintegral_indicator_const measurableSet_Iio]
    simp_rw [step1]
    have hm2 : Measurable (Function.uncurry fun (b u : ℝ) =>
        eqLaw Fon (Set.Ioi u) * eqLaw Foff (Set.Iio (T - u - b))) :=
      (hF.comp measurable_snd).mul hGbu
    rw [lintegral_lintegral_swap hm2.aemeasurable]
    refine lintegral_congr fun u => ?_
    exact lintegral_const_mul _ (hG.comp ((measurable_const.sub measurable_const).sub measurable_id))
  simp_rw [key]
  rw [← lintegral_tsum]
  · refine lintegral_congr fun u => ?_
    rw [ENNReal.tsum_mul_left]
  · intro n
    exact (hF.mul (hGub.lintegral_prod_right' (ν := ν n))).aemeasurable

end MainRep

end NetTraffic.OnOffFBM.Lib

/-! ### C2b step A4: Karamata applied to the ON tail
`∫_0^T tailI(u) (T-u) du ~ T^{3-α} L(T) / ((α-1)(2-α)(3-α))`, `tailI u = ∫_u^∞ F̄`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section KarApp

theorem Fbar_antitone (F : Measure ℝ) [IsFiniteMeasure F] : Antitone (Fbar F) :=
  fun _ _ h => measureReal_mono (Set.Ioi_subset_Ioi h)

theorem Fbar_nonneg (F : Measure ℝ) (x : ℝ) : 0 ≤ Fbar F x := measureReal_nonneg

theorem Fbar_pos_of_sv {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ}
    (hsv : IsSlowlyVarying (Lsv F a)) (x : ℝ) : 0 < Fbar F x := by
  obtain ⟨y, hy⟩ := (hsv.1.and (eventually_ge_atTop (max x 1))).exists
  have hy0 : 0 < y := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hy.2)
  have h1 : 0 < Fbar F y := by
    have := hy.1
    unfold Lsv at this
    exact pos_of_mul_pos_right this (Real.rpow_nonneg hy0.le _)
  exact lt_of_lt_of_le h1 (Fbar_antitone F (le_trans (le_max_left _ _) hy.2))

theorem Fbar_rv {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ}
    (hsv : IsSlowlyVarying (Lsv F a)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => Fbar F (c * x) / Fbar F x) atTop (𝓝 (c ^ (-a))) := by
  have h := (hsv.2 c hc).const_mul (c ^ (-a))
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  unfold Lsv
  have hF := Fbar_pos_of_sv hsv x
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx a
  have hca : 0 < c ^ a := Real.rpow_pos_of_pos hc a
  rw [Real.mul_rpow hc.le hx.le, Real.rpow_neg hc.le]
  field_simp

noncomputable def tailI (F : Measure ℝ) (u : ℝ) : ℝ := ∫ v in Set.Ioi (max u 0), Fbar F v

theorem Fbar_integrableOn {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (Fbar F) (Set.Ioi u) := by
  have h : IntegrableOn (Fbar F) (Set.Ioi 0) := by
    refine ⟨(Fbar_measurable F).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Fbar_nonneg F x),
      lintegral_Fbar_eq_mean F h0 hi]
    exact ENNReal.ofReal_lt_top
  exact h.mono_set (Set.Ioi_subset_Ioi hu)

theorem tailI_antitone {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) : Antitone (tailI F) := by
  intro u u' huu
  unfold tailI
  refine setIntegral_mono_set (Fbar_integrableOn h0 hi (le_max_right u 0))
    (Eventually.of_forall fun x => Fbar_nonneg F x) ?_
  exact Eventually.of_forall (Set.Ioi_subset_Ioi (max_le_max huu le_rfl))

theorem tailI_pos {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (hsv : IsSlowlyVarying (Lsv F a)) (u : ℝ) :
    0 < tailI F u := by
  set m := max u 0
  have hm : 0 ≤ m := le_max_right u 0
  have hsub : Set.Ioc m (m + 1) ⊆ Set.Ioi m := Set.Ioc_subset_Ioi_self
  have h1 : ∫ v in Set.Ioc m (m + 1), Fbar F v ≤ tailI F u :=
    setIntegral_mono_set (Fbar_integrableOn h0 hi hm)
      (Eventually.of_forall fun x => Fbar_nonneg F x) (Eventually.of_forall hsub)
  have h2 : volume.real (Set.Ioc m (m + 1)) • Fbar F (m + 1) ≤
      ∫ v in Set.Ioc m (m + 1), Fbar F v :=
    setIntegral_ge_of_const_le measurableSet_Ioc (by simp)
      (fun x hx => Fbar_antitone F hx.2) ((Fbar_integrableOn h0 hi hm).mono_set hsub)
  have h3 : volume.real (Set.Ioc m (m + 1)) = 1 := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; ring
  rw [h3, one_smul] at h2
  linarith [Fbar_pos_of_sv hsv (m + 1)]

theorem tailI_ratio {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (ha : 1 < a)
    (hsv : IsSlowlyVarying (Lsv F a)) :
    Tendsto (fun x => tailI F x / (x * Fbar F x)) atTop (𝓝 (1 / (a - 1))) := by
  have h := karamata_tail (Fbar_antitone F) (Fbar_pos_of_sv hsv) ha fun c hc => Fbar_rv hsv hc
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  unfold tailI
  rw [max_eq_left hx]

theorem tailI_rv {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (ha : 1 < a)
    (hsv : IsSlowlyVarying (Lsv F a)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => tailI F (c * x) / tailI F x) atTop (𝓝 (c ^ (-(a - 1)))) := by
  have hK := tailI_ratio ha hsv
  have hKc := hK.comp (tendsto_id.const_mul_atTop hc)
  have hk0 : (1 / (a - 1)) ≠ 0 := by
    have : 0 < a - 1 := by linarith
    positivity
  have hlim := ((hKc.div hK hk0).mul_const c).mul (Fbar_rv hsv hc)
  rw [div_self hk0, one_mul] at hlim
  have hval : c * c ^ (-a) = c ^ (-(a - 1)) := by
    rw [show -(a - 1) = 1 + -a by ring, Real.rpow_add hc, Real.rpow_one]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Pi.div_apply, Function.comp_apply, id]
  have hI := tailI_pos h0 hi hsv x
  have hIc := tailI_pos h0 hi hsv (c * x)
  have hF := Fbar_pos_of_sv hsv x
  have hFc := Fbar_pos_of_sv hsv (c * x)
  have hcx : 0 < c * x := mul_pos hc hx
  field_simp
  try ring

theorem tailI_head {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (ha : 1 < a) (ha2 : a < 2)
    (hsv : IsSlowlyVarying (Lsv F a)) :
    Tendsto (fun T => (∫ u in (0:ℝ)..T, tailI F u * (T - u)) / (T ^ (3 - a) * Lsv F a T)) atTop
      (𝓝 (1 / ((a - 1) * (2 - a) * (3 - a)))) := by
  have hH := karamata_head (tailI_antitone h0 hi) (tailI_pos h0 hi hsv) (by linarith : 0 < a - 1)
    (by linarith : a - 1 < 1) fun c hc => tailI_rv h0 hi ha hsv hc
  rw [integral_kernel (by linarith) (by linarith)] at hH
  have hlim := hH.mul (tailI_ratio ha hsv)
  have hval : 1 / ((1 - (a - 1)) * (2 - (a - 1))) * (1 / (a - 1)) =
      1 / ((a - 1) * (2 - a) * (3 - a)) := by
    have h1 : (a - 1) ≠ 0 := by linarith
    have h2 : (2 - a) ≠ 0 := by linarith
    have h3 : (3 - a) ≠ 0 := by linarith
    rw [show 1 - (a - 1) = 2 - a by ring, show 2 - (a - 1) = 3 - a by ring]
    field_simp
    try ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hF := Fbar_pos_of_sv hsv T
  have hI := tailI_pos h0 hi hsv T
  have hT3 : T ^ (3 - a) * Lsv F a T = T ^ 3 * Fbar F T := by
    unfold Lsv
    rw [← mul_assoc, ← Real.rpow_add hT, show 3 - a + a = (3:ℝ) by ring]
    norm_cast
  rw [hT3]
  field_simp
  try ring

end KarApp

end NetTraffic.OnOffFBM.Lib

end F05Part3

-- ==== part Asym_part.lean ====
section F05Part4

/-! ### C2b asymptotics: `MainK ~ IPhi/(μ μ_on)`, error terms `o(N)`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Asym

theorem mean_nonneg_of {F : Measure ℝ} (h0 : F (Set.Iio 0) = 0) : 0 ≤ mean F :=
  integral_nonneg_of_ae (ae_nonneg_of_Iio F h0)

theorem tailI_nonneg (F : Measure ℝ) (u : ℝ) : 0 ≤ tailI F u :=
  setIntegral_nonneg measurableSet_Ioi fun x _ => Fbar_nonneg F x

theorem tailI_zero {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) : tailI F 0 = mean F := by
  have h := lintegral_Fbar_eq_mean F h0 hi
  rw [← ofReal_integral_eq_lintegral_ofReal (Fbar_integrableOn h0 hi le_rfl)
    (Eventually.of_forall fun x => Fbar_nonneg F x)] at h
  have h2 := (ENNReal.ofReal_eq_ofReal_iff (tailI_nonneg F 0) (mean_nonneg_of h0)).1
    (by unfold tailI; rw [max_self]; exact h)
  exact h2

theorem tailI_le_mean {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (u : ℝ) : tailI F u ≤ mean F := by
  have e : tailI F u = tailI F (max u 0) := by
    unfold tailI; rw [max_eq_left (le_max_right u 0)]
  rw [e, ← tailI_zero h0 hi]
  exact tailI_antitone h0 hi (le_max_right u 0)

theorem eqLaw_Ioi_tailI {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) {u : ℝ} (hu : 0 ≤ u) :
    eqLaw F (Set.Ioi u) = ENNReal.ofReal (tailI F u / mean F) := by
  rw [eqLaw_Ioi F hu, tailI, max_eq_left hu, ← integral_div,
    ofReal_integral_eq_lintegral_ofReal ((Fbar_integrableOn h0 hi hu).div_const _)
      (Eventually.of_forall fun x => div_nonneg (Fbar_nonneg F x) (mean_nonneg_of h0))]

/-- Generic Abelian sandwich: an `ε`-relative, `O(T)`-absolute perturbation of `b` has the same
normalised limit when `T/N → 0`. -/
theorem tendsto_of_sandwich {a b N : ℝ → ℝ} {k : ℝ}
    (hb : Tendsto (fun T => b T / N T) atTop (𝓝 k))
    (hT : Tendsto (fun T => T / N T) atTop (𝓝 0))
    (hN : ∀ᶠ T in atTop, 0 < N T)
    (hab : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ T in atTop, |a T - b T| ≤ ε * |b T| + C * T) :
    Tendsto (fun T => a T / N T) atTop (𝓝 k) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hk1 : 0 < |k| + 1 := by positivity
  set ε : ℝ := δ / (3 * (|k| + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨C, hC⟩ := hab ε hε
  have h1 := Metric.tendsto_nhds.1 hb (min (δ / 3) 1) (by positivity)
  have hT' := hT.const_mul (|C|)
  rw [mul_zero] at hT'
  have h2 := Metric.tendsto_nhds.1 hT' (δ / 3) (by positivity)
  filter_upwards [h1, h2, hC, hN, eventually_ge_atTop 0] with T h1 h2 hC hN hT0
  rw [Real.dist_eq] at h1 h2 ⊢
  rw [sub_zero] at h2
  have hbk1 : |b T / N T - k| < δ / 3 := lt_of_lt_of_le h1 (min_le_left _ _)
  have hbk2 : |b T / N T - k| < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
  have hbN : |b T / N T| ≤ |k| + 1 := by
    have := abs_sub_abs_le_abs_sub (b T / N T) k
    linarith
  have e1 : |a T / N T - b T / N T| = |a T - b T| / N T := by
    rw [← sub_div, abs_div, abs_of_pos hN]
  have hCT : C * T ≤ |C| * T := mul_le_mul_of_nonneg_right (le_abs_self C) hT0
  have e2 : |a T - b T| / N T ≤ ε * |b T / N T| + |C| * (T / N T) := by
    rw [div_le_iff₀ hN, abs_div, abs_of_pos hN]
    have : (ε * (|b T| / N T) + |C| * (T / N T)) * N T = ε * |b T| + |C| * T := by
      field_simp
    rw [this]; linarith
  have e3 : ε * |b T / N T| ≤ δ / 3 := by
    calc ε * |b T / N T| ≤ ε * (|k| + 1) := mul_le_mul_of_nonneg_left hbN hε.le
      _ = δ / 3 := by rw [hεdef]; field_simp
  have e4 : |C| * (T / N T) < δ / 3 := lt_of_le_of_lt (le_abs_self _) h2
  have := abs_sub_le (a T / N T) (b T / N T) k
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem U_nonpos [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    {z : ℝ} (hz : z ≤ 0) :
    ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio z) = 0 :=
  ENNReal.tsum_eq_zero.2 fun n =>
    measure_mono_null (Set.Iio_subset_Iio hz) (nu_Iio_zero hs hon0 hoff0 n)

theorem U_bound [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    ∃ c s0 : ℝ, 0 ≤ c ∧ 0 ≤ s0 ∧ ∀ z, 0 ≤ z →
      ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio z) ≤ ENNReal.ofReal (c * (z + s0)) := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  have : IsProbabilityMeasure (eqLaw Foff) := eqLaw_isProb Foff hoff0 hioff hoff
  have hp0 : 0 < mean Fon / mu Fon Foff := div_pos hon hmu
  have hq0 : 0 < mean Foff / mu Fon Foff := div_pos hoff hmu
  have hpqE : ENNReal.ofReal (mean Fon / mu Fon Foff) +
      ENNReal.ofReal (mean Foff / mu Fon Foff) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le hq0.le, ← add_div,
      show mean Fon + mean Foff = mu Fon Foff from rfl, div_self (ne_of_gt hmu), ENNReal.ofReal_one]
  obtain ⟨s0, hs0, hR⟩ := Rk_lim hpqE (by norm_num : (0:ℝ) < 1 / 2)
  have hc0 : 0 ≤ 2 * (mu Fon Foff)⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.2 hmu.le)
  refine ⟨2 * (mu Fon Foff)⁻¹, s0, hc0, hs0, fun z hz => ?_⟩
  have h := renewal_U_upper _ (Rk Fon Foff) (Rk_mono Fon Foff)
    (fun z hz => Rk_renewal hon0 hoff0 hon hoff hion hioff hs hz) hz hs0
  have hR' : ENNReal.ofReal (1 / 2) ≤ Rk Fon Foff s0 := by
    have : (1:ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [this] at hR; exact hR
  set U := ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio z)
  calc U = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) * U) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ ≤ ENNReal.ofReal 2 * (Rk Fon Foff s0 * U) := by gcongr
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (mu Fon Foff)⁻¹ * ENNReal.ofReal (z + s0)) := by gcongr
    _ = ENNReal.ofReal (2 * (mu Fon Foff)⁻¹ * (z + s0)) := by
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul (by norm_num), mul_assoc]

theorem ofReal_integral_le_lint {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : Integrable g μ) : ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans ENNReal.ofReal_toReal_le

theorem MainK_sandwich [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T, 0 ≤ T →
      MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T ≠ ∞ ∧
      |(MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal -
          (∫ u in (0:ℝ)..T, tailI Fon u * (T - u)) / (mu Fon Foff * mean Fon)| ≤
        ε * ((∫ u in (0:ℝ)..T, tailI Fon u * (T - u)) / mean Fon) + C * T := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  have : IsProbabilityMeasure (eqLaw Foff) := eqLaw_isProb Foff hoff0 hioff hoff
  obtain ⟨C0, hC0⟩ := H_bound hon0 hoff0 hon hoff hion hioff hs hε
  set C1 := max C0 0 with hC1def
  have hC1 : 0 ≤ C1 := le_max_right _ _
  have hC01 : C0 ≤ C1 := le_max_left _ _
  refine ⟨C1, hC1, fun T hT => ?_⟩
  set m := mean Fon with hm
  set μ := mu Fon Foff with hμ
  set H : ℝ → ℝ≥0∞ := fun z => ∑' n, ∫⁻ b, eqLaw Foff (Set.Iio (z - b)) ∂(P.map (psum (srcZ s) n))
    with hHdef
  set f : ℝ → ℝ := fun u => tailI Fon u / m with hfdef
  have hf0 : ∀ u, 0 ≤ f u := fun u => div_nonneg (tailI_nonneg Fon u) hon.le
  have hf1 : ∀ u, f u ≤ 1 := fun u => div_le_one_of_le₀ (tailI_le_mean hon0 hion u) hon.le
  have hrep : MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T =
      ∫⁻ u in Set.Ioi 0, eqLaw Fon (Set.Ioi u) * H (T - u) := MainK_rep Fon Foff _ T
  have hHnn : ∀ z, z ≤ 0 → H z = 0 := fun z hz =>
    le_antisymm ((renewal_H_le_U _ (eqLaw Foff) (eqLaw_Iio_zero Foff) z).trans
      (le_of_eq (U_nonpos hs hon0 hoff0 hz))) zero_le
  have hti : ∀ a c : ℝ, IntervalIntegrable (tailI Fon) volume a c :=
    fun a c => (tailI_antitone hon0 hion).intervalIntegrable
  have hfi : IntervalIntegrable f volume 0 T := (hti 0 T).div_const _
  have hgi : ∀ (c d : ℝ), IntervalIntegrable (fun u => f u * (c * (T - u) + d)) volume 0 T :=
    fun c d => hfi.mul_continuousOn (by fun_prop)
  have hAi : IntervalIntegrable (fun u => tailI Fon u * (T - u)) volume 0 T :=
    (hti 0 T).mul_continuousOn (by fun_prop)
  set A := ∫ u in (0:ℝ)..T, tailI Fon u * (T - u) with hAdef
  set B := ∫ u in (0:ℝ)..T, f u with hBdef
  have hint : ∀ c d : ℝ, ∫ u in (0:ℝ)..T, f u * (c * (T - u) + d) = c / m * A + d * B := by
    intro c d
    rw [hAdef, hBdef, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hAi.const_mul _) (hfi.const_mul _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [hfdef]
    ring
  have hBT : B ≤ T := by
    have := intervalIntegral.integral_mono_on hT hfi intervalIntegrable_const fun u _ => hf1 u
    simpa using this
  -- upper bound
  have hup : MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T ≤
      ENNReal.ofReal (∫ u in (0:ℝ)..T, f u * ((μ⁻¹ + ε) * (T - u) + C1)) := by
    rw [hrep]
    have hpt : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0:ℝ))), eqLaw Fon (Set.Ioi u) * H (T - u) ≤
        (Set.Iic T).indicator (fun u => ENNReal.ofReal (f u * ((μ⁻¹ + ε) * (T - u) + C1))) u := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      have hu0 : 0 ≤ u := le_of_lt hu
      by_cases huT : u ≤ T
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 huT), eqLaw_Ioi_tailI hon0 hion hu0,
          ENNReal.ofReal_mul (hf0 u)]
        refine mul_le_mul_right ?_ _
        obtain ⟨hfin, hb⟩ := hC0 (T - u) (by linarith)
        rw [← ENNReal.ofReal_toReal (a := H (T - u)) hfin]
        refine ENNReal.ofReal_le_ofReal ?_
        have hb' : |(H (T - u)).toReal - μ⁻¹ * (T - u)| ≤ ε * (T - u) + C0 := hb
        have := (abs_le.1 hb').2
        nlinarith
      · rw [Set.indicator_of_notMem (by simpa using huT), hHnn _ (by linarith), mul_zero]
    refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
    rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.Iic_inter_Ioi, intervalIntegral.integral_of_le hT,
      ofReal_integral_eq_lintegral_ofReal (hgi _ _).1]
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have : 0 ≤ (μ⁻¹ + ε) * (T - u) + C1 := by
      have := hu.2
      have : 0 ≤ μ⁻¹ + ε := by have := inv_pos.2 hmu; linarith
      nlinarith
    exact mul_nonneg (hf0 u) this
  -- lower bound
  have hlo : ENNReal.ofReal (∫ u in (0:ℝ)..T, f u * ((μ⁻¹ - ε) * (T - u) + -C1)) ≤
      MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T := by
    rw [hrep, intervalIntegral.integral_of_le hT]
    refine (ofReal_integral_le_lint (hgi _ _).1).trans ?_
    refine le_trans ?_ (lintegral_mono_set (Set.Ioc_subset_Ioi_self : Set.Ioc (0:ℝ) T ⊆ Set.Ioi 0))
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu.1
    rw [eqLaw_Ioi_tailI hon0 hion hu0, ENNReal.ofReal_mul (hf0 u)]
    refine mul_le_mul_right ?_ _
    obtain ⟨hfin, hb⟩ := hC0 (T - u) (by linarith [hu.2])
    rw [← ENNReal.ofReal_toReal (a := H (T - u)) hfin]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb' : |(H (T - u)).toReal - μ⁻¹ * (T - u)| ≤ ε * (T - u) + C0 := hb
    have := (abs_le.1 hb').1
    nlinarith
  have hfin : MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  refine ⟨hfin, ?_⟩
  have hX1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hup
  rw [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hT fun u hu => mul_nonneg (hf0 u)
    (by have := hu.2; have : 0 ≤ μ⁻¹ + ε := by have := inv_pos.2 hmu; linarith
        nlinarith)), hint] at hX1
  have hX2 := (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlo
  rw [hint] at hX2
  have e1 : (μ⁻¹ + ε) / m * A = A / (μ * m) + ε * (A / m) := by
    field_simp
  have e2 : (μ⁻¹ - ε) / m * A = A / (μ * m) - ε * (A / m) := by
    field_simp
  have hCB : C1 * B ≤ C1 * T := mul_le_mul_of_nonneg_left hBT hC1
  rw [abs_le]
  constructor <;> nlinarith

theorem rv_lower {f : ℝ → ℝ} (hf : Antitone f) (hpos : ∀ x, 0 < f x) {ρ : ℝ}
    (hrv : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 ((2:ℝ) ^ (-ρ)))) {ε : ℝ} (hε : 0 < ε)
    (hερ : ε < ρ) :
    ∃ c x0 : ℝ, 0 < c ∧ 0 < x0 ∧ ∀ x, x0 ≤ x → c * x ^ (-(ρ + ε)) ≤ f x := by
  obtain ⟨C, x0, hx0, hC, h⟩ := potter_antitone hf hpos hrv hε hερ
  refine ⟨f x0 / C * x0 ^ (ρ + ε), x0, mul_pos (div_pos (hpos x0) hC) (Real.rpow_pos_of_pos hx0 _),
    hx0, fun x hx => ?_⟩
  have h2 := (h x0 x le_rfl hx).2
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  rw [Real.div_rpow hxpos.le hx0.le] at h2
  rw [Real.rpow_neg hxpos.le]
  have hxe : 0 < x ^ (ρ + ε) := Real.rpow_pos_of_pos hxpos _
  have hx0e : 0 < x0 ^ (ρ + ε) := Real.rpow_pos_of_pos hx0 _
  have key : f x0 / C * x0 ^ (ρ + ε) * (x ^ (ρ + ε))⁻¹ =
      f x0 / (C * (x ^ (ρ + ε) / x0 ^ (ρ + ε))) := by
    field_simp
  rw [key, div_le_iff₀ (by positivity)]
  linarith [h2, show C * (x ^ (ρ + ε) / x0 ^ (ρ + ε)) * f x = f x * (C * (x ^ (ρ + ε) / x0 ^ (ρ + ε)))
    by ring]

theorem rv_upper {f : ℝ → ℝ} (hf : Antitone f) (hpos : ∀ x, 0 < f x) {ρ : ℝ}
    (hrv : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 ((2:ℝ) ^ (-ρ)))) {ε : ℝ} (hε : 0 < ε)
    (hερ : ε < ρ) :
    ∃ C x0 : ℝ, 0 < C ∧ 0 < x0 ∧ ∀ x, x0 ≤ x → f x ≤ C * x ^ (-ρ + ε) := by
  obtain ⟨C, x0, hx0, hC, h⟩ := potter_antitone hf hpos hrv hε hερ
  refine ⟨C * f x0 / x0 ^ (-ρ + ε), x0, div_pos (mul_pos hC (hpos x0)) (Real.rpow_pos_of_pos hx0 _),
    hx0, fun x hx => ?_⟩
  have h1 := (h x0 x le_rfl hx).1
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hx
  rw [Real.div_rpow hxpos.le hx0.le] at h1
  calc f x ≤ C * (x ^ (-ρ + ε) / x0 ^ (-ρ + ε)) * f x0 := h1
    _ = C * f x0 / x0 ^ (-ρ + ε) * x ^ (-ρ + ε) := by ring

theorem N_eq (F : Measure ℝ) {a T : ℝ} (hT : 0 < T) :
    T ^ (3 - a) * Lsv F a T = T ^ (3:ℝ) * Fbar F T := by
  unfold Lsv
  rw [← mul_assoc, ← Real.rpow_add hT, sub_add_cancel]

theorem N_pos {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (hsv : IsSlowlyVarying (Lsv F a)) :
    ∀ᶠ T in atTop, 0 < T ^ (3 - a) * Lsv F a T := by
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [N_eq F hT]
  exact mul_pos (Real.rpow_pos_of_pos hT _) (Fbar_pos_of_sv hsv T)

theorem T_div_N {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (ha1 : 1 < a) (ha2 : a < 2)
    (hsv : IsSlowlyVarying (Lsv F a)) :
    Tendsto (fun T => T / (T ^ (3 - a) * Lsv F a T)) atTop (𝓝 0) := by
  set ε : ℝ := (2 - a) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨c, x0, hc, hx0, hlow⟩ := rv_lower (Fbar_antitone F) (Fbar_pos_of_sv hsv)
    (Fbar_rv hsv two_pos) hε (by rw [hεdef]; linarith)
  have hlim : Tendsto (fun T : ℝ => c⁻¹ * T ^ (-(2 - a - ε))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by rw [hεdef]; linarith : 0 < 2 - a - ε)).const_mul c⁻¹
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [N_pos hsv, eventually_gt_atTop 0] with T hN hT
    exact div_nonneg hT.le hN.le
  · filter_upwards [eventually_ge_atTop x0] with T hT
    have hT0 : 0 < T := lt_of_lt_of_le hx0 hT
    rw [N_eq F hT0]
    have hF := hlow T hT
    have hFp := Fbar_pos_of_sv hsv T
    have h3 : 0 < T ^ (3:ℝ) := Real.rpow_pos_of_pos hT0 _
    have hX : 0 < T ^ (-(2 - a - ε)) := Real.rpow_pos_of_pos hT0 _
    have e : T ^ (-(2 - a - ε)) * (T ^ (3:ℝ) * T ^ (-(a + ε))) = T := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0,
        show -(2 - a - ε) + (3 + -(a + ε)) = (1:ℝ) by ring, Real.rpow_one]
    have e2 : c⁻¹ * T ^ (-(2 - a - ε)) * (T ^ (3:ℝ) * (c * T ^ (-(a + ε)))) = T := by
      calc c⁻¹ * T ^ (-(2 - a - ε)) * (T ^ (3:ℝ) * (c * T ^ (-(a + ε))))
          = (c⁻¹ * c) * (T ^ (-(2 - a - ε)) * (T ^ (3:ℝ) * T ^ (-(a + ε)))) := by ring
        _ = T := by rw [inv_mul_cancel₀ hc.ne', one_mul, e]
    rw [div_le_iff₀ (mul_pos h3 hFp)]
    calc T = c⁻¹ * T ^ (-(2 - a - ε)) * (T ^ (3:ℝ) * (c * T ^ (-(a + ε)))) := e2.symm
      _ ≤ c⁻¹ * T ^ (-(2 - a - ε)) * (T ^ (3:ℝ) * Fbar F T) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF h3.le) ?_
        exact mul_nonneg (inv_nonneg.2 hc.le) hX.le

theorem Fbar_ratio_zero {F G : Measure ℝ} [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hsvF : IsSlowlyVarying (Lsv F a))
    (hsvG : IsSlowlyVarying (Lsv G b)) :
    Tendsto (fun T => Fbar G T / Fbar F T) atTop (𝓝 0) := by
  set ε : ℝ := min ((b - a) / 3) (a / 2) with hεdef
  have hε1 : ε ≤ (b - a) / 3 := min_le_left _ _
  have hε2 : ε ≤ a / 2 := min_le_right _ _
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨c, x0, hc, hx0, hlow⟩ := rv_lower (Fbar_antitone F) (Fbar_pos_of_sv hsvF)
    (Fbar_rv hsvF two_pos) hε (by linarith)
  obtain ⟨C, x1, hC, hx1, hup⟩ := rv_upper (Fbar_antitone G) (Fbar_pos_of_sv hsvG)
    (Fbar_rv hsvG two_pos) hε (by linarith)
  have hlim : Tendsto (fun T : ℝ => C / c * T ^ (-(b - a - 2 * ε))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : 0 < b - a - 2 * ε)).const_mul (C / c)
    rwa [mul_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun T => div_nonneg (Fbar_nonneg G T) (Fbar_nonneg F T)
  · filter_upwards [eventually_ge_atTop x0, eventually_ge_atTop x1] with T hT0' hT1
    have hT0 : 0 < T := lt_of_lt_of_le hx0 hT0'
    have hl := hlow T hT0'
    have hu := hup T hT1
    have hcl : 0 < c * T ^ (-(a + ε)) := mul_pos hc (Real.rpow_pos_of_pos hT0 _)
    calc Fbar G T / Fbar F T ≤ (C * T ^ (-b + ε)) / (c * T ^ (-(a + ε))) :=
          div_le_div₀ (by positivity) hu hcl hl
      _ = C / c * T ^ (-(b - a - 2 * ε)) := by
          rw [mul_div_mul_comm, ← Real.rpow_sub hT0]
          congr 2; ring

theorem IPhi_ratio_zero {F G : Measure ℝ} [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    {a b : ℝ} (hG0 : G (Set.Iio 0) = 0) (hiG : Integrable (fun x : ℝ => x) G)
    (ha1 : 1 < a) (hab : a < b) (hb2 : b < 2)
    (hsvF : IsSlowlyVarying (Lsv F a)) (hsvG : IsSlowlyVarying (Lsv G b)) :
    Tendsto (fun T => (∫ u in (0:ℝ)..(2 * T), tailI G u * (2 * T - u)) /
      (T ^ (3 - a) * Lsv F a T)) atTop (𝓝 0) := by
  have hH := (tailI_head hG0 hiG (by linarith) hb2 hsvG).comp
    (tendsto_id.const_mul_atTop (two_pos : (0:ℝ) < 2))
  have hR := Fbar_ratio_zero (by linarith : (0:ℝ) < a) hab hsvF hsvG
  have hR8 : Tendsto (fun T => 8 * (Fbar G (2 * T) / Fbar F T)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun T => 8 * (Fbar G T / Fbar F T)) atTop (𝓝 0) := by
      have := hR.const_mul 8; rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
    · exact Eventually.of_forall fun T =>
        mul_nonneg (by norm_num) (div_nonneg (Fbar_nonneg G _) (Fbar_nonneg F T))
    · filter_upwards [eventually_ge_atTop 0] with T hT
      have hFp := Fbar_pos_of_sv hsvF T
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hFp.le) (by norm_num)
      exact Fbar_antitone G (by linarith)
  have hprod := hH.mul hR8
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have h2T : (0:ℝ) < 2 * T := by linarith
  simp only [Function.comp, id]
  rw [N_eq G h2T, N_eq F hT]
  have hGp := Fbar_pos_of_sv hsvG (2 * T)
  have hFp := Fbar_pos_of_sv hsvF T
  have h8 : (2 * T) ^ (3:ℝ) = 8 * T ^ (3:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hT.le]; norm_num
  rw [h8]
  have h3 : 0 < T ^ (3:ℝ) := Real.rpow_pos_of_pos hT _
  field_simp

theorem E1K_bound [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hion : Integrable (fun x : ℝ => x) Fon)
    (hioff : Integrable (fun x : ℝ => x) Foff) {s : Source Ω} (T : ℝ) :
    E1K Fon Foff (fun j => P.map (psum (srcZ s) j)) T ≤
      ENNReal.ofReal (mean Foff) * ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio T) := by
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  unfold E1K
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_indicator_const measurableSet_Iio]
  refine lintegral_mono fun b => ?_
  by_cases hb : b < T
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hb)]
    calc ∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff
        ≤ ∫⁻ w, ENNReal.ofReal w ∂Foff := by
          refine lintegral_mono fun w => ?_
          calc ∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)
              ≤ ∫⁻ _x, ENNReal.ofReal w ∂(eqLaw Fon) :=
                lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)
            _ = ENNReal.ofReal w := by rw [lintegral_const, measure_univ, mul_one]
      _ = ENNReal.ofReal (mean Foff) :=
          (ofReal_integral_eq_lintegral_ofReal hioff (ae_nonneg_of_Iio Foff hoff0)).symm
  · rw [Set.indicator_of_notMem (by simpa using hb)]
    calc ∫⁻ w, (∫⁻ x, ENNReal.ofReal (min w (T - (x + b))) ∂(eqLaw Fon)) ∂Foff
        ≤ ∫⁻ _w, (0:ℝ≥0∞) ∂Foff := by
          refine lintegral_mono fun w => ?_
          refine (lintegral_mono_ae ?_).trans (le_of_eq (lintegral_zero (μ := eqLaw Fon)))
          filter_upwards [ae_nonneg_of_Iio _ (eqLaw_Iio_zero Fon)] with x hx
          exact le_of_eq (ENNReal.ofReal_eq_zero.2 (min_le_of_right_le (by linarith [not_lt.1 hb])))
      _ = 0 := lintegral_zero

theorem lintegral_min_eqLaw {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (hm : 0 < mean F) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ y, ENNReal.ofReal (min y T) ∂(eqLaw F) ≤
      ENNReal.ofReal (∫ u in (0:ℝ)..T, tailI F u / mean F) := by
  have : IsProbabilityMeasure (eqLaw F) := eqLaw_isProb F h0 hi hm
  rw [Phi_rep]
  have hfi : IntervalIntegrable (fun u => tailI F u / mean F) volume 0 T :=
    (tailI_antitone h0 hi).intervalIntegrable.div_const _
  calc ∫⁻ u in Set.Ioi 0, (Set.Iio T).indicator (fun u => eqLaw F (Set.Ioi u)) u
      ≤ ∫⁻ u in Set.Ioi 0, (Set.Iio T).indicator
          (fun u => ENNReal.ofReal (tailI F u / mean F)) u := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun u hu => le_of_eq ?_
        simp only [Set.indicator_apply]
        split_ifs
        · exact eqLaw_Ioi_tailI h0 hi (le_of_lt hu)
        · rfl
    _ = ∫⁻ u in Set.Ioo 0 T, ENNReal.ofReal (tailI F u / mean F) := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Set.Iio_inter_Ioi]
    _ ≤ ∫⁻ u in Set.Ioc 0 T, ENNReal.ofReal (tailI F u / mean F) :=
        lintegral_mono_set Set.Ioo_subset_Ioc_self
    _ = ENNReal.ofReal (∫ u in (0:ℝ)..T, tailI F u / mean F) := by
        rw [intervalIntegral.integral_of_le hT, ofReal_integral_eq_lintegral_ofReal hfi.1]
        exact Eventually.of_forall fun u =>
          div_nonneg (tailI_nonneg F u) (mean_nonneg_of h0)

theorem E2K_bound [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff) (hion : Integrable (fun x : ℝ => x) Fon)
    (hioff : Integrable (fun x : ℝ => x) Foff) {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    {T : ℝ} (hT : 0 ≤ T) :
    E2K Fon Foff (fun j => P.map (psum (srcZ s) j)) T ≤
      ENNReal.ofReal (∫ u in (0:ℝ)..T, tailI Foff u / mean Foff) *
        ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio T) := by
  have : IsProbabilityMeasure (eqLaw Fon) := eqLaw_isProb Fon hon0 hion hon
  have : IsProbabilityMeasure (eqLaw Foff) := eqLaw_isProb Foff hoff0 hioff hoff
  unfold E2K
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [← lintegral_indicator_const measurableSet_Iio]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_nonneg_of_Iio _ (nu_Iio_zero hs hon0 hoff0 n)] with b hb0
  by_cases hb : b < T
  · rw [Set.indicator_of_mem (Set.mem_Iio.2 hb)]
    refine le_trans ?_ (lintegral_min_eqLaw hoff0 hioff hoff hT)
    refine lintegral_mono fun y => ?_
    calc ∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)
        ≤ ∫⁻ _x, ENNReal.ofReal (min y T) ∂(eqLaw Fon) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_nonneg_of_Iio _ (eqLaw_Iio_zero Fon)] with x hx
          exact ENNReal.ofReal_le_ofReal (min_le_min_left y (by linarith))
      _ = ENNReal.ofReal (min y T) := by rw [lintegral_const, measure_univ, mul_one]
  · rw [Set.indicator_of_notMem (by simpa using hb)]
    calc ∫⁻ y, (∫⁻ x, ENNReal.ofReal (min y (T - (x + b))) ∂(eqLaw Fon)) ∂(eqLaw Foff)
        ≤ ∫⁻ _y, (0:ℝ≥0∞) ∂(eqLaw Foff) := by
          refine lintegral_mono fun y => ?_
          refine (lintegral_mono_ae ?_).trans (le_of_eq (lintegral_zero (μ := eqLaw Fon)))
          filter_upwards [ae_nonneg_of_Iio _ (eqLaw_Iio_zero Fon)] with x hx
          exact le_of_eq (ENNReal.ofReal_eq_zero.2 (min_le_of_right_le (by linarith [not_lt.1 hb])))
      _ = 0 := lintegral_zero

theorem J_le {F : Measure ℝ} [IsProbabilityMeasure F] (h0 : F (Set.Iio 0) = 0)
    (hi : Integrable (fun x : ℝ => x) F) (hm : 0 < mean F) {T : ℝ} (hT : 0 < T) :
    ∫ u in (0:ℝ)..T, tailI F u / mean F ≤
      (∫ u in (0:ℝ)..(2 * T), tailI F u * (2 * T - u)) / (T * mean F) := by
  have hti : ∀ a c : ℝ, IntervalIntegrable (tailI F) volume a c :=
    fun a c => (tailI_antitone h0 hi).intervalIntegrable
  have hgi : ∀ c, IntervalIntegrable (fun u => tailI F u * (2 * T - u) / (T * mean F)) volume 0 c :=
    fun c => ((hti 0 c).mul_continuousOn (by fun_prop)).div_const _
  calc ∫ u in (0:ℝ)..T, tailI F u / mean F
      ≤ ∫ u in (0:ℝ)..T, tailI F u * (2 * T - u) / (T * mean F) := by
        refine intervalIntegral.integral_mono_on hT.le ((hti 0 T).div_const _) (hgi T) ?_
        intro u hu
        have ht := tailI_nonneg F u
        rw [div_le_div_iff₀ hm (mul_pos hT hm)]
        have : T ≤ 2 * T - u := by linarith [hu.2]
        have := mul_le_mul_of_nonneg_left this ht
        nlinarith
    _ ≤ ∫ u in (0:ℝ)..(2 * T), tailI F u * (2 * T - u) / (T * mean F) := by
        refine intervalIntegral.integral_mono_interval le_rfl hT.le (by linarith) ?_ (hgi _)
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun u hu => ?_
        exact div_nonneg (mul_nonneg (tailI_nonneg F u) (by linarith [hu.2]))
          (mul_pos hT hm).le
    _ = (∫ u in (0:ℝ)..(2 * T), tailI F u * (2 * T - u)) / (T * mean F) :=
        intervalIntegral.integral_div _ _

theorem div_N_tendsto_zero {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ} (ha1 : 1 < a)
    (ha2 : a < 2) (hsv : IsSlowlyVarying (Lsv F a)) (s0 : ℝ) :
    Tendsto (fun T => (T + s0) / (T ^ (3 - a) * Lsv F a T)) atTop (𝓝 0) := by
  have hTN := T_div_N ha1 ha2 hsv
  have h1N : Tendsto (fun T => 1 / (T ^ (3 - a) * Lsv F a T)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hTN ?_ ?_
    · filter_upwards [N_pos hsv] with T hN using div_nonneg zero_le_one hN.le
    · filter_upwards [N_pos hsv, eventually_ge_atTop 1] with T hN hT
      exact div_le_div_of_nonneg_right hT hN.le
  have := hTN.add (h1N.const_mul s0)
  rw [mul_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [N_pos hsv] with T hN
  field_simp

variable {α αoff : ℝ}

theorem MainK_asymp [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Tendsto (fun T => (MainK Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal /
      (T ^ (3 - α) * Lsv Fon α T)) atTop
      (𝓝 ((1 / ((α - 1) * (2 - α) * (3 - α))) / (mu Fon Foff * mean Fon))) := by
  have hα2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hμm : 0 < mu Fon Foff * mean Fon := mul_pos hmu hon
  refine tendsto_of_sandwich (b := fun T => (∫ u in (0:ℝ)..T, tailI Fon u * (T - u)) /
    (mu Fon Foff * mean Fon)) ?_ (T_div_N hF.one_lt hα2 hF.sv_on) (N_pos hF.sv_on) ?_
  · have h := (tailI_head hF.on_nonneg hion hF.one_lt hα2 hF.sv_on).div_const
      (mu Fon Foff * mean Fon)
    refine h.congr fun T => ?_
    ring
  · intro ε hε
    obtain ⟨C, _, hC⟩ := MainK_sandwich hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs
      (div_pos hε hmu)
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop 0] with T hT
    obtain ⟨_, h⟩ := hC T hT
    have hI : 0 ≤ ∫ u in (0:ℝ)..T, tailI Fon u * (T - u) :=
      intervalIntegral.integral_nonneg hT fun u hu =>
        mul_nonneg (tailI_nonneg Fon u) (by linarith [hu.2])
    rw [abs_of_nonneg (div_nonneg hI hμm.le)]
    have e : ε / mu Fon Foff * ((∫ u in (0:ℝ)..T, tailI Fon u * (T - u)) / mean Fon) =
        ε * ((∫ u in (0:ℝ)..T, tailI Fon u * (T - u)) / (mu Fon Foff * mean Fon)) := by
      field_simp
    linarith

theorem E1K_asymp [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Tendsto (fun T => (E1K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal /
      (T ^ (3 - α) * Lsv Fon α T)) atTop (𝓝 0) := by
  have hα2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  obtain ⟨c, s0, hc, hs0, hU⟩ := U_bound hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs
  have hlim := (div_N_tendsto_zero hF.one_lt hα2 hF.sv_on s0).const_mul (mean Foff * c)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [N_pos hF.sv_on] with T hN using div_nonneg ENNReal.toReal_nonneg hN.le
  · filter_upwards [N_pos hF.sv_on, eventually_ge_atTop 0] with T hN hT
    have hb : (E1K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal ≤
        mean Foff * c * (T + s0) := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      calc E1K Fon Foff (fun j => P.map (psum (srcZ s) j)) T
          ≤ ENNReal.ofReal (mean Foff) * ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio T) :=
            E1K_bound hF.on_nonneg hF.off_nonneg hon hion hioff T
        _ ≤ ENNReal.ofReal (mean Foff) * ENNReal.ofReal (c * (T + s0)) := by gcongr; exact hU T hT
        _ = ENNReal.ofReal (mean Foff * c * (T + s0)) := by
            rw [← ENNReal.ofReal_mul hoff.le, mul_assoc]
    calc (E1K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal / (T ^ (3 - α) * Lsv Fon α T)
        ≤ mean Foff * c * (T + s0) / (T ^ (3 - α) * Lsv Fon α T) :=
          div_le_div_of_nonneg_right hb hN.le
      _ = mean Foff * c * ((T + s0) / (T ^ (3 - α) * Lsv Fon α T)) := by ring

theorem E2K_asymp [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Tendsto (fun T => (E2K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal /
      (T ^ (3 - α) * Lsv Fon α T)) atTop (𝓝 0) := by
  obtain ⟨c, s0, hc, hs0, hU⟩ := U_bound hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs
  have hR := (IPhi_ratio_zero hF.off_nonneg hioff hF.one_lt hF.lt_off hF.off_lt_two hF.sv_on
    hF.sv_off).const_mul (c * (1 + s0) / mean Foff)
  rw [mul_zero] at hR
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR ?_ ?_
  · filter_upwards [N_pos hF.sv_on] with T hN using div_nonneg ENNReal.toReal_nonneg hN.le
  · filter_upwards [N_pos hF.sv_on, eventually_ge_atTop 1] with T hN hT1
    have hT : 0 < T := by linarith
    set J := ∫ u in (0:ℝ)..T, tailI Foff u / mean Foff with hJ
    set I2 := ∫ u in (0:ℝ)..(2 * T), tailI Foff u * (2 * T - u) with hI2
    have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hT.le fun u _ =>
      div_nonneg (tailI_nonneg Foff u) hoff.le
    have hI20 : 0 ≤ I2 := intervalIntegral.integral_nonneg (by linarith) fun u hu =>
      mul_nonneg (tailI_nonneg Foff u) (by linarith [hu.2])
    have hJle : J ≤ I2 / (T * mean Foff) := J_le hF.off_nonneg hioff hoff hT
    have hb : (E2K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal ≤
        J * (c * (T + s0)) := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      calc E2K Fon Foff (fun j => P.map (psum (srcZ s) j)) T
          ≤ ENNReal.ofReal J * ∑' n, (P.map (psum (srcZ s) n)) (Set.Iio T) :=
            E2K_bound hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs hT.le
        _ ≤ ENNReal.ofReal J * ENNReal.ofReal (c * (T + s0)) := by gcongr; exact hU T hT.le
        _ = ENNReal.ofReal (J * (c * (T + s0))) := by rw [← ENNReal.ofReal_mul hJ0]
    have hb2 : J * (c * (T + s0)) ≤ c * (1 + s0) / mean Foff * I2 := by
      have h1 : J * (c * (T + s0)) ≤ I2 / (T * mean Foff) * (c * (T + s0)) :=
        mul_le_mul_of_nonneg_right hJle (by positivity)
      have h2 : I2 / (T * mean Foff) * (c * (T + s0)) =
          c / mean Foff * I2 * ((T + s0) / T) := by field_simp
      have h3 : (T + s0) / T ≤ 1 + s0 := by
        rw [div_le_iff₀ hT]; nlinarith
      have h4 : c / mean Foff * I2 * ((T + s0) / T) ≤ c / mean Foff * I2 * (1 + s0) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : c / mean Foff * I2 * (1 + s0) = c * (1 + s0) / mean Foff * I2 := by ring
      linarith
    calc (E2K Fon Foff (fun j => P.map (psum (srcZ s) j)) T).toReal / (T ^ (3 - α) * Lsv Fon α T)
        ≤ c * (1 + s0) / mean Foff * I2 / (T ^ (3 - α) * Lsv Fon α T) :=
          div_le_div_of_nonneg_right (hb.trans hb2) hN.le
      _ = c * (1 + s0) / mean Foff * (I2 / (T ^ (3 - α) * Lsv Fon α T)) := by ring

/-- **C2b VarAsymp** for one ON/OFF source. -/
theorem var_asymp_source [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    Tendsto (fun T => Var[s.G P T; P] / (T ^ (3 - α) * Lsv Fon α T)) atTop
      (𝓝 (sigma0sq Fon Foff α)) := by
  have hα2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  have hα1 := hF.one_lt
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hM := MainK_asymp hF hon hoff hion hioff hs
  have hE1 := E1K_asymp hF hon hoff hion hioff hs
  have hE2 := E2K_asymp hF hon hoff hion hioff hs
  have hlim := ((hM.const_mul (mean Foff / mu Fon Foff)).add
    ((hE2.sub hE1).const_mul (mean Fon / mu Fon Foff))).const_mul
    (2 * (mean Foff / mu Fon Foff) * mean Fon)
  have hg3 : Real.Gamma (3 - α) = (2 - α) * Real.Gamma (2 - α) := by
    rw [show (3:ℝ) - α = (2 - α) + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hg4 : Real.Gamma (4 - α) = (3 - α) * Real.Gamma (3 - α) := by
    rw [show (4:ℝ) - α = (3 - α) + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hG : 0 < Real.Gamma (2 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hval : 2 * (mean Foff / mu Fon Foff) * mean Fon *
      (mean Foff / mu Fon Foff * ((1 / ((α - 1) * (2 - α) * (3 - α))) / (mu Fon Foff * mean Fon)) +
        mean Fon / mu Fon Foff * (0 - 0)) = sigma0sq Fon Foff α := by
    unfold sigma0sq
    rw [hg4, hg3]
    have h1 : α - 1 ≠ 0 := by linarith
    have h2 : 2 - α ≠ 0 := by linarith
    have h3 : 3 - α ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [var_G_decomp hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs hT]
  ring

end Asym

end NetTraffic.OnOffFBM.Lib

end F05Part4

-- ==== part Inc_part.lean ====
section F05Part5

/-! ### C3: uniform increment bound `Var(G(Tc) - G(Ta)) ≤ C N(T) (c-a)^β`, `β > 1`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Inc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem gamS_abs_le [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) (d : ℝ) :
    |gamS Fon Foff (fun j => P.map (psum (srcZ s) j)) d| ≤ 1 := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hp0 : 0 ≤ mean Fon / mu Fon Foff := (div_pos hon hmu).le
  have hp1 : mean Fon / mu Fon Foff ≤ 1 := by
    rw [div_le_one hmu]; unfold mu; linarith
  have hd : max d 0 - max (-d) 0 = d := by
    rcases le_total 0 d with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  rw [← hd, ← moment_Y hon0 hoff0 hon hoff hion hioff hs (le_max_right _ _) (le_max_right _ _)]
  have h := norm_integral_le_of_norm_le_const (μ := P) (C := 1)
    (f := fun ω => (What s (max (-d) 0) ω - mean Fon / mu Fon Foff) *
      (What s (max d 0) ω - mean Fon / mu Fon Foff))
    (Eventually.of_forall fun ω => by
      have a1 := What_nonneg s (max (-d) 0) ω
      have a2 := What_le_one s (max (-d) 0) ω
      have b1 := What_nonneg s (max d 0) ω
      have b2 := What_le_one s (max d 0) ω
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_one₀ (abs_le.2 ⟨by linarith, by linarith⟩) (abs_nonneg _)
        (abs_le.2 ⟨by linarith, by linarith⟩))
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

theorem var_G_le_sq [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {t : ℝ} (ht : 0 ≤ t) :
    Var[s.G P t; P] ≤ t ^ 2 := by
  have h := stat_increments hon0 hoff0 hon hoff hion hioff hs (a := 0) (c := t) le_rfl ht
  rw [sub_zero] at h
  rw [← h, var_G_sub hon0 hoff0 hon hoff hion hioff hs le_rfl ht]
  have hin : ∀ u, ‖∫ v in (0:ℝ)..t, gamS Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - u)‖ ≤
      1 * |t - 0| := fun u =>
    intervalIntegral.norm_integral_le_of_norm_le_const fun v _ => by
      rw [Real.norm_eq_abs]; exact gamS_abs_le hon0 hoff0 hon hoff hion hioff hs _
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (fun u _ => hin u)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht, one_mul] at hout
  nlinarith [le_abs_self (∫ u in (0:ℝ)..t, ∫ v in (0:ℝ)..t,
    gamS Fon Foff (fun j => P.map (psum (srcZ s) j)) (v - u))]

variable {α αoff : ℝ}

/-- **C3 IncrementBound** for one ON/OFF source. -/
theorem increment_bound_source [IsProbabilityMeasure P] {Fon Foff : Measure ℝ}
    [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff] (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {K : ℝ} (hK : 0 < K) :
    ∃ C β T₀ : ℝ, 1 < β ∧ ∀ T, T₀ ≤ T → ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ K →
      Var[fun ω => s.G P (T * c) ω - s.G P (T * a) ω; P] ≤
        C * (T ^ (3 - α) * Lsv Fon α T) * (c - a) ^ β := by
  have hα1 := hF.one_lt
  have hα2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  set ε : ℝ := (2 - α) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set β : ℝ := 3 - α - 2 * ε with hβdef
  have hβ1 : 1 < β := by rw [hβdef, hεdef]; linarith
  have hβ2 : β < 2 := by rw [hβdef, hεdef]; linarith
  have hV := var_asymp_source hF hon hoff hion hioff hs
  set S : ℝ := |sigma0sq Fon Foff α| + 1 with hSdef
  have hS : 0 < S := by positivity
  obtain ⟨t1, ht1⟩ := eventually_atTop.1
    ((hV.eventually (gt_mem_nhds (by linarith [le_abs_self (sigma0sq Fon Foff α)] :
      sigma0sq Fon Foff α < S))).and (N_pos hF.sv_on))
  obtain ⟨C0, x0, hx0, hC0, hpot⟩ := potter_antitone (Fbar_antitone Fon)
    (Fbar_pos_of_sv hF.sv_on) (Fbar_rv hF.sv_on two_pos) hε (by linarith : ε < α)
  obtain ⟨cl, x2, hcl, hx2, hlow⟩ := rv_lower (Fbar_antitone Fon) (Fbar_pos_of_sv hF.sv_on)
    (Fbar_rv hF.sv_on two_pos) hε (by linarith : ε < α)
  set x1 : ℝ := max (max t1 x0) 1 with hx1def
  have hx1one : 1 ≤ x1 := le_max_right _ _
  have hx1t1 : t1 ≤ x1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hx1x0 : x0 ≤ x1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx1pos : 0 < x1 := by linarith
  set CA : ℝ := x1 ^ (2 - β) / cl with hCAdef
  have hCA : 0 < CA := div_pos (Real.rpow_pos_of_pos hx1pos _) hcl
  have hK3 : 0 < K ^ (3 - β) := Real.rpow_pos_of_pos hK _
  set C : ℝ := CA + S * C0 + S * K ^ (3 - β) with hCdef
  refine ⟨C, β, max x1 x2, hβ1, fun T hT a c ha hac hcK => ?_⟩
  have hTx1 : x1 ≤ T := le_trans (le_max_left _ _) hT
  have hTx2 : x2 ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := le_trans hx1one hTx1
  have hT0 : 0 < T := by linarith
  have hTa : 0 ≤ T * a := mul_nonneg hT0.le ha
  rw [stat_increments hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs hTa
    (mul_le_mul_of_nonneg_left hac hT0.le), show T * c - T * a = T * (c - a) by ring]
  set h : ℝ := c - a with hhdef
  have hh0 : 0 ≤ h := by rw [hhdef]; linarith
  have hhK : h ≤ K := by rw [hhdef]; linarith
  set NT : ℝ := T ^ (3 - α) * Lsv Fon α T with hNTdef
  have hNTeq : NT = T ^ (3:ℝ) * Fbar Fon T := N_eq Fon hT0
  have h3 : 0 < T ^ (3:ℝ) := Real.rpow_pos_of_pos hT0 _
  have hFT := Fbar_pos_of_sv hF.sv_on T
  have hNT : 0 < NT := by rw [hNTeq]; exact mul_pos h3 hFT
  have hhb : 0 ≤ h ^ β := Real.rpow_nonneg hh0 _
  have hmono : ∀ X : ℝ, X ≤ C → X * NT * h ^ β ≤ C * NT * h ^ β := fun X hX =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hNT.le) hhb
  have hSC0 : 0 < S * C0 := mul_pos hS hC0
  have hSK : 0 < S * K ^ (3 - β) := mul_pos hS hK3
  have hTh0 : 0 ≤ T * h := mul_nonneg hT0.le hh0
  by_cases hA : T * h < x1
  · -- small increments: `Var ≤ (Th)^2`
    refine le_trans (var_G_le_sq hF.on_nonneg hF.off_nonneg hon hoff hion hioff hs hTh0) ?_
    refine le_trans ?_ (hmono CA (by linarith))
    have hhx : h ≤ x1 / T := by rw [le_div_iff₀ hT0]; linarith
    have hh2 : h ^ β * h ^ (2 - β) = h ^ 2 := by
      rw [← Real.rpow_add' hh0 (by rw [show β + (2 - β) = (2:ℝ) by ring]; norm_num),
        show β + (2 - β) = (2:ℝ) by ring, Real.rpow_two]
    have p2 : h ^ (2 - β) ≤ x1 ^ (2 - β) / T ^ (2 - β) := by
      rw [← Real.div_rpow hx1pos.le hT0.le]
      exact Real.rpow_le_rpow hh0 hhx (by linarith)
    have p3 : T ^ 2 / T ^ (2 - β) = T ^ β := by
      rw [← Real.rpow_two, ← Real.rpow_sub hT0]; congr 1; ring
    have p4 : T ^ β ≤ T ^ (3:ℝ) * T ^ (-(α + ε)) := by
      rw [← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by rw [hβdef]; linarith)
    have p5 := hlow T hTx2
    have hx1b : 0 < x1 ^ (2 - β) := Real.rpow_pos_of_pos hx1pos _
    have hT2b : 0 < T ^ (2 - β) := Real.rpow_pos_of_pos hT0 _
    calc (T * h) ^ 2 = T ^ 2 * h ^ β * h ^ (2 - β) := by rw [mul_pow, ← hh2]; ring
      _ ≤ T ^ 2 * h ^ β * (x1 ^ (2 - β) / T ^ (2 - β)) :=
          mul_le_mul_of_nonneg_left p2 (mul_nonneg (by positivity) hhb)
      _ = x1 ^ (2 - β) * h ^ β * (T ^ 2 / T ^ (2 - β)) := by ring
      _ = x1 ^ (2 - β) * h ^ β * T ^ β := by rw [p3]
      _ ≤ x1 ^ (2 - β) * h ^ β * (T ^ (3:ℝ) * T ^ (-(α + ε))) :=
          mul_le_mul_of_nonneg_left p4 (mul_nonneg hx1b.le hhb)
      _ = x1 ^ (2 - β) / cl * h ^ β * (T ^ (3:ℝ) * (cl * T ^ (-(α + ε)))) := by
          field_simp
      _ ≤ x1 ^ (2 - β) / cl * h ^ β * (T ^ (3:ℝ) * Fbar Fon T) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p5 h3.le)
            (mul_nonneg hCA.le hhb)
      _ = CA * NT * h ^ β := by rw [hNTeq]; ring
  · rw [not_lt] at hA
    have ht : t1 ≤ T * h := le_trans hx1t1 hA
    obtain ⟨hVt, hNt⟩ := ht1 (T * h) ht
    have hVt' : Var[s.G P (T * h); P] ≤ S * ((T * h) ^ (3 - α) * Lsv Fon α (T * h)) :=
      ((div_lt_iff₀ hNt).1 hVt).le
    have hTh : 0 < T * h := lt_of_lt_of_le hx1pos hA
    have hhpos : 0 < h := by
      rcases eq_or_lt_of_le hh0 with e | e
      · rw [← e, mul_zero] at hTh; exact absurd hTh (lt_irrefl 0)
      · exact e
    rw [N_eq Fon hTh, Real.mul_rpow hT0.le hhpos.le] at hVt'
    by_cases hB : h ≤ 1
    · refine le_trans hVt' ?_
      refine le_trans ?_ (hmono (S * C0) (by linarith))
      have hp := (hpot (T * h) T (le_trans hx1x0 hA) (mul_le_of_le_one_right hT0.le hB)).2
      have e1 : T / (T * h) = h⁻¹ := by field_simp
      rw [e1, Real.inv_rpow hhpos.le] at hp
      have hh3 : h ^ (3:ℝ) * (h ^ (α + ε))⁻¹ = h ^ (3 - α - ε) := by
        rw [← Real.rpow_neg hhpos.le, ← Real.rpow_add hhpos]; congr 1; ring
      have hhβ : h ^ (3 - α - ε) ≤ h ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hhpos hB (by rw [hβdef]; linarith)
      have hh3b : 0 < h ^ (3:ℝ) := Real.rpow_pos_of_pos hhpos _
      calc S * (T ^ (3:ℝ) * h ^ (3:ℝ) * Fbar Fon (T * h))
          ≤ S * (T ^ (3:ℝ) * h ^ (3:ℝ) * (C0 * (h ^ (α + ε))⁻¹ * Fbar Fon T)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (mul_pos h3 hh3b).le) hS.le
        _ = S * C0 * (T ^ (3:ℝ) * Fbar Fon T) * (h ^ (3:ℝ) * (h ^ (α + ε))⁻¹) := by ring
        _ = S * C0 * NT * h ^ (3 - α - ε) := by rw [hh3, ← hNTeq]
        _ ≤ S * C0 * NT * h ^ β := mul_le_mul_of_nonneg_left hhβ (mul_pos hSC0 hNT).le
    · rw [not_le] at hB
      refine le_trans hVt' ?_
      refine le_trans ?_ (hmono (S * K ^ (3 - β)) (by linarith))
      have hFb : Fbar Fon (T * h) ≤ Fbar Fon T := Fbar_antitone Fon (le_mul_of_one_le_right hT0.le hB.le)
      have hh3 : h ^ (3:ℝ) = h ^ β * h ^ (3 - β) := by
        rw [← Real.rpow_add hhpos]; congr 1; ring
      have hK' : h ^ (3 - β) ≤ K ^ (3 - β) := Real.rpow_le_rpow hh0 hhK (by linarith)
      have hh3b : 0 < h ^ (3:ℝ) := Real.rpow_pos_of_pos hhpos _
      calc S * (T ^ (3:ℝ) * h ^ (3:ℝ) * Fbar Fon (T * h))
          ≤ S * (T ^ (3:ℝ) * h ^ (3:ℝ) * Fbar Fon T) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFb (mul_pos h3 hh3b).le) hS.le
        _ = S * NT * (h ^ β * h ^ (3 - β)) := by rw [hNTeq, ← hh3]; ring
        _ ≤ S * NT * (h ^ β * K ^ (3 - β)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK' hhb) (mul_pos hS hNT).le
        _ = S * K ^ (3 - β) * NT * h ^ β := by ring

end Inc

end NetTraffic.OnOffFBM.Lib

end F05Part5

-- ==== part Fidi1_part.lean ====
section F05Part6

/-! ### C4a: covariance of one source and scaled second moments of finite combinations. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Fidi1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The bounded, measurable version of `G_T`. -/
noncomputable def Ghat (s : Source Ω) (p T : ℝ) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..T, (What s u ω - p)

theorem Ghat_measurable {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (p : ℝ) {T : ℝ} (hT : 0 ≤ T) : Measurable (Ghat s p T) := by
  have hYs : Measurable (fun q : Ω × ℝ => What s q.2 q.1 - p) :=
    ((What_measurable2 hs).comp measurable_swap).sub measurable_const
  have h := hYs.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc (0:ℝ) T))
  unfold Ghat
  simp only [intervalIntegral.integral_of_le hT]
  exact h.measurable

theorem Ghat_abs_le (s : Source Ω) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (ω : Ω) : |Ghat s p T ω| ≤ T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := T)
    (f := fun u => What s u ω - p) (C := 1) fun u _ => by
      rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [What_nonneg s u ω], by linarith [What_le_one s u ω]⟩
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT, one_mul] at h
  exact h

theorem G_ae_eq [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    ∀ᵐ ω ∂P, ∀ T, 0 ≤ T → s.G P T ω = Ghat s (mean Fon / mu Fon Foff) T ω := by
  filter_upwards [good_ae hs hon0 hoff0] with ω hω T hT
  unfold Source.G Ghat
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hT] at hu
  rw [W_eq_What hω hu.1, mean_W hon0 hoff0 hon hoff hion hioff hs hu.1]

theorem integral_Ghat [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, Ghat s (mean Fon / mu Fon Foff) T ω ∂P = 0 := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hm0 : 0 ≤ mean Fon / mu Fon Foff := div_nonneg hon.le hmu.le
  have hm1 : mean Fon / mu Fon Foff ≤ 1 := (div_le_one hmu).2 (by unfold mu; linarith)
  set p := mean Fon / mu Fon Foff with hp
  set μ : Measure ℝ := volume.restrict (Set.Ioc 0 T) with hμ
  have hYs : Measurable (fun q : Ω × ℝ => What s q.2 q.1 - p) :=
    ((What_measurable2 hs).comp measurable_swap).sub measurable_const
  have hb : ∀ u ω, |What s u ω - p| ≤ 1 := fun u ω =>
    abs_le.2 ⟨by linarith [What_nonneg s u ω], by linarith [What_le_one s u ω]⟩
  have hYint : Integrable (fun q : Ω × ℝ => What s q.2 q.1 - p) (P.prod μ) :=
    Integrable.of_bound hYs.aestronglyMeasurable 1 (Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]; exact hb _ _)
  unfold Ghat
  simp only [intervalIntegral.integral_of_le hT]
  rw [integral_integral_swap (f := fun ω u => What s u ω - p) hYint]
  have h0 : ∀ᵐ u ∂μ, ∫ ω, (What s u ω - p) ∂P = 0 := by
    rw [hμ]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [integral_sub (What_integrable hs u) (integrable_const _),
      mean_What hon0 hoff0 hon hoff hion hioff hs hu.1.le, integral_const]
    simp [hp]
  rw [integral_congr_ae h0, integral_zero]

theorem Ghat_integrable [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (Ghat s p T) P :=
  Integrable.of_bound (Ghat_measurable hs p hT).aestronglyMeasurable T
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact Ghat_abs_le s hp0 hp1 hT ω)

theorem Ghat_mul_integrable [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a c : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) : Integrable (fun ω => Ghat s p a ω * Ghat s p c ω) P :=
  Integrable.of_bound ((Ghat_measurable hs p ha).mul (Ghat_measurable hs p hc)).aestronglyMeasurable
    (a * c) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (Ghat_abs_le s hp0 hp1 ha ω) (Ghat_abs_le s hp0 hp1 hc ω) (abs_nonneg _) ha)

/-- Variance of `G_T` as a second moment of `Ghat`. -/
theorem var_G_eq [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {T : ℝ} (hT : 0 ≤ T) :
    Var[s.G P T; P] = ∫ ω, Ghat s (mean Fon / mu Fon Foff) T ω * Ghat s (mean Fon / mu Fon Foff) T ω ∂P := by
  have hae : s.G P T =ᵐ[P] Ghat s (mean Fon / mu Fon Foff) T := by
    filter_upwards [G_ae_eq hon0 hoff0 hon hoff hion hioff hs] with ω hω
    exact hω T hT
  rw [variance_congr hae, variance_of_integral_eq_zero (Ghat_measurable hs _ hT).aemeasurable
    (integral_Ghat hon0 hoff0 hon hoff hion hioff hs hT)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [pow_two]

/-- **Covariance of one source** from stationary increments:
`E[G_a G_c] = (V(a) + V(c) - V(c-a))/2`, `V = Var G`. -/
theorem cov_G [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) :
    ∫ ω, s.G P a ω * s.G P c ω ∂P =
      (Var[s.G P a; P] + Var[s.G P c; P] - Var[s.G P (c - a); P]) / 2 := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hm0 : 0 ≤ mean Fon / mu Fon Foff := div_nonneg hon.le hmu.le
  have hm1 : mean Fon / mu Fon Foff ≤ 1 := (div_le_one hmu).2 (by unfold mu; linarith)
  have hc : 0 ≤ c := ha.trans hac
  have hinc := stat_increments hon0 hoff0 hon hoff hion hioff hs ha hac
  rw [← hinc, var_G_eq hon0 hoff0 hon hoff hion hioff hs ha,
    var_G_eq hon0 hoff0 hon hoff hion hioff hs hc]
  have hG := G_ae_eq hon0 hoff0 hon hoff hion hioff hs
  set p := mean Fon / mu Fon Foff with hp
  have hae : (fun ω => s.G P c ω - s.G P a ω) =ᵐ[P] fun ω => Ghat s p c ω - Ghat s p a ω := by
    filter_upwards [hG] with ω hω
    rw [hω c hc, hω a ha]
  have hmean : ∫ ω, (Ghat s p c ω - Ghat s p a ω) ∂P = 0 := by
    rw [integral_sub (Ghat_integrable hs hm0 hm1 hc) (Ghat_integrable hs hm0 hm1 ha),
      integral_Ghat hon0 hoff0 hon hoff hion hioff hs hc,
      integral_Ghat hon0 hoff0 hon hoff hion hioff hs ha, sub_zero]
  rw [variance_congr hae, variance_of_integral_eq_zero (X := fun ω => Ghat s p c ω - Ghat s p a ω)
    (((Ghat_measurable hs p hc).sub (Ghat_measurable hs p ha)).aemeasurable) hmean]
  have hlhs : ∫ ω, s.G P a ω * s.G P c ω ∂P = ∫ ω, Ghat s p a ω * Ghat s p c ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hG] with ω hω
    rw [hω a ha, hω c hc]
  have hsq : ∫ ω, (Ghat s p c ω - Ghat s p a ω) ^ 2 ∂P =
      ∫ ω, (Ghat s p a ω * Ghat s p a ω + Ghat s p c ω * Ghat s p c ω -
        2 * (Ghat s p a ω * Ghat s p c ω)) ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    ring
  have hI1 : Integrable (fun ω => Ghat s p a ω * Ghat s p a ω + Ghat s p c ω * Ghat s p c ω) P :=
    (Ghat_mul_integrable hs hm0 hm1 ha ha).add (Ghat_mul_integrable hs hm0 hm1 hc hc)
  have hI2 : Integrable (fun ω => 2 * (Ghat s p a ω * Ghat s p c ω)) P :=
    (Ghat_mul_integrable hs hm0 hm1 ha hc).const_mul 2
  rw [hlhs, hsq, integral_sub hI1 hI2,
    integral_add (Ghat_mul_integrable hs hm0 hm1 ha ha) (Ghat_mul_integrable hs hm0 hm1 hc hc),
    integral_const_mul]
  ring

theorem G_mul_integrable [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    Integrable (fun ω => s.G P a ω * s.G P c ω) P := by
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hm0 : 0 ≤ mean Fon / mu Fon Foff := div_nonneg hon.le hmu.le
  have hm1 : mean Fon / mu Fon Foff ≤ 1 := (div_le_one hmu).2 (by unfold mu; linarith)
  refine (Ghat_mul_integrable hs hm0 hm1 ha hc).congr ?_
  filter_upwards [G_ae_eq hon0 hoff0 hon hoff hion hioff hs] with ω hω
  rw [hω a ha, hω c hc]

/-- The fBM covariance `½(t^{2H} + s^{2H} - |t-s|^{2H})`. -/
noncomputable def covH (H s t : ℝ) : ℝ :=
  (1 / 2) * (t ^ (2 * H) + s ^ (2 * H) - |t - s| ^ (2 * H))

theorem covH_comm (H s t : ℝ) : covH H s t = covH H t s := by
  unfold covH
  rw [abs_sub_comm]
  ring

theorem G_zero (s : Source Ω) : s.G P 0 = fun _ => 0 := by
  funext ω; simp [Source.G]

/-- `Var(G(Tt))/N(T) → σ₀² t^{3-α}`. -/
theorem var_scaled [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => Var[s.G P (T * t); P] / (T ^ (3 - α) * Lsv Fon α T)) atTop
      (𝓝 (sigma0sq Fon Foff α * t ^ (3 - α))) := by
  have hα2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have h3 : (3 - α) ≠ 0 := by linarith
    rw [Real.zero_rpow h3, mul_zero]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun T => ?_)
    dsimp only
    rw [mul_zero, G_zero, show (fun _ : Ω => (0:ℝ)) = 0 from rfl, variance_zero, zero_div]
  · have hA := (var_asymp_source hF hon hoff hion hioff hs).comp
      (tendsto_id.atTop_mul_const hpos)
    have hB := (hF.sv_on.2 t hpos).const_mul (t ^ (3 - α))
    rw [mul_one] at hB
    refine (hA.mul hB).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hLT : 0 < Lsv Fon α T := by
      unfold Lsv; exact mul_pos (Real.rpow_pos_of_pos hT _) (Fbar_pos_of_sv hF.sv_on T)
    have hLtT : 0 < Lsv Fon α (T * t) := by
      unfold Lsv
      exact mul_pos (Real.rpow_pos_of_pos (mul_pos hT hpos) _) (Fbar_pos_of_sv hF.sv_on _)
    have hTt := Real.rpow_pos_of_pos hT (3 - α)
    have htt := Real.rpow_pos_of_pos hpos (3 - α)
    simp only [Function.comp, id]
    rw [show t * T = T * t from mul_comm t T, Real.mul_rpow hT.le hpos.le]
    field_simp
    try ring

/-- `E[G(Ta)G(Tb)]/N(T) → σ₀² covH(a,b)`. -/
theorem cov_scaled [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun T => (∫ ω, s.G P (T * a) ω * s.G P (T * b) ω ∂P) / (T ^ (3 - α) * Lsv Fon α T))
      atTop (𝓝 (sigma0sq Fon Foff α * covH (hurst α) a b)) := by
  have hon0 := hF.on_nonneg
  have hoff0 := hF.off_nonneg
  have h2H : 2 * hurst α = 3 - α := by unfold hurst; ring
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Tendsto (fun T =>
      (∫ ω, s.G P (T * a) ω * s.G P (T * b) ω ∂P) / (T ^ (3 - α) * Lsv Fon α T))
      atTop (𝓝 (sigma0sq Fon Foff α * covH (hurst α) a b)) := by
    intro a b ha hab
    have hb := ha.trans hab
    have h := (((var_scaled hF hon hoff hion hioff hs ha).add
      (var_scaled hF hon hoff hion hioff hs hb)).sub
      (var_scaled hF hon hoff hion hioff hs (sub_nonneg.2 hab))).div_const 2
    have hlim : (sigma0sq Fon Foff α * a ^ (3 - α) + sigma0sq Fon Foff α * b ^ (3 - α) -
        sigma0sq Fon Foff α * (b - a) ^ (3 - α)) / 2 = sigma0sq Fon Foff α * covH (hurst α) a b := by
      unfold covH
      rw [h2H, abs_of_nonneg (sub_nonneg.2 hab)]
      ring
    rw [hlim] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [cov_G hon0 hoff0 hon hoff hion hioff hs (mul_nonneg hT ha) (mul_le_mul_of_nonneg_left hab hT),
      show T * b - T * a = T * (b - a) by ring]
    ring
  rcases le_total a b with hab | hba
  · exact key a b ha hab
  · rw [covH_comm]
    refine (key b a hb hba).congr fun T => ?_
    congr 2
    funext ω
    ring

/-- **Scaled second moment of a finite combination** (fidi covariance of one source). -/
theorem fidi_second_moment [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i) (c : ι → ℝ) :
    Tendsto (fun T => (∫ ω, (∑ i, c i * s.G P (T * t i) ω) ^ 2 ∂P) / (T ^ (3 - α) * Lsv Fon α T))
      atTop (𝓝 (sigma0sq Fon Foff α * ∑ i, ∑ j, c i * c j * covH (hurst α) (t i) (t j))) := by
  have hon0 := hF.on_nonneg
  have hoff0 := hF.off_nonneg
  have hlim : Tendsto (fun T => ∑ i, ∑ j, c i * c j *
      ((∫ ω, s.G P (T * t i) ω * s.G P (T * t j) ω ∂P) / (T ^ (3 - α) * Lsv Fon α T))) atTop
      (𝓝 (∑ i, ∑ j, c i * c j * (sigma0sq Fon Foff α * covH (hurst α) (t i) (t j)))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (cov_scaled hF hon hoff hion hioff hs (ht i) (ht j)).const_mul _
  have heq : ∑ i, ∑ j, c i * c j * (sigma0sq Fon Foff α * covH (hurst α) (t i) (t j)) =
      sigma0sq Fon Foff α * ∑ i, ∑ j, c i * c j * covH (hurst α) (t i) (t j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [heq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  have hint : ∀ i j, Integrable (fun ω => s.G P (T * t i) ω * s.G P (T * t j) ω) P := fun i j =>
    G_mul_integrable hon0 hoff0 hon hoff hion hioff hs (mul_nonneg hT (ht i)) (mul_nonneg hT (ht j))
  have hsq : ∀ ω, (∑ i, c i * s.G P (T * t i) ω) ^ 2 =
      ∑ i, ∑ j, c i * c j * (s.G P (T * t i) ω * s.G P (T * t j) ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hE : ∫ ω, (∑ i, c i * s.G P (T * t i) ω) ^ 2 ∂P =
      ∑ i, ∑ j, c i * c j * ∫ ω, s.G P (T * t i) ω * s.G P (T * t j) ω ∂P := by
    simp_rw [hsq]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  try dsimp only
  rw [hE, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Fidi1

end NetTraffic.OnOffFBM.Lib

end F05Part6

-- ==== part Fidi2_part.lean ====
section F05Part7

/-! ### C4b: the canonical source, the law of a source's ingredients, iid superposition. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Fidi2

/-- Index type of a source's ingredients. -/
abbrev SIdx := Fin 4 ⊕ (ℕ ⊕ ℕ)

/-- The space of a source's ingredients. -/
abbrev SE := SIdx → ℝ

/-- The canonical source on the ingredient space: its fields are the coordinates. -/
def canonE : Source SE where
  B := fun e => e (Sum.inl 0)
  X0 := fun e => e (Sum.inl 1)
  Y0 := fun e => e (Sum.inl 2)
  Yoff := fun e => e (Sum.inl 3)
  X := fun n e => e (Sum.inr (Sum.inl n))
  Y := fun n e => e (Sum.inr (Sum.inr n))

/-- All ingredients of a source as one point of `SE`. -/
def famvec {Ω : Type*} (s : Source Ω) (ω : Ω) : SE := fun i => s.family i ω

theorem canonE_family (i : SIdx) : canonE.family i = fun e : SE => e i := by
  rcases i with i | (n | n)
  · fin_cases i <;> rfl
  · rfl
  · rfl

theorem famvec_measurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Fon Foff : Measure ℝ}
    {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) : Measurable (famvec s) :=
  measurable_pi_iff.2 hs.measurable

theorem What_famvec {Ω : Type*} (s : Source Ω) (t : ℝ) (ω : Ω) :
    What canonE t (famvec s ω) = What s t ω := rfl

theorem Ghat_famvec {Ω : Type*} (s : Source Ω) (p T : ℝ) (ω : Ω) :
    Ghat canonE p T (famvec s ω) = Ghat s p T ω := rfl

/-- The law of the ingredients is the same for every ON/OFF source with the same period laws. -/
theorem law_famvec {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {Fon Foff : Measure ℝ} {s : Source Ω} {s' : Source Ω'}
    (hs : IsOnOffSource P Fon Foff s) (hs' : IsOnOffSource P' Fon Foff s') :
    P.map (famvec s) = P'.map (famvec s') := by
  unfold famvec
  rw [hs.indep.map_fun_eq_infinitePi_map hs.measurable,
    hs'.indep.map_fun_eq_infinitePi_map hs'.measurable]
  congr 1
  funext i
  rcases i with i | (n | n)
  · fin_cases i
    · exact hs.law_B.trans hs'.law_B.symm
    · exact hs.law_X0.trans hs'.law_X0.symm
    · exact hs.law_Y0.trans hs'.law_Y0.symm
    · exact hs.law_Yoff.trans hs'.law_Yoff.symm
  · exact (hs.law_X n).trans (hs'.law_X n).symm
  · exact (hs.law_Y n).trans (hs'.law_Y n).symm

/-- The canonical source is an ON/OFF source under the law of the ingredients. -/
theorem canonE_isOnOff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s) :
    IsOnOffSource (P.map (famvec s)) Fon Foff canonE := by
  have hfm := famvec_measurable hs
  have : IsProbabilityMeasure (P.map (famvec s)) := Measure.isProbabilityMeasure_map hfm.aemeasurable
  have hmap : ∀ i : SIdx, (P.map (famvec s)).map (fun e : SE => e i) = P.map (s.family i) :=
    fun i => by rw [Measure.map_map (measurable_pi_apply i) hfm]; rfl
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_, ?_, fun n => ?_, fun n => ?_⟩
  · rw [canonE_family]; exact measurable_pi_apply i
  · have hfam : canonE.family = fun (i : SIdx) (e : SE) => e i := funext canonE_family
    rw [hfam, iIndepFun_iff_map_fun_eq_infinitePi_map (fun i => measurable_pi_apply i)]
    have h1 : (P.map (famvec s)).map (fun (e : SE) (i : SIdx) => e i) = P.map (famvec s) :=
      Measure.map_id'
    rw [h1]
    simp_rw [hmap]
    exact hs.indep.map_fun_eq_infinitePi_map hs.measurable
  · exact (hmap (Sum.inl 0)).trans hs.law_B
  · exact (hmap (Sum.inl 1)).trans hs.law_X0
  · exact (hmap (Sum.inl 2)).trans hs.law_Y0
  · exact (hmap (Sum.inl 3)).trans hs.law_Yoff
  · exact (hmap (Sum.inr (Sum.inl n))).trans (hs.law_X n)
  · exact (hmap (Sum.inr (Sum.inr n))).trans (hs.law_Y n)

/-- The map from `Source.data` to the ingredient vector. -/
def dataToE (d : ℝ × ℝ × ℝ × ℝ × (ℕ → ℝ) × (ℕ → ℝ)) : SE :=
  Sum.elim ![d.1, d.2.1, d.2.2.1, d.2.2.2.1] (Sum.elim d.2.2.2.2.1 d.2.2.2.2.2)

theorem dataToE_measurable : Measurable dataToE := by
  rw [measurable_pi_iff]
  rintro (i | (n | n))
  · fin_cases i
    · exact measurable_fst
    · exact measurable_fst.comp measurable_snd
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  · exact (measurable_pi_apply n).comp (measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  · exact (measurable_pi_apply n).comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem famvec_eq_data {Ω : Type*} (s : Source Ω) : famvec s = dataToE ∘ s.data := by
  funext ω i
  rcases i with i | (n | n)
  · fin_cases i <;> rfl
  · rfl
  · rfl

/-- **iid superposition**: `E exp(i Σ_{m<M} h(src m)) = (E_{Q0} exp(i h))^M`. -/
theorem integral_exp_sum_iid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {M : ℕ} {src : ℕ → Source Ω}
    (hmodel : IsOnOffSuperposition P Fon Foff M src) (hM : 0 < M) (h : SE → ℝ)
    (hh : Measurable h) :
    ∫ ω, Complex.exp (Complex.I * ↑(∑ m ∈ Finset.range M, h (famvec (src m) ω))) ∂P =
      (∫ e, Complex.exp (Complex.I * ↑(h e)) ∂(P.map (famvec (src 0)))) ^ M := by
  have hsrc : ∀ m : Fin M, IsOnOffSource P Fon Foff (src m) := fun m => hmodel.source m m.2
  have hfm : ∀ m : Fin M, Measurable (famvec (src m)) := fun m => famvec_measurable (hsrc m)
  have hind : iIndepFun (fun m : Fin M => famvec (src m)) P := by
    have hfun : (fun m : Fin M => famvec (src m)) = fun (m : Fin M) => dataToE ∘ (src m).data :=
      funext fun (m : Fin M) => famvec_eq_data (src m)
    rw [hfun]
    exact hmodel.indep.comp _ fun _ => dataToE_measurable
  have hjoint := (iIndepFun_iff_map_fun_eq_pi_map (fun m => (hfm m).aemeasurable)).1 hind
  set g : SE → ℂ := fun e => Complex.exp (Complex.I * ↑(h e)) with hg
  have hgm : Measurable g := by
    rw [hg]; exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hh))
  have hpt : ∀ ω, Complex.exp (Complex.I * ↑(∑ m ∈ Finset.range M, h (famvec (src m) ω))) =
      ∏ m : Fin M, g ((fun ω (m : Fin M) => famvec (src m) ω) ω m) := by
    intro ω
    rw [Finset.sum_range, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hpt]
  have hjm : Measurable (fun ω (m : Fin M) => famvec (src m) ω) := measurable_pi_iff.2 hfm
  rw [← integral_map (f := fun x : Fin M → SE => ∏ m : Fin M, g (x m)) hjm.aemeasurable
    (Finset.measurable_prod _ fun m _ => hgm.comp (measurable_pi_apply m)).aestronglyMeasurable,
    hjoint, integral_fintype_prod_eq_prod (fun _ : Fin M => g)]
  have hlaw : ∀ m : Fin M, P.map (famvec (src m)) = P.map (famvec (src 0)) := fun m =>
    law_famvec (hsrc m) (hmodel.source 0 hM)
  simp_rw [hlaw]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Fidi2

end NetTraffic.OnOffFBM.Lib

end F05Part7

-- ==== part NT.lean ====
section F05Part8

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

/-- Fast growth (Condition 2) forces `M T * T * F̄_on(T) → ∞`. This is the Lindeberg
negligibility of one source: `(T / d_T)^2 = 1 / (M T F̄_on(T)) → 0`. -/
theorem tendsto_M_mul_T_mul_Fbar {Fon Foff : Measure ℝ} {α αoff : ℝ}
    (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ} (hC2 : Condition2 Fon M) :
    Tendsto (fun T => (M T : ℝ) * T * Fbar Fon T) atTop atTop := by
  have hα1 : 1 ≤ α := hF.one_lt.le
  refine tendsto_atTop.2 fun B => ?_
  set K : ℝ := max 1 (2 * B) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hKB : 2 * B ≤ K := le_max_right _ _
  have hKKa : K ≤ K ^ α := Real.self_le_rpow_of_one_le hK1 hα1
  have hsv := hF.sv_on.2 K hK0
  filter_upwards [hC2.eventually_gt_atTop K, eventually_gt_atTop (0 : ℝ),
    hsv.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)), hF.sv_on.1] with T hb hT0 hL2 hLpos
  have hbK : K * T < b Fon ((M T : ℝ) * T) := by rwa [lt_div_iff₀ hT0] at hb
  have h1 : 1 < (M T : ℝ) * T * Fbar Fon (K * T) := by
    by_contra h
    replace h := not_lt.mp h
    have hmem : K * T ∈ {x : ℝ | 0 < x ∧ (M T : ℝ) * T * Fbar Fon x ≤ 1} :=
      ⟨mul_pos hK0 hT0, h⟩
    have hle : b Fon ((M T : ℝ) * T) ≤ K * T := csInf_le ⟨0, fun x hx => hx.1.le⟩ hmem
    linarith
  have hL : Lsv Fon α (K * T) < 2 * Lsv Fon α T := by
    rwa [div_lt_iff₀ hLpos] at hL2
  have hp : 0 < T ^ α := Real.rpow_pos_of_pos hT0 α
  have key : (K ^ α * Fbar Fon (K * T)) * T ^ α < (2 * Fbar Fon T) * T ^ α := by
    calc (K ^ α * Fbar Fon (K * T)) * T ^ α = Lsv Fon α (K * T) := by
          unfold Lsv; rw [Real.mul_rpow hK0.le hT0.le]; ring
      _ < 2 * Lsv Fon α T := hL
      _ = (2 * Fbar Fon T) * T ^ α := by unfold Lsv; ring
  have hlt : K ^ α * Fbar Fon (K * T) < 2 * Fbar Fon T := lt_of_mul_lt_mul_right key hp.le
  have hMT : 0 ≤ (M T : ℝ) * T := by positivity
  have e1 : K ^ α * ((M T : ℝ) * T * Fbar Fon (K * T)) ≤ 2 * ((M T : ℝ) * T * Fbar Fon T) := by
    calc K ^ α * ((M T : ℝ) * T * Fbar Fon (K * T))
        = ((M T : ℝ) * T) * (K ^ α * Fbar Fon (K * T)) := by ring
      _ ≤ ((M T : ℝ) * T) * (2 * Fbar Fon T) := mul_le_mul_of_nonneg_left hlt.le hMT
      _ = 2 * ((M T : ℝ) * T * Fbar Fon T) := by ring
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK0 α
  have e2 : K ^ α < K ^ α * ((M T : ℝ) * T * Fbar Fon (K * T)) := lt_mul_of_one_lt_right hKa h1
  linarith

/-- For `T > 0`, `d_T = T * √(M T * T * F̄_on(T))`. -/
theorem dT_eq_mul_sqrt (Fon : Measure ℝ) (α : ℝ) (M : ℝ → ℕ) {T : ℝ} (hT : 0 < T) :
    dT Fon α M T = T * Real.sqrt ((M T : ℝ) * T * Fbar Fon T) := by
  unfold dT Lsv
  have h3 : T ^ (3 - α) * T ^ α = T ^ 2 * T := by
    rw [← Real.rpow_add hT, show (3 - α + α) = ((3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have : T ^ (3 - α) * (T ^ α * Fbar Fon T) * (M T : ℝ) = T ^ 2 * ((M T : ℝ) * T * Fbar Fon T) := by
    calc T ^ (3 - α) * (T ^ α * Fbar Fon T) * (M T : ℝ)
        = (T ^ (3 - α) * T ^ α) * (Fbar Fon T * (M T : ℝ)) := by ring
      _ = T ^ 2 * ((M T : ℝ) * T * Fbar Fon T) := by rw [h3]; ring
  rw [this, Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT.le]

/-- Lindeberg negligibility: under fast growth, `d_T / T → ∞`. -/
theorem tendsto_dT_div_T {Fon Foff : Measure ℝ} {α αoff : ℝ}
    (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ} (hC2 : Condition2 Fon M) :
    Tendsto (fun T => dT Fon α M T / T) atTop atTop := by
  have h := Real.tendsto_sqrt_atTop.comp (tendsto_M_mul_T_mul_Fbar hF hC2)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simp only [Function.comp_apply]
  rw [dT_eq_mul_sqrt Fon α M hT, mul_div_cancel_left₀ _ hT.ne']

end NetTraffic.OnOffFBM.Lib

/-! Potter-type upper bound for slowly varying functions (used for C3, finiteness of means,
and `σ₀ > 0`). -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

/-- **Potter upper bound.** A slowly varying `L` that is bounded above on every `(0, R]` grows
slower than any power: for `ε > 0` there are `C, x₀ > 0` with `L x ≤ C x^ε` for `x ≥ x₀`. -/
theorem potter_upper {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (hloc : ∀ R : ℝ, ∃ B : ℝ, ∀ x, 0 < x → x ≤ R → L x ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ C x₀ : ℝ, 0 < x₀ ∧ ∀ x, x₀ ≤ x → L x ≤ C * x ^ ε := by
  have h2ε : (1 : ℝ) < 2 ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hev : ∀ᶠ x in atTop, L (2 * x) < 2 ^ ε * L x ∧ 0 < L x := by
    filter_upwards [(hL.2 2 two_pos).eventually (gt_mem_nhds h2ε), hL.1] with x hx hpos
    exact ⟨by rwa [div_lt_iff₀ hpos] at hx, hpos⟩
  obtain ⟨a, ha⟩ := eventually_atTop.1 hev
  set x₀ := max a 1 with hx₀
  have hx₀1 : 1 ≤ x₀ := le_max_right _ _
  have hx₀0 : 0 < x₀ := lt_of_lt_of_le one_pos hx₀1
  have hx₀a : a ≤ x₀ := le_max_left _ _
  obtain ⟨B, hB⟩ := hloc (2 * x₀)
  have hB0 : 0 ≤ B := ((ha x₀ hx₀a).2.le).trans (hB x₀ hx₀0 (by linarith))
  have claim : ∀ k : ℕ, ∀ x, x₀ ≤ x → x < 2 ^ k * x₀ → L x ≤ B * (x / x₀) ^ ε := by
    intro k
    induction k with
    | zero =>
      intro x hx hxk
      simp at hxk
      linarith
    | succ k ih =>
      intro x hx hxk
      have hq1 : 1 ≤ x / x₀ := by rw [le_div_iff₀ hx₀0]; linarith
      by_cases hx2 : x ≤ 2 * x₀
      · have h1 : L x ≤ B := hB x (by linarith) hx2
        have h2 : 1 ≤ (x / x₀) ^ ε := Real.one_le_rpow hq1 hε.le
        nlinarith
      · push Not at hx2
        set y := x / 2 with hy
        have hyx : x = 2 * y := by rw [hy]; ring
        have hy0 : x₀ ≤ y := by rw [hy]; linarith
        have hyk : y < 2 ^ k * x₀ := by
          rw [hy]; rw [pow_succ] at hxk; linarith
        have hIH := ih y hy0 hyk
        have hstep := (ha y (hx₀a.trans hy0)).1
        have hpow : (2 : ℝ) ^ ε * (y / x₀) ^ ε = (x / x₀) ^ ε := by
          rw [← Real.mul_rpow (by norm_num) (div_nonneg (by linarith) hx₀0.le), hyx]
          ring_nf
        have h2e : 0 ≤ (2 : ℝ) ^ ε := by positivity
        calc L x = L (2 * y) := by rw [hyx]
          _ ≤ 2 ^ ε * L y := hstep.le
          _ ≤ 2 ^ ε * (B * (y / x₀) ^ ε) := mul_le_mul_of_nonneg_left hIH h2e
          _ = B * ((2 : ℝ) ^ ε * (y / x₀) ^ ε) := by ring
          _ = B * (x / x₀) ^ ε := by rw [hpow]
  refine ⟨B / x₀ ^ ε, x₀, hx₀0, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (x / x₀) (by norm_num : (1 : ℝ) < 2)
  have hxk : x < 2 ^ k * x₀ := by rwa [div_lt_iff₀ hx₀0] at hk
  have := claim k x hx hxk
  rw [Real.div_rpow (by linarith) hx₀0.le] at this
  have hp : 0 < x₀ ^ ε := Real.rpow_pos_of_pos hx₀0 ε
  calc L x ≤ B * (x ^ ε / x₀ ^ ε) := this
    _ = B / x₀ ^ ε * x ^ ε := by ring

/-- The tail factor `L(x) = x^a F̄(x)` of a probability law is bounded on every `(0, R]`
when `a ≥ 0`. -/
theorem Lsv_bounded_on (F : Measure ℝ) [IsProbabilityMeasure F] {a : ℝ} (ha : 0 ≤ a) (R : ℝ) :
    ∃ B : ℝ, ∀ x, 0 < x → x ≤ R → Lsv F a x ≤ B := by
  refine ⟨R ^ a, fun x hx hxR => ?_⟩
  unfold Lsv Fbar
  have h1 : F.real (Set.Ioi x) ≤ 1 := by
    rw [← probReal_univ (μ := F)]
    exact measureReal_mono (Set.subset_univ _)
  have h0 : 0 ≤ F.real (Set.Ioi x) := measureReal_nonneg
  have hxa : x ^ a ≤ R ^ a := Real.rpow_le_rpow hx.le hxR ha
  have hxa0 : 0 ≤ x ^ a := Real.rpow_nonneg hx.le a
  calc x ^ a * F.real (Set.Ioi x) ≤ x ^ a * 1 := mul_le_mul_of_nonneg_left h1 hxa0
    _ ≤ R ^ a := by linarith

/-- Potter bound for the ON-period tail factor `L_on`. -/
theorem potter_Lon {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] {α αoff : ℝ}
    (hF : HeavyTails Fon Foff α αoff) {ε : ℝ} (hε : 0 < ε) :
    ∃ C x₀ : ℝ, 0 < x₀ ∧ ∀ x, x₀ ≤ x → Lsv Fon α x ≤ C * x ^ ε :=
  potter_upper hF.sv_on (Lsv_bounded_on Fon (by linarith [hF.one_lt])) hε

/-- Potter bound for the OFF-period tail factor `L_off`. -/
theorem potter_Loff {Fon Foff : Measure ℝ} [IsProbabilityMeasure Foff] {α αoff : ℝ}
    (hF : HeavyTails Fon Foff α αoff) {ε : ℝ} (hε : 0 < ε) :
    ∃ C x₀ : ℝ, 0 < x₀ ∧ ∀ x, x₀ ≤ x → Lsv Foff αoff x ≤ C * x ^ ε :=
  potter_upper hF.sv_off (Lsv_bounded_on Foff (by linarith [hF.one_lt, hF.lt_off])) hε

/-- A heavy-tailed law on `[0, ∞)` with tail index `a > 1` has a finite mean. -/
theorem integrable_id_of_heavy {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ}
    (h0 : F (Set.Iio 0) = 0) (ha : 1 < a) (hsv : IsSlowlyVarying (Lsv F a)) :
    Integrable (fun x : ℝ => x) F := by
  set ε : ℝ := (a - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C, x₀, hx₀, hC⟩ := potter_upper hsv (Lsv_bounded_on F (by linarith)) hε0
  have hp : ε - a < -1 := by rw [hε]; linarith
  have hFnn : ∀ t, 0 ≤ Fbar F t := fun t => measureReal_nonneg
  have hFle : ∀ t, x₀ ≤ t → Fbar F t ≤ C * t ^ (ε - a) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have h1 := hC t ht
    unfold Lsv at h1
    have hta : 0 < t ^ a := Real.rpow_pos_of_pos ht0 a
    have h2 : Fbar F t ≤ C * t ^ ε / t ^ a := by
      rw [le_div_iff₀ hta]; linarith
    calc Fbar F t ≤ C * t ^ ε / t ^ a := h2
      _ = C * t ^ (ε - a) := by rw [Real.rpow_sub ht0]; ring
  have hanti : Antitone (Fbar F) := fun s t hst =>
    measureReal_mono (Set.Ioi_subset_Ioi hst)
  have hmeas : Measurable (Fbar F) := hanti.measurable
  have hI1 : IntegrableOn (Fbar F) (Set.Ioc 0 x₀) :=
    (AntitoneOn.integrableOn_isCompact isCompact_Icc (hanti.antitoneOn _)).mono_set
      Set.Ioc_subset_Icc_self
  have hI2 : IntegrableOn (Fbar F) (Set.Ioi x₀) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hp hx₀).const_mul C)
      hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn t)]
    exact hFle t (le_of_lt ht)
  have hI : IntegrableOn (Fbar F) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx₀.le]
    exact hI1.union hI2
  have hnn : 0 ≤ᵐ[F] (fun x : ℝ => x) := by
    rw [Filter.EventuallyLE, ae_iff]
    exact measure_mono_null (fun x hx => Set.mem_Iio.2 (not_le.1 hx)) h0
  have hlc := lintegral_eq_lintegral_meas_lt F hnn measurable_id.aemeasurable
  have hfin : ∫⁻ t in Set.Ioi 0, F {x | t < x} < ⊤ := by
    calc ∫⁻ t in Set.Ioi 0, F {x | t < x} = ∫⁻ t in Set.Ioi 0, ‖Fbar F t‖ₑ := by
          refine lintegral_congr fun t => ?_
          rw [Real.enorm_eq_ofReal (hFnn t)]
          exact (ofReal_measureReal (measure_ne_top F _)).symm
      _ < ⊤ := hI.2
  refine ⟨measurable_id'.aestronglyMeasurable, ?_⟩
  have hcongr : ∫⁻ x, ‖x‖ₑ ∂F = ∫⁻ x, ENNReal.ofReal x ∂F :=
    lintegral_congr_ae (by filter_upwards [hnn] with x hx; exact Real.enorm_eq_ofReal hx)
  show ∫⁻ x, ‖x‖ₑ ∂F < ⊤
  rw [hcongr, hlc]
  exact hfin

/-- A heavy-tailed law on `[0, ∞)` (tail index `a > 1`, slowly varying tail factor) has a
strictly positive mean. -/
theorem mean_pos_of_heavy {F : Measure ℝ} [IsProbabilityMeasure F] {a : ℝ}
    (h0 : F (Set.Iio 0) = 0) (ha : 1 < a) (hsv : IsSlowlyVarying (Lsv F a)) :
    0 < mean F := by
  obtain ⟨x₁, hL, hx₁⟩ := (hsv.1.and (eventually_gt_atTop (0 : ℝ))).exists
  have hFb : 0 < Fbar F x₁ := by
    unfold Lsv at hL
    exact pos_of_mul_pos_right hL (Real.rpow_pos_of_pos hx₁ a).le
  have hint := integrable_id_of_heavy h0 ha hsv
  have hnn : ∀ᵐ x ∂F, 0 ≤ x := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => Set.mem_Iio.2 (not_le.1 hx)) h0
  have hle : (Set.Ioi x₁).indicator (fun _ => x₁) ≤ᵐ[F] (fun x : ℝ => x) := by
    filter_upwards [hnn] with x hx
    by_cases hxs : x ∈ Set.Ioi x₁
    · rw [Set.indicator_of_mem hxs]; exact le_of_lt hxs
    · rw [Set.indicator_of_notMem hxs]; exact hx
  have hmono := integral_mono_ae ((integrable_const x₁).indicator measurableSet_Ioi) hint hle
  rw [integral_indicator_const _ measurableSet_Ioi] at hmono
  have : 0 < F.real (Set.Ioi x₁) • x₁ := by
    rw [smul_eq_mul]; exact mul_pos hFb hx₁
  unfold mean
  linarith

/-- `μ = μ_on + μ_off > 0` and `μ_off > 0`. -/
theorem mean_off_pos {Fon Foff : Measure ℝ} [IsProbabilityMeasure Foff] {α αoff : ℝ}
    (hF : HeavyTails Fon Foff α αoff) : 0 < mean Foff :=
  mean_pos_of_heavy hF.off_nonneg (by linarith [hF.one_lt, hF.lt_off]) hF.sv_off

theorem mean_on_pos {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] {α αoff : ℝ}
    (hF : HeavyTails Fon Foff α αoff) : 0 < mean Fon :=
  mean_pos_of_heavy hF.on_nonneg hF.one_lt hF.sv_on

theorem mu_pos {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) : 0 < mu Fon Foff := by
  unfold mu; linarith [mean_on_pos hF, mean_off_pos hF]

/-- `σ₀² > 0`, hence `σ₀ > 0`. -/
theorem sigma0sq_pos {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) : 0 < sigma0sq Fon Foff α := by
  have h1 := hF.one_lt
  have h2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  have hg2 : 0 < Real.Gamma (2 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hg4 : 0 < Real.Gamma (4 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hm := mean_off_pos hF
  have hmu := mu_pos hF
  unfold sigma0sq
  apply div_pos
  · apply div_pos _ (by linarith)
    exact mul_pos (mul_pos two_pos (pow_pos hm 2)) hg2
  · exact mul_pos (pow_pos hmu 3) hg4

theorem sigma0_pos {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) : 0 < sigma0 Fon Foff α :=
  Real.sqrt_pos.2 (sigma0sq_pos hF)

end NetTraffic.OnOffFBM.Lib

/-! C4 for f05ae606: a Lindeberg-type CLT, in characteristic-function form, for rows of iid
bounded, asymptotically negligible variables (a triangular array). -/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped NNReal ENNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

/-- General exponent: if `M n → ∞` and `M n * (a n - 1) → t` then `a n ^ M n → exp t`. -/
theorem tendsto_pow_exp_of_tendsto_mul_sub_one {a : ℕ → ℂ} {Mn : ℕ → ℕ} {t : ℂ}
    (hM : Tendsto Mn atTop atTop)
    (h : Tendsto (fun n => (Mn n : ℂ) * (a n - 1)) atTop (𝓝 t)) :
    Tendsto (fun n => a n ^ Mn n) atTop (𝓝 (Complex.exp t)) := by
  have hinv : Tendsto (fun n => ((Mn n : ℂ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ((Mn n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using h2
  have hz : Tendsto (fun n => a n - 1) atTop (𝓝 0) := by
    have h3 := hinv.mul h
    rw [zero_mul] at h3
    refine h3.congr' ?_
    filter_upwards [hM.eventually_gt_atTop 0] with n hn
    have hne : (Mn n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    exact inv_mul_cancel_left₀ hne _
  have hzn : ∀ᶠ n in atTop, ‖a n - 1‖ < 1 / 2 :=
    hz.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1 / 2))
  have hlog : Tendsto (fun n => (Mn n : ℂ) * Complex.log (a n)) atTop (𝓝 t) := by
    have hdiff : Tendsto (fun n => (Mn n : ℂ) * Complex.log (a n) - (Mn n : ℂ) * (a n - 1))
        atTop (𝓝 0) := by
      have hb : Tendsto (fun n => ‖(Mn n : ℂ) * (a n - 1)‖ * ‖a n - 1‖) atTop
          (𝓝 (‖t‖ * ‖(0 : ℂ)‖)) := h.norm.mul hz.norm
      rw [norm_zero, mul_zero] at hb
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [hzn] with n hn
      have hz1 : ‖a n - 1‖ < 1 := by linarith
      have hL := Complex.norm_log_one_add_sub_self_le hz1
      rw [add_sub_cancel] at hL
      have hfac : (1 - ‖a n - 1‖)⁻¹ / 2 ≤ 1 := by
        rw [div_le_one (by norm_num : (0 : ℝ) < 2), inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      have hq : ‖a n - 1‖ ^ 2 * (1 - ‖a n - 1‖)⁻¹ / 2 ≤ ‖a n - 1‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hfac (sq_nonneg ‖a n - 1‖)
        linarith
      calc ‖(Mn n : ℂ) * Complex.log (a n) - (Mn n : ℂ) * (a n - 1)‖
          = (Mn n : ℝ) * ‖Complex.log (a n) - (a n - 1)‖ := by
            rw [← mul_sub, norm_mul, Complex.norm_natCast]
        _ ≤ (Mn n : ℝ) * ‖a n - 1‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (hL.trans hq) (Nat.cast_nonneg _)
        _ = ‖(Mn n : ℂ) * (a n - 1)‖ * ‖a n - 1‖ := by
            rw [norm_mul, Complex.norm_natCast]; ring
    have h4 := hdiff.add h
    rw [zero_add] at h4
    refine h4.congr' (Eventually.of_forall fun n => ?_)
    simp only [sub_add_cancel]
  have hexp := (Complex.continuous_exp.tendsto t).comp hlog
  refine hexp.congr' ?_
  filter_upwards [hzn] with n hn
  have ha0 : a n ≠ 0 := by
    intro h0
    rw [h0] at hn
    norm_num at hn
  simp only [Function.comp_apply]
  rw [Complex.exp_nat_mul, Complex.exp_log ha0]

/-- Second-order expansion of the characteristic function of a bounded centred variable:
`|φ(v) - (1 - v² E Z² / 2)| ≤ |v|³ c E Z²` when `|Z| ≤ c` and `|v| c ≤ 1`. -/
theorem norm_charFun_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) {c : ℝ}
    (hb : ∀ᵐ ω ∂P, |Z ω| ≤ c) (h0 : ∫ ω, Z ω ∂P = 0) {v : ℝ} (hv : |v| * c ≤ 1) :
    ‖charFun (P.map Z) v - ((1 - v ^ 2 * (∫ ω, Z ω ^ 2 ∂P) / 2 : ℝ) : ℂ)‖ ≤
      |v| ^ 3 * c * ∫ ω, Z ω ^ 2 ∂P := by
  have hZi : Integrable Z P :=
    Integrable.of_bound hZ.aestronglyMeasurable c (by simpa [Real.norm_eq_abs] using hb)
  have hZ2i : Integrable (fun ω => Z ω ^ 2) P := by
    refine Integrable.of_bound (hZ.pow_const 2).aestronglyMeasurable (c ^ 2) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  rw [charFun_apply_real, integral_map hZ.aemeasurable (by fun_prop)]
  have hpoly : ∀ ω, (1 : ℂ) + (v : ℂ) * (Z ω : ℂ) * I + ((v : ℂ) * (Z ω : ℂ) * I) ^ 2 / 2 =
      ((1 - v ^ 2 * Z ω ^ 2 / 2 : ℝ) : ℂ) + ((v * Z ω : ℝ) : ℂ) * I := by
    intro ω
    push_cast
    linear_combination ((v : ℂ) ^ 2 * (Z ω : ℂ) ^ 2 / 2) * I_sq
  have hr1 : Integrable (fun ω => 1 - v ^ 2 * Z ω ^ 2 / 2) P :=
    (integrable_const 1).sub ((hZ2i.const_mul (v ^ 2)).div_const 2)
  have hr2 : Integrable (fun ω => v * Z ω) P := hZi.const_mul v
  have hpolyi : Integrable (fun ω => (1 : ℂ) + (v : ℂ) * (Z ω : ℂ) * I +
      ((v : ℂ) * (Z ω : ℂ) * I) ^ 2 / 2) P := by
    simp_rw [hpoly]
    exact hr1.ofReal.add (hr2.ofReal.mul_const I)
  have hpi : ∫ ω, ((1 : ℂ) + (v : ℂ) * (Z ω : ℂ) * I + ((v : ℂ) * (Z ω : ℂ) * I) ^ 2 / 2) ∂P =
      ((1 - v ^ 2 * (∫ ω, Z ω ^ 2 ∂P) / 2 : ℝ) : ℂ) := by
    simp_rw [hpoly]
    have hc1 : Integrable (fun ω => ((1 - v ^ 2 * Z ω ^ 2 / 2 : ℝ) : ℂ)) P := hr1.ofReal
    have hc2 : Integrable (fun ω => ((v * Z ω : ℝ) : ℂ) * I) P := hr2.ofReal.mul_const I
    rw [integral_add hc1 hc2, integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal, integral_const_mul, h0,
      integral_sub (integrable_const 1) ((hZ2i.const_mul (v ^ 2)).div_const 2), integral_const,
      integral_div, integral_const_mul]
    simp
  have hexpi : Integrable (fun ω => cexp ((v : ℂ) * (Z ω : ℂ) * I)) P := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => ?_)
    have : (v : ℂ) * (Z ω : ℂ) * I = ((v * Z ω : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hbound : ∀ᵐ ω ∂P, ‖cexp ((v : ℂ) * (Z ω : ℂ) * I) - ((1 : ℂ) + (v : ℂ) * (Z ω : ℂ) * I +
      ((v : ℂ) * (Z ω : ℂ) * I) ^ 2 / 2)‖ ≤ |v| ^ 3 * c * Z ω ^ 2 := by
    filter_upwards [hb] with ω hω
    set y : ℂ := (v : ℂ) * (Z ω : ℂ) * I with hy
    have hny : ‖y‖ = |v| * |Z ω| := by
      rw [hy, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, mul_one]
    have hy1 : ‖y‖ ≤ 1 := by
      rw [hny]
      calc |v| * |Z ω| ≤ |v| * c := mul_le_mul_of_nonneg_left hω (abs_nonneg v)
        _ ≤ 1 := hv
    have hE := Complex.exp_bound hy1 (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℂ) = 1 + y + y ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hs] at hE
    have h3 : 0 ≤ ‖y‖ ^ 3 := by positivity
    have hk : ‖y‖ ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * (3 : ℕ) : ℝ)⁻¹) ≤
        ‖y‖ ^ 3 := by
      norm_num [Nat.factorial]
      nlinarith
    have hZ3 : |Z ω| ^ 3 ≤ c * Z ω ^ 2 := by
      have e : |Z ω| ^ 3 = |Z ω| * Z ω ^ 2 := by rw [← sq_abs]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hω (sq_nonneg _)
    have hv3 : 0 ≤ |v| ^ 3 := by positivity
    calc _ ≤ _ := hE
      _ ≤ ‖y‖ ^ 3 := hk
      _ = |v| ^ 3 * |Z ω| ^ 3 := by rw [hny, mul_pow]
      _ ≤ |v| ^ 3 * (c * Z ω ^ 2) := mul_le_mul_of_nonneg_left hZ3 hv3
      _ = |v| ^ 3 * c * Z ω ^ 2 := by ring
  have hgi : Integrable (fun ω => |v| ^ 3 * c * Z ω ^ 2) P := hZ2i.const_mul _
  calc _ = ‖∫ ω, (cexp ((v : ℂ) * (Z ω : ℂ) * I) - ((1 : ℂ) + (v : ℂ) * (Z ω : ℂ) * I +
        ((v : ℂ) * (Z ω : ℂ) * I) ^ 2 / 2)) ∂P‖ := by
        rw [integral_sub hexpi hpolyi, hpi]
    _ ≤ ∫ ω, |v| ^ 3 * c * Z ω ^ 2 ∂P := norm_integral_le_of_norm_le hgi hbound
    _ = |v| ^ 3 * c * ∫ ω, Z ω ^ 2 ∂P := integral_const_mul _ _

/-- One row of the array: the error in `M (φ(u/√M) - 1) ≈ -E Z² u² / 2`. -/
theorem step_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : Measurable Z) {c : ℝ} (hb : ∀ᵐ ω ∂P, |Z ω| ≤ c)
    (h0 : ∫ ω, Z ω ∂P = 0) {M : ℕ} (hM : 0 < M) (u : ℝ)
    (hcu : |u| * (c / Real.sqrt M) < 1) :
    ‖(M : ℂ) * (charFun (P.map Z) ((Real.sqrt M)⁻¹ * u) - 1) -
        ((-((∫ ω, Z ω ^ 2 ∂P) * u ^ 2) / 2 : ℝ) : ℂ)‖ ≤
      |u| ^ 3 * (c / Real.sqrt M) * ∫ ω, Z ω ^ 2 ∂P := by
  set s := Real.sqrt (M : ℝ) with hs
  set m2 := ∫ ω, Z ω ^ 2 ∂P with hm2
  have hs0 : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast hM)
  have hs2 : s ^ 2 = (M : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  set v := s⁻¹ * u with hv
  have hvc : |v| * c ≤ 1 := by
    have : |v| * c = |u| * (c / s) := by
      rw [hv, abs_mul, abs_inv, abs_of_pos hs0]; ring
    rw [this]; exact hcu.le
  have hB := norm_charFun_sub_le hZ hb h0 hvc
  have hMv2 : (M : ℝ) * v ^ 2 = u ^ 2 := by
    rw [hv, ← hs2, mul_pow, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hs0.ne'),
      one_mul]
  have hMv3 : (M : ℝ) * |v| ^ 3 = |u| ^ 3 / s := by
    rw [hv, abs_mul, abs_inv, abs_of_pos hs0, ← hs2]
    have : s ≠ 0 := hs0.ne'
    field_simp
  have hMv2c : (M : ℂ) * (v : ℂ) ^ 2 = (u : ℂ) ^ 2 := by exact_mod_cast hMv2
  have heq : (M : ℂ) * (charFun (P.map Z) v - 1) - ((-(m2 * u ^ 2) / 2 : ℝ) : ℂ) =
      (M : ℂ) * (charFun (P.map Z) v - ((1 - v ^ 2 * m2 / 2 : ℝ) : ℂ)) := by
    push_cast
    linear_combination (-(m2 : ℂ) / 2) * hMv2c
  rw [heq, norm_mul, Complex.norm_natCast]
  calc (M : ℝ) * ‖charFun (P.map Z) v - ((1 - v ^ 2 * m2 / 2 : ℝ) : ℂ)‖
      ≤ (M : ℝ) * (|v| ^ 3 * c * m2) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
    _ = ((M : ℝ) * |v| ^ 3) * c * m2 := by ring
    _ = |u| ^ 3 * (c / s) * m2 := by rw [hMv3]; ring

/-- **C4 (triangular CLT, charFun form).** Rows of `M n` iid copies of a centred variable `Z n`
with `|Z n| ≤ c n`, `E (Z n)² → s2`, `M n → ∞`, `c n / √(M n) → 0`:
`φ_{Z n}(u / √(M n))^{M n} → exp(-s2 u² / 2)`. -/
theorem triangularCLT_charFun (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)] (Z : ∀ n, Ω n → ℝ)
    (c : ℕ → ℝ) (Mn : ℕ → ℕ) (s2 : ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hb : ∀ n, ∀ᵐ ω ∂P n, |Z n ω| ≤ c n)
    (h0 : ∀ n, ∫ ω, Z n ω ∂P n = 0)
    (h2 : Tendsto (fun n => ∫ ω, Z n ω ^ 2 ∂P n) atTop (𝓝 s2))
    (hM : Tendsto Mn atTop atTop) (hc : Tendsto (fun n => c n / Real.sqrt (Mn n)) atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => charFun ((P n).map (Z n)) ((Real.sqrt (Mn n))⁻¹ * u) ^ Mn n)
      atTop (𝓝 (Complex.exp (-(s2 * u ^ 2 : ℝ) / 2))) := by
  apply tendsto_pow_exp_of_tendsto_mul_sub_one hM
  have hmain : Tendsto (fun n => ((-((∫ ω, Z n ω ^ 2 ∂P n) * u ^ 2) / 2 : ℝ) : ℂ)) atTop
      (𝓝 ((-(s2 * u ^ 2) / 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (((h2.mul_const _).neg).div_const 2)
  have hbd : Tendsto (fun n => |u| ^ 3 * (c n / Real.sqrt (Mn n)) * ∫ ω, Z n ω ^ 2 ∂P n)
      atTop (𝓝 0) := by
    have h5 := (hc.const_mul (|u| ^ 3)).mul h2
    rwa [mul_zero, zero_mul] at h5
  have hcv : ∀ᶠ n in atTop, |u| * (c n / Real.sqrt (Mn n)) < 1 := by
    have h6 := hc.const_mul |u|
    rw [mul_zero] at h6
    exact h6.eventually (gt_mem_nhds one_pos)
  have hrem : Tendsto (fun n => (Mn n : ℂ) * (charFun ((P n).map (Z n))
      ((Real.sqrt (Mn n))⁻¹ * u) - 1) - ((-((∫ ω, Z n ω ^ 2 ∂P n) * u ^ 2) / 2 : ℝ) : ℂ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [hM.eventually_gt_atTop 0, hcv] with n hn hcn
    exact step_bound (hZ n) (hb n) (h0 n) hn u hcn
  have h7 := hrem.add hmain
  simp only [sub_add_cancel, zero_add] at h7
  convert h7 using 2
  push_cast
  ring

end NetTraffic.OnOffFBM.Lib

end F05Part8

-- ==== part Fidi3_part.lean ====
section F05Part9

/-! ### C4c: finite-dimensional convergence of `Gnorm` (characteristic functions). -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Fidi3

/-- The cumulative input as a sum of the bounded centred workloads plus the mean drift. -/
theorem A_eq_sum_Ghat {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Fon Foff : Measure ℝ} (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    {M : ℕ} {src : ℕ → Source Ω} (hmodel : IsOnOffSuperposition P Fon Foff M src) (p : ℝ) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, 0 ≤ x → (∀ m ∈ Finset.range M, ∀ u, 0 ≤ u → P[(src m).W u] = p) →
      A M src x ω = ∑ m ∈ Finset.range M, Ghat (src m) p x ω + M * x * p := by
  have hgood : ∀ᵐ ω ∂P, ∀ m ∈ Finset.range M, Good (src m) ω := by
    rw [Finset.eventually_all]
    intro m hm
    exact good_ae (hmodel.source m (Finset.mem_range.1 hm)) hon0 hoff0
  filter_upwards [hgood] with ω hω x hx _
  have hII : ∀ m ∈ Finset.range M, IntervalIntegrable (fun u => What (src m) u ω) volume 0 x :=
    fun m hm => (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2
      (Integrable.of_bound (((What_measurable2 (hmodel.source m (Finset.mem_range.1 hm))).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (What_nonneg _ _ _)]; exact What_le_one _ _ _))
  unfold A N
  have h1 : ∫ u in (0:ℝ)..x, ∑ m ∈ Finset.range M, (src m).W u ω =
      ∫ u in (0:ℝ)..x, ∑ m ∈ Finset.range M, What (src m) u ω := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hx] at hu
    exact Finset.sum_congr rfl fun m hm => W_eq_What (hω m hm) hu.1
  rw [h1, intervalIntegral.integral_finsetSum hII]
  have h2 : ∀ m ∈ Finset.range M, Ghat (src m) p x ω = (∫ u in (0:ℝ)..x, What (src m) u ω) - x * p := by
    intro m hm
    unfold Ghat
    rw [intervalIntegral.integral_sub (hII m hm) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

theorem sum_rearr {ι κ : Type*} [Fintype ι] (s : Finset κ) (c : ι → ℝ) (G : κ → ι → ℝ) (a b : ℝ) :
    ∑ i, c i * ((∑ m ∈ s, G m i) / (a * b)) = ∑ m ∈ s, b⁻¹ * ((∑ i, c i * G m i) / a) := by
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **C4 (fidi convergence, charFun form)**: for times `t i` and weights `c i`,
`E exp(i Σ c_i Gnorm(t_i)) → exp(-σ₀² Σ c_i c_j covH(t_i,t_j)/2)`. -/
theorem fidi_charFun {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ} (hM : SourceCount M)
    (hC2 : Condition2 Fon M) {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)]
    {P : ∀ T, Measure (Ω T)} [∀ T, IsProbabilityMeasure (P T)] {src : ∀ T, ℕ → Source (Ω T)}
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T))
    {Tn : ℕ → ℝ} (hTn : Tendsto Tn atTop atTop) {ι : Type*} [Fintype ι] (t : ι → ℝ≥0)
    (c : ι → ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I *
        ↑(∑ i, c i * Gnorm Fon Foff α M (src (Tn n)) (Tn n) (t i) ω)) ∂(P (Tn n))) atTop
      (𝓝 (Complex.exp (-(sigma0sq Fon Foff α *
        ∑ i, ∑ j, c i * c j * covH (hurst α) (t i) (t j) : ℝ) / 2))) := by
  have hon0 := hF.on_nonneg
  have hoff0 := hF.off_nonneg
  have hα2 : α < 2 := lt_trans hF.lt_off hF.off_lt_two
  have hon := mean_on_pos hF
  have hoff := mean_off_pos hF
  have hion := integrable_id_of_heavy hon0 hF.one_lt hF.sv_on
  have hioff := integrable_id_of_heavy hoff0 (by linarith [hF.one_lt, hF.lt_off]) hF.sv_off
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hm0 : 0 ≤ mean Fon / mu Fon Foff := div_nonneg hon.le hmu.le
  have hm1 : mean Fon / mu Fon Foff ≤ 1 := (div_le_one hmu).2 (by unfold mu; linarith)
  set p := mean Fon / mu Fon Foff with hp
  set Nf : ℝ → ℝ := fun T => T ^ (3 - α) * Lsv Fon α T with hNf
  have hNpos : ∀ T, 0 < T → 0 < Nf T := fun T hT => by
    simp only [hNf]
    unfold Lsv
    exact mul_pos (Real.rpow_pos_of_pos hT _)
      (mul_pos (Real.rpow_pos_of_pos hT _) (Fbar_pos_of_sv hF.sv_on T))
  -- a fixed model with at least one source gives the common law `Q0`
  obtain ⟨Ts, hTs⟩ := (hM.tendsto.eventually_gt_atTop 0).exists
  have hs0 : IsOnOffSource (P Ts) Fon Foff (src Ts 0) := (hmodel Ts).source 0 hTs
  set Q0 : Measure SE := (P Ts).map (famvec (src Ts 0)) with hQ0
  have hQ0p : IsProbabilityMeasure Q0 :=
    Measure.isProbabilityMeasure_map (famvec_measurable hs0).aemeasurable
  have hc : IsOnOffSource Q0 Fon Foff canonE := canonE_isOnOff hs0
  set T' : ℕ → ℝ := fun n => max (Tn n) 1 with hT'
  have hT'1 : ∀ n, 1 ≤ T' n := fun n => le_max_right _ _
  have hT'0 : ∀ n, 0 < T' n := fun n => lt_of_lt_of_le one_pos (hT'1 n)
  have hT'lim : Tendsto T' atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) hTn
  set Z : ℕ → SE → ℝ := fun n e =>
    (∑ i, c i * Ghat canonE p (T' n * t i) e) / Real.sqrt (Nf (T' n)) with hZ
  set cc : ℕ → ℝ := fun n => (∑ i, |c i| * (T' n * t i)) / Real.sqrt (Nf (T' n)) with hcc
  set s2 : ℝ := sigma0sq Fon Foff α * ∑ i, ∑ j, c i * c j * covH (hurst α) (t i) (t j) with hs2
  have hti : ∀ n i, 0 ≤ T' n * (t i : ℝ) := fun n i => mul_nonneg (hT'0 n).le (t i).2
  have hZm : ∀ n, Measurable (Z n) := fun n =>
    (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (Ghat_measurable hc p (hti n i))).div_const _
  have hZb : ∀ n, ∀ᵐ e ∂Q0, |Z n e| ≤ cc n := fun n => Eventually.of_forall fun e => by
    simp only [hZ, hcc]
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (hNpos _ (hT'0 n)))]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Ghat_abs_le canonE hm0 hm1 (hti n i) e) (abs_nonneg _)
  have hZ0 : ∀ n, ∫ e, Z n e ∂Q0 = 0 := fun n => by
    simp only [hZ]
    rw [integral_div, integral_finsetSum _ fun i _ =>
      (Ghat_integrable hc hm0 hm1 (hti n i)).const_mul _]
    have hI : ∀ i, ∫ e, Ghat canonE p (T' n * t i) e ∂Q0 = 0 := fun i =>
      integral_Ghat hon0 hoff0 hon hoff hion hioff hc (hti n i)
    rw [Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hI i, mul_zero], zero_div]
  have hZ2 : Tendsto (fun n => ∫ e, Z n e ^ 2 ∂Q0) atTop (𝓝 s2) := by
    have h := (fidi_second_moment hF hon hoff hion hioff hc (fun i => (t i : ℝ)) (fun i => (t i).2)
      c).comp hT'lim
    refine h.congr fun n => ?_
    simp only [Function.comp, hZ]
    have hae : (fun e => (∑ i, c i * canonE.G Q0 (T' n * t i) e) ^ 2) =ᵐ[Q0]
        fun e => (∑ i, c i * Ghat canonE p (T' n * t i) e) ^ 2 := by
      filter_upwards [G_ae_eq hon0 hoff0 hon hoff hion hioff hc] with e he
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [he _ (hti n i)]
    rw [integral_congr_ae hae]
    simp_rw [div_pow, Real.sq_sqrt (hNpos _ (hT'0 n)).le]
    rw [integral_div]
  have hMn : Tendsto (fun n => M (Tn n)) atTop atTop := hM.tendsto.comp hTn
  have hcc0 : Tendsto (fun n => cc n / Real.sqrt (M (Tn n))) atTop (𝓝 0) := by
    have hd := ((tendsto_dT_div_T hF hC2).comp hTn).inv_tendsto_atTop
    have h := hd.const_mul (∑ i, |c i| * (t i : ℝ))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hTn.eventually_ge_atTop 1] with n hn
    have hTe : T' n = Tn n := max_eq_left hn
    have hT0 : 0 < Tn n := lt_of_lt_of_le one_pos hn
    simp only [Function.comp, hcc, hTe, Pi.inv_apply]
    have hdT : dT Fon α M (Tn n) = Real.sqrt (Nf (Tn n)) * Real.sqrt (M (Tn n)) := by
      unfold dT; rw [Real.sqrt_mul (hNpos _ hT0).le]
    rw [hdT, inv_div, Finset.sum_mul, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    try ring
  have hclt := triangularCLT_charFun (fun _ => SE) (fun _ => Q0) Z cc (fun n => M (Tn n)) s2
    hZm hZb hZ0 hZ2 hMn hcc0 1
  simp only [one_pow, mul_one] at hclt
  refine hclt.congr' ?_
  filter_upwards [hTn.eventually_ge_atTop 1, (hM.tendsto.comp hTn).eventually_gt_atTop 0] with n hn hMpos
  have hTe : T' n = Tn n := max_eq_left hn
  have hT0 : 0 < Tn n := lt_of_lt_of_le one_pos hn
  simp only [Function.comp] at hMpos
  set T := Tn n with hTdef
  set m := M T with hmdef
  have hmod := hmodel T
  have hsrc0 : IsOnOffSource (P T) Fon Foff (src T 0) := hmod.source 0 hMpos
  have hlaw : (P T).map (famvec (src T 0)) = Q0 := law_famvec hsrc0 hs0
  -- the integrand as an iid sum
  set h : SE → ℝ := fun e => (Real.sqrt m)⁻¹ * Z n e with hh
  have hhm : Measurable h := measurable_const.mul (hZm n)
  have hpt : ∀ᵐ ω ∂(P T), ∑ i, c i * Gnorm Fon Foff α M (src T) T (t i) ω =
      ∑ k ∈ Finset.range m, h (famvec (src T k) ω) := by
    filter_upwards [A_eq_sum_Ghat hon0 hoff0 hmod p] with ω hω
    have hmean : ∀ k ∈ Finset.range m, ∀ u, 0 ≤ u → (P T)[(src T k).W u] = p := fun k hk u hu =>
      mean_W hon0 hoff0 hon hoff hion hioff (hmod.source k (Finset.mem_range.1 hk)) hu
    have hG : ∀ i, Gnorm Fon Foff α M (src T) T (t i) ω =
        (∑ k ∈ Finset.range m, Ghat (src T k) p (T * t i) ω) /
          (Real.sqrt (Nf T) * Real.sqrt m) := by
      intro i
      unfold Gnorm
      rw [hω (T * t i) (mul_nonneg hT0.le (t i).2) hmean]
      have hdT : dT Fon α M T = Real.sqrt (Nf T) * Real.sqrt m := by
        unfold dT; rw [Real.sqrt_mul (hNpos _ hT0).le]
      rw [hdT]
      congr 1
      rw [hp]
      ring
    simp_rw [hG]
    rw [sum_rearr (Finset.range m) c (fun k i => Ghat (src T k) p (T * t i) ω)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hh, hZ, hTe]
    rfl
  rw [integral_congr_ae (hpt.mono fun ω hω => by rw [hω]),
    integral_exp_sum_iid hmod hMpos h hhm, hlaw, charFun_apply_real,
    integral_map (φ := Z n) (hZm n).aemeasurable
      (f := fun x : ℝ => Complex.exp (↑((Real.sqrt m)⁻¹) * ↑x * Complex.I))
      (Continuous.aestronglyMeasurable (by fun_prop))]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  simp only [hh]
  congr 1
  push_cast
  ring

end Fidi3

end NetTraffic.OnOffFBM.Lib

end F05Part9

-- ==== part Tight1_part.lean ====
section F05Part10

/-! ### C5 input: second moments of increments of `Gnorm`, uniformly in `T`. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Tight1

theorem indep_famvec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Fon Foff : Measure ℝ}
    {M : ℕ} {src : ℕ → Source Ω} (hmodel : IsOnOffSuperposition P Fon Foff M src) :
    iIndepFun (fun m : Fin M => famvec (src m)) P := by
  have hfun : (fun m : Fin M => famvec (src m)) = fun (m : Fin M) => dataToE ∘ (src m).data :=
    funext fun (m : Fin M) => famvec_eq_data (src m)
  rw [hfun]
  exact hmodel.indep.comp _ fun _ => dataToE_measurable

/-- Second moment of an iid centred bounded sum over the sources. -/
theorem integral_sq_sum_iid {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Fon Foff : Measure ℝ} {M : ℕ} {src : ℕ → Source Ω}
    (hmodel : IsOnOffSuperposition P Fon Foff M src) (hM : 0 < M) (h : SE → ℝ)
    (hh : Measurable h) (C : ℝ) (hb : ∀ e, |h e| ≤ C)
    (h0 : ∫ e, h e ∂(P.map (famvec (src 0))) = 0) :
    ∫ ω, (∑ m ∈ Finset.range M, h (famvec (src m) ω)) ^ 2 ∂P =
      M * ∫ e, h e ^ 2 ∂(P.map (famvec (src 0))) := by
  have hsrc : ∀ m ∈ Finset.range M, IsOnOffSource P Fon Foff (src m) := fun m hm =>
    hmodel.source m (Finset.mem_range.1 hm)
  have hlaw : ∀ m ∈ Finset.range M, P.map (famvec (src m)) = P.map (famvec (src 0)) := fun m hm =>
    law_famvec (hsrc m hm) (hmodel.source 0 hM)
  have hXm : ∀ m ∈ Finset.range M, Measurable (fun ω => h (famvec (src m) ω)) := fun m hm =>
    hh.comp (famvec_measurable (hsrc m hm))
  have hXint : ∀ m ∈ Finset.range M, ∀ k ∈ Finset.range M,
      Integrable (fun ω => h (famvec (src m) ω) * h (famvec (src k) ω)) P := fun m hm k hk =>
    Integrable.of_bound ((hXm m hm).mul (hXm k hk)).aestronglyMeasurable (C * C)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hb _) (hb _) (abs_nonneg _) ((abs_nonneg (h (famvec (src m) ω))).trans (hb _)))
  have hE : ∀ m ∈ Finset.range M, ∫ ω, h (famvec (src m) ω) ∂P = 0 := by
    intro m hm
    rw [← integral_map (famvec_measurable (hsrc m hm)).aemeasurable hh.aestronglyMeasurable,
      hlaw m hm, h0]
  have hE2 : ∀ m ∈ Finset.range M, ∫ ω, h (famvec (src m) ω) * h (famvec (src m) ω) ∂P =
      ∫ e, h e ^ 2 ∂(P.map (famvec (src 0))) := by
    intro m hm
    rw [← hlaw m hm, integral_map (famvec_measurable (hsrc m hm)).aemeasurable
      (hh.pow_const 2).aestronglyMeasurable]
    simp_rw [pow_two]
  have hI := indep_famvec hmodel
  have hind : ∀ m ∈ Finset.range M, ∀ k ∈ Finset.range M, m ≠ k →
      IndepFun (fun ω => h (famvec (src m) ω)) (fun ω => h (famvec (src k) ω)) P := by
    intro m hm k hk hmk
    have hne : (⟨m, Finset.mem_range.1 hm⟩ : Fin M) ≠ ⟨k, Finset.mem_range.1 hk⟩ := by
      intro heq; exact hmk (congrArg Fin.val heq)
    exact (hI.indepFun hne).comp hh hh
  have hsq : ∀ ω, (∑ m ∈ Finset.range M, h (famvec (src m) ω)) ^ 2 =
      ∑ m ∈ Finset.range M, ∑ k ∈ Finset.range M, h (famvec (src m) ω) * h (famvec (src k) ω) := by
    intro ω; rw [sq, Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [integral_finsetSum _ fun m hm => integrable_finsetSum _ fun k hk => hXint m hm k hk]
  have hdiag : ∀ m ∈ Finset.range M, ∫ ω, (∑ k ∈ Finset.range M,
      h (famvec (src m) ω) * h (famvec (src k) ω)) ∂P = ∫ e, h e ^ 2 ∂(P.map (famvec (src 0))) := by
    intro m hm
    rw [integral_finsetSum _ fun k hk => hXint m hm k hk]
    rw [Finset.sum_eq_single m (fun k hk hkm => by
      rw [(hind m hm k hk (Ne.symm hkm)).integral_fun_mul_eq_mul_integral
        (hXm m hm).aestronglyMeasurable (hXm k hk).aestronglyMeasurable, hE m hm, zero_mul])
      (fun hn => absurd hm hn)]
    exact hE2 m hm
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- `Gnorm` as a normalised sum of the bounded centred workloads. -/
theorem Gnorm_eq_sum {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    (hon : 0 < mean Fon) (hoff : 0 < mean Foff)
    (hion : Integrable (fun x : ℝ => x) Fon) (hioff : Integrable (fun x : ℝ => x) Foff)
    {α : ℝ} {M : ℝ → ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {src : ℕ → Source Ω} {T : ℝ} (hT : 0 ≤ T)
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Gnorm Fon Foff α M src T t ω =
      (∑ k ∈ Finset.range (M T), Ghat (src k) (mean Fon / mu Fon Foff) (T * t) ω) /
        dT Fon α M T := by
  filter_upwards [A_eq_sum_Ghat hon0 hoff0 hmod (mean Fon / mu Fon Foff)] with ω hω t
  have hmean : ∀ k ∈ Finset.range (M T), ∀ u, 0 ≤ u → P[(src k).W u] = mean Fon / mu Fon Foff :=
    fun k hk u hu => mean_W hon0 hoff0 hon hoff hion hioff (hmod.source k (Finset.mem_range.1 hk)) hu
  unfold Gnorm
  rw [hω (T * t) (mul_nonneg hT t.2) hmean]
  congr 1
  ring

/-- **Uniform increment bound for `Gnorm`**: `E (Gnorm c - Gnorm a)^2 ≤ C (c - a)^β`, `β > 1`. -/
theorem gnorm_increment_bound {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ}
    (hM : SourceCount M) {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)]
    {P : ∀ T, Measure (Ω T)} [∀ T, IsProbabilityMeasure (P T)] {src : ∀ T, ℕ → Source (Ω T)}
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) {K : ℝ} (hK : 0 < K) :
    ∃ C β T₀ : ℝ, 1 < β ∧ ∀ T, T₀ ≤ T → ∀ a c : ℝ≥0, a ≤ c → (c : ℝ) ≤ K →
      ∫ ω, (Gnorm Fon Foff α M (src T) T c ω - Gnorm Fon Foff α M (src T) T a ω) ^ 2 ∂(P T) ≤
        C * ((c : ℝ) - a) ^ β := by
  have hon0 := hF.on_nonneg
  have hoff0 := hF.off_nonneg
  have hon := mean_on_pos hF
  have hoff := mean_off_pos hF
  have hion := integrable_id_of_heavy hon0 hF.one_lt hF.sv_on
  have hioff := integrable_id_of_heavy hoff0 (by linarith [hF.one_lt, hF.lt_off]) hF.sv_off
  have hmu : 0 < mu Fon Foff := by unfold mu; linarith
  have hm0 : 0 ≤ mean Fon / mu Fon Foff := div_nonneg hon.le hmu.le
  have hm1 : mean Fon / mu Fon Foff ≤ 1 := (div_le_one hmu).2 (by unfold mu; linarith)
  set p := mean Fon / mu Fon Foff with hp
  obtain ⟨Ts, hTs⟩ := (hM.tendsto.eventually_gt_atTop 0).exists
  have hs0 : IsOnOffSource (P Ts) Fon Foff (src Ts 0) := (hmodel Ts).source 0 hTs
  set Q0 : Measure SE := (P Ts).map (famvec (src Ts 0)) with hQ0
  have hQ0p : IsProbabilityMeasure Q0 :=
    Measure.isProbabilityMeasure_map (famvec_measurable hs0).aemeasurable
  have hc : IsOnOffSource Q0 Fon Foff canonE := canonE_isOnOff hs0
  obtain ⟨C, β, T₁, hβ, hbd⟩ := increment_bound_source hF hon hoff hion hioff hc hK
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 (hM.tendsto.eventually_gt_atTop 0)
  refine ⟨C, β, max (max T₁ T₂) 1, hβ, fun T hT a c hac hcK => ?_⟩
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hMpos : 0 < M T := hT₂ T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT)
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
  have hmod := hmodel T
  have hlaw : (P T).map (famvec (src T 0)) = Q0 := law_famvec (hmod.source 0 hMpos) hs0
  have hTa : 0 ≤ T * (a : ℝ) := mul_nonneg hT0.le a.2
  have hTc : 0 ≤ T * (c : ℝ) := mul_nonneg hT0.le c.2
  set D := dT Fon α M T with hD
  set h : SE → ℝ := fun e => (Ghat canonE p (T * c) e - Ghat canonE p (T * a) e) / D with hh
  have hhm : Measurable h :=
    ((Ghat_measurable hc p hTc).sub (Ghat_measurable hc p hTa)).div_const _
  have hhb : ∀ e, |h e| ≤ (T * c + T * a) / |D| := fun e => by
    simp only [hh]
    rw [abs_div]
    refine div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add
      (Ghat_abs_le canonE hm0 hm1 hTc e) (Ghat_abs_le canonE hm0 hm1 hTa e))) (abs_nonneg _)
  have hIc : ∫ e, Ghat canonE p (T * c) e ∂Q0 = 0 := integral_Ghat hon0 hoff0 hon hoff hion hioff hc hTc
  have hIa : ∫ e, Ghat canonE p (T * a) e ∂Q0 = 0 := integral_Ghat hon0 hoff0 hon hoff hion hioff hc hTa
  have hh0 : ∫ e, h e ∂Q0 = 0 := by
    simp only [hh]
    rw [integral_div, integral_sub (Ghat_integrable hc hm0 hm1 hTc) (Ghat_integrable hc hm0 hm1 hTa),
      hIc, hIa, sub_zero, zero_div]
  -- the increment as an iid sum
  have hpt : ∀ᵐ ω ∂(P T), Gnorm Fon Foff α M (src T) T c ω - Gnorm Fon Foff α M (src T) T a ω =
      ∑ k ∈ Finset.range (M T), h (famvec (src T k) ω) := by
    filter_upwards [Gnorm_eq_sum (α := α) hon0 hoff0 hon hoff hion hioff hT0.le hmod] with ω hω
    rw [hω c, hω a, ← sub_div, ← Finset.sum_sub_distrib, Finset.sum_div]
    rfl
  rw [integral_congr_ae (hpt.mono fun ω hω => by rw [hω])]
  rw [integral_sq_sum_iid hmod hMpos h hhm _ hhb (by rw [hlaw]; exact hh0), hlaw]
  -- the one-source second moment is the variance
  have hvar : Var[fun e => canonE.G Q0 (T * c) e - canonE.G Q0 (T * a) e; Q0] =
      ∫ e, (Ghat canonE p (T * c) e - Ghat canonE p (T * a) e) ^ 2 ∂Q0 := by
    have hae : (fun e => canonE.G Q0 (T * c) e - canonE.G Q0 (T * a) e) =ᵐ[Q0]
        fun e => Ghat canonE p (T * c) e - Ghat canonE p (T * a) e := by
      filter_upwards [G_ae_eq hon0 hoff0 hon hoff hion hioff hc] with e he
      rw [he _ hTc, he _ hTa]
    rw [variance_congr hae, variance_of_integral_eq_zero
      (X := fun e => Ghat canonE p (T * c) e - Ghat canonE p (T * a) e)
      (((Ghat_measurable hc p hTc).sub (Ghat_measurable hc p hTa)).aemeasurable)
      (by rw [integral_sub (Ghat_integrable hc hm0 hm1 hTc) (Ghat_integrable hc hm0 hm1 hTa),
        hIc, hIa, sub_zero])]
  have hb2 := hbd T hT1 a c a.2 (NNReal.coe_le_coe.2 hac) hcK
  rw [hvar] at hb2
  have hN : 0 < T ^ (3 - α) * Lsv Fon α T := by
    unfold Lsv
    exact mul_pos (Real.rpow_pos_of_pos hT0 _)
      (mul_pos (Real.rpow_pos_of_pos hT0 _) (Fbar_pos_of_sv hF.sv_on T))
  have hD2 : D ^ 2 = T ^ (3 - α) * Lsv Fon α T * (M T : ℝ) := by
    rw [hD]; unfold dT
    exact Real.sq_sqrt (mul_nonneg hN.le (Nat.cast_nonneg _))
  have hsqh : ∫ e, h e ^ 2 ∂Q0 = (∫ e, (Ghat canonE p (T * c) e - Ghat canonE p (T * a) e) ^ 2 ∂Q0) / D ^ 2 := by
    simp only [hh]
    simp_rw [div_pow]
    rw [integral_div]
  rw [hsqh, hD2]
  have hMr : (0 : ℝ) < M T := Nat.cast_pos.2 hMpos
  rw [mul_div_assoc', div_le_iff₀ (mul_pos hN hMr)]
  calc (M T : ℝ) * ∫ e, (Ghat canonE p (T * c) e - Ghat canonE p (T * a) e) ^ 2 ∂Q0
      ≤ (M T : ℝ) * (C * (T ^ (3 - α) * Lsv Fon α T) * ((c : ℝ) - a) ^ β) :=
        mul_le_mul_of_nonneg_left hb2 hMr.le
    _ = C * ((c : ℝ) - a) ^ β * (T ^ (3 - α) * Lsv Fon α T * (M T : ℝ)) := by ring

end Tight1

end NetTraffic.OnOffFBM.Lib

end F05Part10

-- ==== part Gen.lean ====
section F05Part11

/-! ### C5a: dyadic chaining and the Kolmogorov modulus estimate on `C(ℝ≥0, ℝ)` (Mathlib only). -/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

section Kolm

/-- The dyadic floor point of level `j`. -/
noncomputable def dyf (j : ℕ) (t : ℝ) : ℝ := (⌊t * 2 ^ j⌋₊ : ℝ) / 2 ^ j

lemma dyf_le (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : dyf j t ≤ t := by
  unfold dyf
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

lemma sub_dyf_lt (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : t - dyf j t < 1 / 2 ^ j := by
  unfold dyf
  have h2 : (0:ℝ) < 2 ^ j := by positivity
  have := Nat.lt_floor_add_one (t * 2 ^ j)
  rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h2]
  linarith

lemma tendsto_dyf {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun j => dyf j t) atTop (𝓝 t) := by
  have h1 : Tendsto (fun j : ℕ => (1:ℝ) / 2 ^ j) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 : Tendsto (fun j : ℕ => t - 1 / 2 ^ j) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h2 tendsto_const_nhds
    (fun j => by have := sub_dyf_lt j ht; linarith) (fun j => dyf_le j ht)

lemma floor_two_mul (x : ℝ) (hx : 0 ≤ x) :
    2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ ∧ ⌊2 * x⌋₊ ≤ 2 * ⌊x⌋₊ + 1 := by
  have a1 := Nat.floor_le hx
  have a2 := Nat.lt_floor_add_one x
  have b1 := Nat.floor_le (by linarith : 0 ≤ 2 * x)
  have b2 := Nat.lt_floor_add_one (2 * x)
  have h1 : 2 * ⌊x⌋₊ < ⌊2 * x⌋₊ + 1 := by
    have : ((2 * ⌊x⌋₊ : ℕ) : ℝ) < ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h2 : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
    have : ((⌊2 * x⌋₊ : ℕ) : ℝ) < ((2 * ⌊x⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  omega

lemma dyf_step (f : ℝ → ℝ) (m r : ℝ) (j : ℕ)
    (H : ∀ k : ℕ, ((k:ℝ) + 1) ≤ m * 2 ^ (j+1) →
      |f (((k:ℝ) + 1) / 2 ^ (j+1)) - f ((k:ℝ) / 2 ^ (j+1))| ≤ r ^ (j+1))
    (hr : 0 ≤ r) {t : ℝ} (ht : 0 ≤ t) (htm : t ≤ m) :
    |f (dyf (j+1) t) - f (dyf j t)| ≤ r ^ (j+1) := by
  have hx : 0 ≤ t * 2 ^ j := by positivity
  have hb : t * 2 ^ (j+1) = 2 * (t * 2 ^ j) := by ring
  obtain ⟨h1, h2⟩ := floor_two_mul _ hx
  have e1 : dyf j t = ((2 * ⌊t * 2 ^ j⌋₊ : ℕ) : ℝ) / 2 ^ (j+1) := by
    unfold dyf; push_cast; rw [pow_succ]; field_simp
  have e2 : dyf (j+1) t = ((⌊2 * (t * 2 ^ j)⌋₊ : ℕ) : ℝ) / 2 ^ (j+1) := by
    unfold dyf; rw [hb]
  rcases (show ⌊2 * (t * 2 ^ j)⌋₊ = 2 * ⌊t * 2 ^ j⌋₊ ∨
      ⌊2 * (t * 2 ^ j)⌋₊ = 2 * ⌊t * 2 ^ j⌋₊ + 1 by omega) with h | h
  · rw [e1, e2, h, sub_self, abs_zero]; positivity
  · rw [e1, e2, h]
    have hk := H (2 * ⌊t * 2 ^ j⌋₊) (by
      have := Nat.floor_le (show 0 ≤ 2 * (t * 2 ^ j) by positivity)
      rw [h] at this
      push_cast at this ⊢
      calc (2 * (⌊t * 2 ^ j⌋₊ : ℝ) + 1) ≤ 2 * (t * 2 ^ j) := this
        _ = t * 2 ^ (j+1) := by ring
        _ ≤ m * 2 ^ (j+1) := by gcongr)
    push_cast at hk ⊢
    exact hk

lemma dyf_chain (f : ℝ → ℝ) (hf : Continuous f) (m r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ)
    (H : ∀ j, J ≤ j → ∀ k : ℕ, ((k:ℝ) + 1) ≤ m * 2 ^ j →
      |f (((k:ℝ) + 1) / 2 ^ j) - f ((k:ℝ) / 2 ^ j)| ≤ r ^ j)
    {t : ℝ} (ht : 0 ≤ t) (htm : t ≤ m) :
    |f t - f (dyf J t)| ≤ r ^ (J+1) / (1 - r) := by
  have hstep : ∀ N : ℕ, |f (dyf (N + J) t) - f (dyf J t)| ≤
      ∑ i ∈ Finset.range N, r ^ (J + 1 + i) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := dyf_step f m r (N + J) (H (N + J + 1) (by omega)) hr0 ht htm
      calc |f (dyf (N + 1 + J) t) - f (dyf J t)|
          ≤ |f (dyf (N + J + 1) t) - f (dyf (N + J) t)| + |f (dyf (N + J) t) - f (dyf J t)| := by
            rw [show N + 1 + J = N + J + 1 by omega]; exact abs_sub_le _ _ _
        _ ≤ _ := by rw [show J + 1 + N = N + J + 1 by omega]; linarith
  have hgeo : ∀ N : ℕ, ∑ i ∈ Finset.range N, r ^ (J + 1 + i) ≤ r ^ (J+1) / (1 - r) := by
    intro N
    have : ∑ i ∈ Finset.range N, r ^ (J + 1 + i) =
        ∑ i ∈ Finset.Ico (J+1) (J+1+N), r ^ i := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
    rw [this]
    exact geom_sum_Ico_le_of_lt_one hr0 hr1
  have hlim : Tendsto (fun N => |f (dyf (N + J) t) - f (dyf J t)|) atTop
      (𝓝 (|f t - f (dyf J t)|)) := by
    have h1 : Tendsto (fun N => dyf (N + J) t) atTop (𝓝 t) :=
      (tendsto_dyf ht).comp (tendsto_add_atTop_nat J)
    exact (((hf.tendsto t).comp h1).sub_const _).abs
  exact le_of_tendsto' hlim (fun N => (hstep N).trans (hgeo N))

lemma dyf_modulus (f : ℝ → ℝ) (hf : Continuous f) (m r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ)
    (H : ∀ j, J ≤ j → ∀ k : ℕ, ((k:ℝ) + 1) ≤ m * 2 ^ j →
      |f (((k:ℝ) + 1) / 2 ^ j) - f ((k:ℝ) / 2 ^ j)| ≤ r ^ j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htm : t ≤ m) (hd : t - s ≤ 1 / 2 ^ J) :
    |f t - f s| ≤ 2 * (r ^ (J+1) / (1 - r)) + r ^ J := by
  have h2 : (0:ℝ) < 2 ^ J := by positivity
  have hab : ⌊s * 2 ^ J⌋₊ ≤ ⌊t * 2 ^ J⌋₊ := Nat.floor_le_floor (by gcongr)
  have hba : ⌊t * 2 ^ J⌋₊ ≤ ⌊s * 2 ^ J⌋₊ + 1 := by
    have h1 := Nat.floor_le (mul_nonneg (hs.trans hst) h2.le)
    have h2' := Nat.lt_floor_add_one (s * 2 ^ J)
    have h3 : (t - s) * 2 ^ J ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hd h2.le
      rwa [one_div, inv_mul_cancel₀ h2.ne'] at this
    have : ((⌊t * 2 ^ J⌋₊ : ℕ) : ℝ) < ((⌊s * 2 ^ J⌋₊ + 2 : ℕ) : ℝ) := by
      push_cast; nlinarith
    have : ⌊t * 2 ^ J⌋₊ < ⌊s * 2 ^ J⌋₊ + 2 := by exact_mod_cast this
    omega
  have hcs := dyf_chain f hf m r hr0 hr1 J H hs (hst.trans htm)
  have hct := dyf_chain f hf m r hr0 hr1 J H (hs.trans hst) htm
  have hmid : |f (dyf J t) - f (dyf J s)| ≤ r ^ J := by
    rcases (show ⌊t * 2 ^ J⌋₊ = ⌊s * 2 ^ J⌋₊ ∨ ⌊t * 2 ^ J⌋₊ = ⌊s * 2 ^ J⌋₊ + 1 by omega) with h | h
    · simp only [dyf]; rw [h, sub_self, abs_zero]; positivity
    · have hk := H J le_rfl ⌊s * 2 ^ J⌋₊ (by
        have := Nat.floor_le (mul_nonneg (hs.trans hst) h2.le)
        rw [h] at this; push_cast at this
        calc (⌊s * 2 ^ J⌋₊ : ℝ) + 1 ≤ t * 2 ^ J := this
          _ ≤ m * 2 ^ J := by gcongr)
      simp only [dyf]; rw [h]; push_cast; exact hk
  have e1 := abs_sub_le (f t) (f (dyf J t)) (f s)
  have e2 := abs_sub_le (f (dyf J t)) (f (dyf J s)) (f s)
  rw [abs_sub_comm (f (dyf J s)) (f s)] at e2
  linarith

end Kolm

section KolmE

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

/-- Paths whose modulus of continuity on `[0, m]` at scale `δ` exceeds `η`. -/
def badSet (m δ η : ℝ) : Set C(ℝ≥0, ℝ) :=
  {x | ∃ s t : ℝ≥0, s ≤ t ∧ (t : ℝ) ≤ m ∧ (t : ℝ) - s ≤ δ ∧ η < |x t - x s|}

lemma measurable_eval_sub (s t : ℝ≥0) : Measurable fun x : C(ℝ≥0, ℝ) => x t - x s :=
  ((continuous_eval_const t).sub (continuous_eval_const s)).measurable

lemma isOpen_badSet (m δ η : ℝ) : IsOpen (badSet m δ η) := by
  have : badSet m δ η = ⋃ s : ℝ≥0, ⋃ t : ℝ≥0,
      ⋃ (_ : s ≤ t ∧ (t : ℝ) ≤ m ∧ (t : ℝ) - s ≤ δ), {x : C(ℝ≥0, ℝ) | η < |x t - x s|} := by
    ext x
    simp only [badSet, Set.mem_iUnion, exists_prop, Set.mem_setOf_eq]
    constructor
    · rintro ⟨s, t, h1, h2, h3, h4⟩; exact ⟨s, t, ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨s, t, ⟨h1, h2, h3⟩, h4⟩; exact ⟨s, t, h1, h2, h3, h4⟩
  rw [this]
  refine isOpen_iUnion fun s => isOpen_iUnion fun t => isOpen_iUnion fun _ => ?_
  exact isOpen_lt continuous_const
    ((continuous_eval_const t).sub (continuous_eval_const s)).abs

lemma rpow_half_pow (β : ℝ) (j : ℕ) : (1 / 2 ^ j : ℝ) ^ β = ((1 / 2 : ℝ) ^ β) ^ j := by
  have h : (0:ℝ) ≤ 1 / 2 := by norm_num
  rw [← one_div_pow, ← Real.rpow_natCast, ← Real.rpow_mul h, mul_comm, Real.rpow_mul h,
    Real.rpow_natCast]

/-- **Kolmogorov modulus estimate**, uniform over all laws with the same increment bound. -/
theorem kolm_bad (m C β η ε : ℝ) (hm : 0 ≤ m) (hC : 0 ≤ C) (hβ : 1 < β) (hη : 0 < η)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ μ : Measure C(ℝ≥0, ℝ),
      (∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ m →
        ∫⁻ x, ENNReal.ofReal ((x t - x s) ^ 2) ∂μ ≤ ENNReal.ofReal (C * ((t : ℝ) - s) ^ β)) →
      μ (badSet m δ η) ≤ ENNReal.ofReal ε := by
  set ρ : ℝ := (1 / 2 : ℝ) ^ β with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : 2 * ρ < 1 := by
    have : ρ < (1 / 2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) hβ
    rw [Real.rpow_one] at this; linarith
  set r : ℝ := (1 + 2 * ρ) / 2 with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hr2 : 2 * ρ < r ^ 2 := by rw [hrdef]; nlinarith [sq_nonneg (1 - 2 * ρ)]
  set q : ℝ := 2 * ρ / r ^ 2 with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one (by positivity)]; exact hr2
  -- choose the level `J`
  have hpow : Tendsto (fun J : ℕ => r ^ J) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hpow1 : Tendsto (fun J : ℕ => r ^ (J + 1)) atTop (𝓝 0) :=
    hpow.comp (tendsto_add_atTop_nat 1)
  have hA : Tendsto (fun J : ℕ => 2 * (r ^ (J + 1) / (1 - r)) + r ^ J) atTop (𝓝 0) := by
    simpa using ((hpow1.div_const (1 - r)).const_mul 2).add hpow
  have hB : Tendsto (fun J : ℕ => m * C * q ^ J / (1 - q)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (m * C)).div_const
      (1 - q)
  obtain ⟨J, hJ1, hJ2⟩ :=
    ((hA.eventually (ge_mem_nhds hη)).and (hB.eventually (ge_mem_nhds hε))).exists
  refine ⟨1 / 2 ^ J, by positivity, fun μ hinc => ?_⟩
  -- level sets
  let A : ℕ → ℕ → Set C(ℝ≥0, ℝ) := fun j k =>
    {x | r ^ j < |x ((((k:ℝ) + 1) / 2 ^ j).toNNReal) - x (((k:ℝ) / 2 ^ j).toNNReal)|}
  let L : ℕ → Set C(ℝ≥0, ℝ) := fun j => ⋃ k ∈ Finset.range ⌊m * 2 ^ j⌋₊, A j k
  have hsub : badSet m (1 / 2 ^ J) η ⊆ ⋃ i : ℕ, L (J + i) := by
    intro x hx
    obtain ⟨s, t, hst, htm, hd, hbig⟩ := hx
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, L, A, Set.mem_ofPred_eq, not_lt] at hnot
    set f : ℝ → ℝ := fun u => x u.toNNReal with hfdef
    have hfc : Continuous f := x.continuous.comp continuous_real_toNNReal
    have H : ∀ j, J ≤ j → ∀ k : ℕ, ((k:ℝ) + 1) ≤ m * 2 ^ j →
        |f (((k:ℝ) + 1) / 2 ^ j) - f ((k:ℝ) / 2 ^ j)| ≤ r ^ j := by
      intro j hj k hk
      have hkN : k ∈ Finset.range ⌊m * 2 ^ j⌋₊ := by
        rw [Finset.mem_range]
        have : k + 1 ≤ ⌊m * 2 ^ j⌋₊ := Nat.le_floor (by push_cast; exact hk)
        omega
      have := hnot (j - J) k (by rw [show J + (j - J) = j by omega]; exact hkN)
      rw [show J + (j - J) = j by omega] at this
      exact this
    have hmod := dyf_modulus f hfc m r hr0.le hr1 J H (NNReal.coe_nonneg s) (by exact_mod_cast hst) htm hd
    have e1 : ((s : ℝ)).toNNReal = s := Real.toNNReal_coe
    have e2 : ((t : ℝ)).toNNReal = t := Real.toNNReal_coe
    simp only [hfdef, e1, e2] at hmod
    linarith
  -- one level
  have hlevel : ∀ j : ℕ, μ (L j) ≤ ENNReal.ofReal (m * C * q ^ j) := by
    intro j
    have h2j : (0:ℝ) < 2 ^ j := by positivity
    have hrj : 0 < (r ^ j) ^ 2 := by positivity
    have hAk : ∀ k ∈ Finset.range ⌊m * 2 ^ j⌋₊,
        μ (A j k) ≤ ENNReal.ofReal (C * ρ ^ j / (r ^ j) ^ 2) := by
      intro k hk
      have hk1 : ((k:ℝ) + 1) ≤ m * 2 ^ j := by
        have : k + 1 ≤ ⌊m * 2 ^ j⌋₊ := Finset.mem_range.1 hk
        have := (Nat.le_floor_iff (by positivity : 0 ≤ m * 2 ^ j)).1 this
        push_cast at this; exact this
      have hs0 : (0:ℝ) ≤ (k:ℝ) / 2 ^ j := by positivity
      have ht0 : (0:ℝ) ≤ ((k:ℝ) + 1) / 2 ^ j := by positivity
      have hst : ((k:ℝ) / 2 ^ j).toNNReal ≤ (((k:ℝ) + 1) / 2 ^ j).toNNReal :=
        Real.toNNReal_le_toNNReal (by gcongr; linarith)
      have htm : (((((k:ℝ) + 1) / 2 ^ j).toNNReal : ℝ≥0) : ℝ) ≤ m := by
        rw [Real.coe_toNNReal _ ht0, div_le_iff₀ h2j]; exact hk1
      have hdiff : (((((k:ℝ) + 1) / 2 ^ j).toNNReal : ℝ≥0) : ℝ) -
          ((((k:ℝ) / 2 ^ j).toNNReal : ℝ≥0) : ℝ) = 1 / 2 ^ j := by
        rw [Real.coe_toNNReal _ ht0, Real.coe_toNNReal _ hs0, ← sub_div, add_sub_cancel_left]
      have hi := hinc _ _ hst htm
      rw [hdiff, rpow_half_pow, ← hρdef] at hi
      have hmeas : AEMeasurable (fun x : C(ℝ≥0, ℝ) => ENNReal.ofReal
          ((x (((k:ℝ) + 1) / 2 ^ j).toNNReal - x ((k:ℝ) / 2 ^ j).toNNReal) ^ 2)) μ :=
        (ENNReal.measurable_ofReal.comp
          ((measurable_eval_sub _ _).pow_const 2)).aemeasurable
      have hmk := mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal ((r ^ j) ^ 2))
      have hsubA : A j k ⊆ {x | ENNReal.ofReal ((r ^ j) ^ 2) ≤ ENNReal.ofReal
          ((x (((k:ℝ) + 1) / 2 ^ j).toNNReal - x ((k:ℝ) / 2 ^ j).toNNReal) ^ 2)} := by
        intro x hx
        simp only [A, Set.mem_ofPred_eq] at hx ⊢
        apply ENNReal.ofReal_le_ofReal
        rw [← sq_abs (x _ - x _)]
        exact pow_le_pow_left₀ (by positivity) hx.le 2
      have hm2 : ENNReal.ofReal ((r ^ j) ^ 2) * μ (A j k) ≤ ENNReal.ofReal (C * ρ ^ j) :=
        (by gcongr : _ ≤ _).trans (hmk.trans hi)
      rw [ENNReal.ofReal_div_of_pos hrj, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hrj).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact hm2
    calc μ (L j) ≤ ∑ k ∈ Finset.range ⌊m * 2 ^ j⌋₊, μ (A j k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range ⌊m * 2 ^ j⌋₊, ENNReal.ofReal (C * ρ ^ j / (r ^ j) ^ 2) :=
          Finset.sum_le_sum hAk
      _ = ENNReal.ofReal ((⌊m * 2 ^ j⌋₊ : ℝ) * (C * ρ ^ j / (r ^ j) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (m * C * q ^ j) := by
          apply ENNReal.ofReal_le_ofReal
          have hq : q ^ j = 2 ^ j * ρ ^ j / (r ^ j) ^ 2 := by
            rw [hqdef, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 j]
          rw [hq]
          have hN : (⌊m * 2 ^ j⌋₊ : ℝ) ≤ m * 2 ^ j := Nat.floor_le (by positivity)
          calc (⌊m * 2 ^ j⌋₊ : ℝ) * (C * ρ ^ j / (r ^ j) ^ 2)
              ≤ m * 2 ^ j * (C * ρ ^ j / (r ^ j) ^ 2) :=
                mul_le_mul_of_nonneg_right hN (by positivity)
            _ = m * C * (2 ^ j * ρ ^ j / (r ^ j) ^ 2) := by ring
  have hsum : Summable fun i : ℕ => m * C * q ^ J * q ^ i :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc μ (badSet m (1 / 2 ^ J) η) ≤ μ (⋃ i : ℕ, L (J + i)) := measure_mono hsub
    _ ≤ ∑' i, μ (L (J + i)) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal (m * C * q ^ J * q ^ i) :=
        ENNReal.tsum_le_tsum fun i => by
          rw [show m * C * q ^ J * q ^ i = m * C * q ^ (J + i) by ring]; exact hlevel _
    _ = ENNReal.ofReal (∑' i, m * C * q ^ J * q ^ i) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
    _ = ENNReal.ofReal (m * C * q ^ J / (1 - q)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hJ2

end KolmE

section TightE

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma isClosedEmbedding_toUOF :
    IsClosedEmbedding (UniformOnFun.ofFun {K : Set ℝ≥0 | IsCompact K} ∘
      (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ))) := by
  refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
  have h := ContinuousMap.range_toUniformOnFunIsCompact (α := ℝ≥0) (β := ℝ)
  have e : Set.range (UniformOnFun.ofFun {K : Set ℝ≥0 | IsCompact K} ∘
      (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ))) =
      Set.range ContinuousMap.toUniformOnFunIsCompact := rfl
  rw [e, h]
  exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith

lemma le_of_not_bad {f : C(ℝ≥0, ℝ)} {m δ η : ℝ} (hf : f ∉ badSet m δ η) {s t : ℝ≥0}
    (hst : s ≤ t) (htm : (t : ℝ) ≤ m) (hd : (t : ℝ) - s ≤ δ) : |f t - f s| ≤ η := by
  by_contra h
  exact hf ⟨s, t, hst, htm, hd, not_le.1 h⟩

lemma abs_le_of_not_bad {f : C(ℝ≥0, ℝ)} {m δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hf0 : f 0 = 0)
    (hf : f ∉ badSet m δ η) :
    ∀ k : ℕ, ∀ y : ℝ≥0, (y : ℝ) ≤ m → (y : ℝ) ≤ k * δ → |f y| ≤ k * η := by
  intro k
  induction k with
  | zero =>
    intro y _ hy
    have h1 : (y : ℝ) = 0 := le_antisymm (by simpa using hy) y.2
    have : y = 0 := NNReal.coe_eq_zero.1 h1
    simp [this, hf0]
  | succ k ih =>
    intro y hym hy
    by_cases hyd : (y : ℝ) ≤ δ
    · have := le_of_not_bad hf (zero_le : (0:ℝ≥0) ≤ y) hym (by simp only [NNReal.coe_zero, sub_zero]; exact hyd)
      rw [hf0, sub_zero] at this
      have hk : (0:ℝ) ≤ k * η := by positivity
      push_cast; linarith
    · rw [not_le] at hyd
      set y' : ℝ≥0 := ⟨(y : ℝ) - δ, by linarith⟩ with hy'
      have hy'v : (y' : ℝ) = (y : ℝ) - δ := rfl
      have h1 := ih y' (by rw [hy'v]; linarith) (by rw [hy'v]; push_cast at hy; linarith)
      have hle : y' ≤ y := by
        rw [← NNReal.coe_le_coe, hy'v]; linarith
      have h2 := le_of_not_bad hf hle hym (by rw [hy'v]; linarith)
      have h3 := abs_sub_abs_le_abs_sub (f y) (f y')
      push_cast; linarith

/-- **Tightness in `C(ℝ≥0, ℝ)`** from a uniform modulus estimate (Arzelà-Ascoli). -/
theorem tight_of_modulus (μ : ℕ → Measure C(ℝ≥0, ℝ)) (h0 : ∀ n, μ n {x | x 0 ≠ 0} = 0)
    (hmod : ∀ p : ℕ, ∀ η > 0, ∀ ε > 0, ∃ δ > 0, ∀ n, μ n (badSet p δ η) ≤ ENNReal.ofReal ε) :
    IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he0, hele⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    obtain ⟨e, -, he, he'⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    exact ⟨e, ENNReal.ofReal_pos.1 he, he'.le⟩
  choose δ hδ hδμ using fun p : ℕ =>
    hmod p (1 / ((p:ℝ) + 1)) (by positivity) (e / 2 / 2 ^ p) (by positivity)
  let K : Set C(ℝ≥0, ℝ) := {x | x 0 = 0} ∩ ⋂ p : ℕ, (badSet p (δ p) (1 / ((p:ℝ) + 1)))ᶜ
  refine ⟨closure K, ?_, ?_⟩
  · apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (𝔖 := {K : Set ℝ≥0 | IsCompact K})
      (fun _ h => h) isClosedEmbedding_toUOF
    · intro S _
      apply Equicontinuous.equicontinuousOn
      refine fun x₀ => ?_
      rw [Metric.equicontinuousAt_iff_right]
      intro ε' hε'
      obtain ⟨p, hp⟩ := exists_nat_gt (max ((x₀ : ℝ) + 1) (1 / ε'))
      have hp1 : (x₀ : ℝ) + 1 < p := lt_of_le_of_lt (le_max_left _ _) hp
      have hp2 : 1 / ((p:ℝ) + 1) < ε' := by
        have h3 : 1 / ε' < p + 1 := by linarith [le_max_right ((x₀ : ℝ) + 1) (1 / ε')]
        rw [div_lt_iff₀ hε'] at h3
        rw [div_lt_iff₀ (by positivity)]; linarith
      have hball : Metric.ball x₀ (min (δ p) 1) ∈ 𝓝 x₀ :=
        Metric.ball_mem_nhds _ (lt_min (hδ p) one_pos)
      filter_upwards [hball] with x hx
      rintro ⟨f, hfK⟩
      have hfp : f ∉ badSet p (δ p) (1 / ((p:ℝ) + 1)) := Set.mem_iInter.1 hfK.2 p
      rw [Metric.mem_ball, NNReal.dist_eq] at hx
      have hx1 := lt_of_lt_of_le hx (min_le_left _ _)
      have hx2 := lt_of_lt_of_le hx (min_le_right _ _)
      rw [abs_lt] at hx1 hx2
      simp only [Function.comp_apply]
      rw [Real.dist_eq]
      rcases le_total x₀ x with h | h
      · have := le_of_not_bad hfp h (by linarith) (by linarith)
        rw [abs_sub_comm]; linarith
      · have := le_of_not_bad hfp h (by linarith) (by linarith)
        linarith
    · intro S _ x _
      refine ⟨Metric.closedBall 0 (⌈(x : ℝ) / δ ⌈(x : ℝ)⌉₊⌉₊ * (1 / ((⌈(x : ℝ)⌉₊ : ℝ) + 1))),
        isCompact_closedBall _ _, ?_⟩
      intro f hf
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact abs_le_of_not_bad (hδ _) (by positivity) hf.1 (Set.mem_iInter.1 hf.2 _) _ x
        (Nat.le_ceil _) (by rw [← div_le_iff₀ (hδ _)]; exact Nat.le_ceil _)
  · rintro ν ⟨n, rfl⟩
    calc μ n (closure K)ᶜ ≤ μ n Kᶜ := measure_mono (Set.compl_subset_compl.2 subset_closure)
      _ ≤ μ n {x | x 0 ≠ 0} + μ n (⋃ p : ℕ, badSet p (δ p) (1 / ((p:ℝ) + 1))) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro x hx
          by_cases h : x 0 = 0
          · refine Or.inr ?_
            by_contra hc
            exact hx ⟨h, Set.mem_iInter.2 fun p hp => hc (Set.mem_iUnion.2 ⟨p, hp⟩)⟩
          · exact Or.inl h
      _ ≤ 0 + ∑' p : ℕ, ENNReal.ofReal (e / 2 / 2 ^ p) := by
          rw [h0 n]
          exact add_le_add le_rfl
            ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun p => hδμ p n))
      _ = ENNReal.ofReal e := by
          rw [zero_add, ← ENNReal.ofReal_tsum_of_nonneg (fun p => by positivity)
            (summable_geometric_two' e), tsum_geometric_two']
      _ ≤ ε := hele

lemma badSet_mono {m δ δ' η : ℝ} (h : δ' ≤ δ) : badSet m δ' η ⊆ badSet m δ η := by
  rintro x ⟨s, t, h1, h2, h3, h4⟩
  exact ⟨s, t, h1, h2, h3.trans h, h4⟩

lemma exists_delta_single (ν : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure ν] (m η ε : ℝ) (hη : 0 < η)
    (hε : 0 < ε) : ∃ δ > 0, ν (badSet m δ η) ≤ ENNReal.ofReal ε := by
  have hanti : Antitone fun j : ℕ => badSet m (1 / ((j:ℝ) + 1)) η := by
    intro i j hij
    apply badSet_mono
    gcongr
  have hempty : (⋂ j : ℕ, badSet m (1 / ((j:ℝ) + 1)) η) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    have hcpt : IsCompact (Set.Icc (0:ℝ≥0) m.toNNReal) := isCompact_Icc
    have huc := hcpt.uniformContinuousOn_of_continuous x.continuous.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hd⟩ := huc η hη
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / δ)
    refine ⟨j, ?_⟩
    rintro ⟨s, t, hst, htm, hts, hbig⟩
    have hjδ : 1 / ((j:ℝ) + 1) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at hj
      nlinarith
    have htm0 : t ≤ m.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal']; exact le_max_of_le_left htm
    have htm' : t ∈ Set.Icc (0:ℝ≥0) m.toNNReal := ⟨zero_le, htm0⟩
    have hsm' : s ∈ Set.Icc (0:ℝ≥0) m.toNNReal := ⟨zero_le, le_trans hst htm0⟩
    have hdist : dist t s < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (by simpa using (show (s:ℝ) ≤ t from hst))]; linarith
    have := hd t htm' s hsm' hdist
    rw [Real.dist_eq] at this
    linarith
  have hlim := tendsto_measure_iInter_atTop (μ := ν)
    (fun j : ℕ => (isOpen_badSet m (1 / ((j:ℝ) + 1)) η).measurableSet.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨j, hj⟩ := (hlim.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  exact ⟨1 / ((j:ℝ) + 1), by positivity, hj⟩

lemma exists_delta_finite (μ : ℕ → Measure C(ℝ≥0, ℝ)) [∀ n, IsFiniteMeasure (μ n)] (m η ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (N : ℕ) :
    ∃ δ > 0, ∀ n < N, μ n (badSet m δ η) ≤ ENNReal.ofReal ε := by
  induction N with
  | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    obtain ⟨δ', hδ', h'⟩ := exists_delta_single (μ N) m η ε hη hε
    refine ⟨min δ δ', lt_min hδ hδ', fun n hn => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact (measure_mono (badSet_mono (min_le_left _ _))).trans (h n hn)
    · exact (measure_mono (badSet_mono (min_le_right _ _))).trans h'

/-- Tightness from an eventual Kolmogorov increment bound on every `[0, p]`. -/
theorem tight_of_eventually_kolm (μ : ℕ → Measure C(ℝ≥0, ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    (h0 : ∀ n, μ n {x | x 0 ≠ 0} = 0)
    (hK : ∀ p : ℕ, ∃ C β : ℝ, ∃ N : ℕ, 0 ≤ C ∧ 1 < β ∧ ∀ n, N ≤ n → ∀ s t : ℝ≥0, s ≤ t →
      (t : ℝ) ≤ p → ∫⁻ x, ENNReal.ofReal ((x t - x s) ^ 2) ∂(μ n) ≤
        ENNReal.ofReal (C * ((t : ℝ) - s) ^ β)) :
    IsTightMeasureSet (Set.range μ) := by
  apply tight_of_modulus μ h0
  intro p η hη ε hε
  obtain ⟨C, β, N, hC, hβ, hb⟩ := hK p
  obtain ⟨δ1, hδ1, h1⟩ := kolm_bad p C β η ε (by positivity) hC hβ hη hε
  obtain ⟨δ2, hδ2, h2⟩ := exists_delta_finite μ p η ε hη hε N
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact (measure_mono (badSet_mono (min_le_right _ _))).trans (h2 n hn)
  · exact (measure_mono (badSet_mono (min_le_left _ _))).trans (h1 (μ n) (hb n hn))

end TightE

end NetTraffic.OnOffFBM.Lib

/-! ### Path space `C(ℝ≥0, ℝ)`: the Borel σ-algebra is generated by evaluations (Mathlib only). -/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

section PathE

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

/-- A compact-open subbasic set is described by countably many evaluations. -/
lemma mapsTo_iff_countable (K : Set ℝ≥0) (hK : IsCompact K) (U : Set ℝ) (hU : IsOpen U) :
    ∃ D : Set ℝ≥0, D.Countable ∧ ∃ F : ℕ → Set ℝ, (∀ n, IsClosed (F n)) ∧
      ∀ f : C(ℝ≥0, ℝ), MapsTo f K U ↔ ∃ n, ∀ d ∈ D, f d ∈ F n := by
  obtain ⟨D', hD'c, hD'd⟩ := TopologicalSpace.exists_countable_dense K
  refine ⟨(↑) '' D', hD'c.image _, fun n => ⋂ z ∈ Uᶜ, {y : ℝ | 1 / ((n:ℝ) + 1) ≤ dist y z}, ?_, ?_⟩
  · intro n
    exact isClosed_biInter fun z _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  intro f
  have hFU : ∀ n : ℕ, ∀ y, y ∈ (⋂ z ∈ Uᶜ, {y : ℝ | 1 / ((n:ℝ) + 1) ≤ dist y z}) → y ∈ U := by
    intro n y hy
    by_contra hyU
    have := (mem_iInter₂.1 hy) y hyU
    simp only [mem_setOf_eq, dist_self] at this
    have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    linarith
  constructor
  · intro hmap
    have hcpt : IsCompact (f '' K) := hK.image f.continuous
    obtain ⟨δ, hδ, hsub⟩ := hcpt.exists_cthickening_subset_open hU (mapsTo_iff_image_subset.1 hmap)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
    refine ⟨n, fun d hd => ?_⟩
    obtain ⟨d', _, rfl⟩ := hd
    refine mem_iInter₂.2 fun z hz => ?_
    simp only [mem_setOf_eq]
    by_contra hlt
    rw [not_le] at hlt
    have hle : dist z (f d') ≤ δ := by
      rw [dist_comm]
      have h1 : 1 / ((n:ℝ) + 1) < δ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hδ] at hn
        nlinarith
      linarith
    exact hz (hsub (Metric.mem_cthickening_of_dist_le z (f d') δ _ ⟨d', d'.2, rfl⟩ hle))
  · rintro ⟨n, hn⟩ x hx
    apply hFU n
    have hcl : IsClosed {y : K | f y ∈ ⋂ z ∈ Uᶜ, {y : ℝ | 1 / ((n:ℝ) + 1) ≤ dist y z}} :=
      (isClosed_biInter fun z _ => isClosed_le continuous_const
        (continuous_id.dist continuous_const)).preimage (f.continuous.comp continuous_subtype_val)
    have hsub : D' ⊆ {y : K | f y ∈ ⋂ z ∈ Uᶜ, {y : ℝ | 1 / ((n:ℝ) + 1) ≤ dist y z}} :=
      fun y hy => hn y ⟨y, hy, rfl⟩
    have := closure_minimal hsub hcl
    rw [hD'd.closure_eq] at this
    exact this (mem_univ (⟨x, hx⟩ : K))

/-- The Borel σ-algebra of `C(ℝ≥0, ℝ)` is contained in the one induced by the product σ-algebra. -/
theorem borel_le_comap_coe :
    (borel C(ℝ≥0, ℝ)) ≤ MeasurableSpace.comap (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ))
      MeasurableSpace.pi := by
  rw [borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨K, hK, U, hU, rfl⟩
  obtain ⟨D, hDc, F, hF, hiff⟩ := mapsTo_iff_countable K hK U hU
  refine ⟨⋃ n, ⋂ d ∈ D, {g : ℝ≥0 → ℝ | g d ∈ F n}, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => MeasurableSet.biInter hDc fun d _ =>
      (measurable_pi_apply d) (hF n).measurableSet
  · ext f
    simp only [mem_preimage, mem_iUnion, mem_iInter, mem_setOf_eq]
    exact (hiff f).symm

lemma measurable_coe_path : Measurable (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) :=
  measurable_pi_iff.2 fun t => (continuous_eval_const t).measurable

/-- A map into `C(ℝ≥0, ℝ)` is measurable as soon as all its evaluations are. -/
theorem measurable_toPath {Ω : Type*} [MeasurableSpace Ω] (Φ : Ω → C(ℝ≥0, ℝ))
    (h : ∀ t, Measurable fun ω => Φ ω t) : Measurable Φ := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := borel_le_comap_coe A hA
  exact (measurable_pi_iff.2 h) hB

/-- Finite measures on `C(ℝ≥0, ℝ)` with equal finite-dimensional laws are equal. -/
theorem ext_of_fidi (ν ν' : Measure C(ℝ≥0, ℝ)) [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ∀ s : Finset ℝ≥0, ν.map (fun f : C(ℝ≥0, ℝ) => fun i : s => f i) =
      ν'.map (fun f : C(ℝ≥0, ℝ) => fun i : s => f i)) : ν = ν' := by
  have hres : ∀ s : Finset ℝ≥0, Measurable (fun f : C(ℝ≥0, ℝ) => fun i : s => f i) :=
    fun s => measurable_pi_iff.2 fun i => (continuous_eval_const (i : ℝ≥0)).measurable
  have hmap : ν.map (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) =
      ν'.map (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) := by
    refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : ℝ≥0 => ℝ)
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
    · intro c hc
      obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders c).1 hc
      have hcyl : MeasurableSet (cylinder (α := fun _ : ℝ≥0 => ℝ) s S) := MeasurableSet.cylinder s hS
      rw [Measure.map_apply measurable_coe_path hcyl, Measure.map_apply measurable_coe_path hcyl]
      have e1 := congrArg (fun m => m S) (h s)
      try simp only at e1
      rw [Measure.map_apply (hres s) hS, Measure.map_apply (hres s) hS] at e1
      exact e1
    · rw [Measure.map_apply measurable_coe_path MeasurableSet.univ,
        Measure.map_apply measurable_coe_path MeasurableSet.univ]
      have e1 := congrArg (fun m => m univ) (h ∅)
      try simp only at e1
      rw [Measure.map_apply (hres ∅) MeasurableSet.univ,
        Measure.map_apply (hres ∅) MeasurableSet.univ] at e1
      simpa using e1
  ext A hA
  obtain ⟨B, hB, rfl⟩ := borel_le_comap_coe A hA
  rw [← Measure.map_apply measurable_coe_path hB, ← Measure.map_apply measurable_coe_path hB, hmap]

end PathE

end NetTraffic.OnOffFBM.Lib

end F05Part11

-- ==== part Tight2_part.lean ====
section F05Part12

/-! ### C5 for the model: continuous path version, its law on `C(ℝ≥0, ℝ)`, tightness. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Tight2

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem What_sub_intervalIntegrable {Fon Foff : Measure ℝ} {s : Source Ω}
    (hs : IsOnOffSource P Fon Foff s) (p : ℝ) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun u => What s u ω - p) volume a b := by
  have hm : Measurable fun u => What s u ω - p :=
    ((What_measurable2 hs).comp (measurable_id.prodMk measurable_const)).sub measurable_const
  refine (intervalIntegrable_const (c := (1 + |p|))).mono_fun hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + |p|)]
  have h0 := What_nonneg s u ω
  have h1 := What_le_one s u ω
  rw [abs_le]; constructor <;> linarith [abs_nonneg p, le_abs_self p, neg_abs_le p]

theorem Ghat_continuous {Fon Foff : Measure ℝ} {s : Source Ω} (hs : IsOnOffSource P Fon Foff s)
    (p : ℝ) (ω : Ω) : Continuous fun T => Ghat s p T ω := by
  unfold Ghat
  exact intervalIntegral.continuous_primitive (What_sub_intervalIntegrable hs p ω) 0

theorem Ghat_abs_le' (s : Source Ω) (p T : ℝ) (ω : Ω) : |Ghat s p T ω| ≤ (1 + |p|) * |T| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := T)
    (f := fun u => What s u ω - p) (C := 1 + |p|) fun u _ => by
      rw [Real.norm_eq_abs]
      have h0 := What_nonneg s u ω
      have h1 := What_le_one s u ω
      rw [abs_le]; constructor <;> linarith [abs_nonneg p, le_abs_self p, neg_abs_le p]
  simpa [Ghat, sub_zero] using h

theorem Ghat_zero' (s : Source Ω) (p : ℝ) (ω : Ω) : Ghat s p 0 ω = 0 := by
  simp [Ghat]

/-- The continuous version of the normalised input path (`T < 0`: the a.s. linear path). -/
noncomputable def Gv (Fon Foff : Measure ℝ) (α : ℝ) (M : ℝ → ℕ) (src : ℕ → Source Ω) (T : ℝ)
    (ω : Ω) (t : ℝ≥0) : ℝ :=
  if 0 ≤ T then
    (∑ k ∈ Finset.range (M T), Ghat (src k) (mean Fon / mu Fon Foff) (T * t) ω) / dT Fon α M T
  else -(T * (M T : ℝ) * (mu Fon Foff)⁻¹ * mean Fon * t) / dT Fon α M T

theorem Gv_continuous {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) (ω : Ω) :
    Continuous (Gv Fon Foff α M src T ω) := by
  change Continuous (fun t : ℝ≥0 => Gv Fon Foff α M src T ω t)
  by_cases h : 0 ≤ T
  · simp only [Gv, h, if_true]
    exact (continuous_finset_sum _ fun k hk =>
      (Ghat_continuous (hmod.source k (Finset.mem_range.1 hk)) _ ω).comp
        (continuous_const.mul NNReal.continuous_coe)).div_const _
  · simp only [Gv, h, if_false]
    exact ((continuous_const.mul NNReal.continuous_coe).neg).div_const _

theorem Gv_measurable {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) (t : ℝ≥0) :
    Measurable fun ω => Gv Fon Foff α M src T ω t := by
  by_cases h : 0 ≤ T
  · simp only [Gv, h, if_true]
    exact (Finset.measurable_sum _ fun k hk =>
      Ghat_measurable (hmod.source k (Finset.mem_range.1 hk)) _ (mul_nonneg h t.2)).div_const _
  · simp only [Gv, h, if_false]
    exact measurable_const

theorem Gv_zero (Fon Foff : Measure ℝ) (α : ℝ) (M : ℝ → ℕ) (src : ℕ → Source Ω) (T : ℝ)
    (ω : Ω) : Gv Fon Foff α M src T ω 0 = 0 := by
  by_cases h : 0 ≤ T
  · simp [Gv, h, Ghat_zero']
  · simp [Gv, h]

/-- The continuous path, as an element of `C(ℝ≥0, ℝ)`. -/
noncomputable def pathV {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨Gv Fon Foff α M src T ω, Gv_continuous hmod ω⟩

theorem pathV_apply {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) (ω : Ω) (t : ℝ≥0) :
    pathV (α := α) hmod ω t = Gv Fon Foff α M src T ω t := rfl

theorem pathV_measurable {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) : Measurable (pathV (α := α) hmod) :=
  measurable_toPath _ fun t => Gv_measurable hmod t

theorem W_neg {s : Source Ω} {ω : Ω} (hω : Good s ω) {u : ℝ} (hu : u < 0) : s.W u ω = 0 := by
  unfold Source.W
  have hT0 : 0 ≤ s.T0 ω := by
    obtain ⟨hB, hX0, hY0, hYoff, -⟩ := hω
    unfold Source.T0
    rcases hB with h | h <;> rw [h] <;> nlinarith
  have hTn : ∀ n, 0 ≤ s.Tn n ω := fun n => by
    unfold Source.Tn
    exact add_nonneg hT0 (Finset.sum_nonneg fun i _ =>
      add_nonneg (hω.2.2.2.2 i).1 (hω.2.2.2.2 i).2)
  have h1 : (Set.Ico 0 (s.X0 ω)).indicator (fun _ => (1:ℝ)) u = 0 :=
    Set.indicator_of_notMem (fun h => by linarith [h.1]) _
  have h2 : ∀ n, (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator (fun _ => (1:ℝ)) u = 0 :=
    fun n => Set.indicator_of_notMem (fun h => by linarith [h.1, hTn n]) _
  simp [h1, h2]

theorem A_nonpos {Fon Foff : Measure ℝ} (hon0 : Fon (Set.Iio 0) = 0) (hoff0 : Foff (Set.Iio 0) = 0)
    {M : ℕ} {src : ℕ → Source Ω} (hmod : IsOnOffSuperposition P Fon Foff M src) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, x ≤ 0 → A M src x ω = 0 := by
  have hgood : ∀ᵐ ω ∂P, ∀ m ∈ Finset.range M, Good (src m) ω := by
    rw [Finset.eventually_all]
    intro m hm
    exact good_ae (hmod.source m (Finset.mem_range.1 hm)) hon0 hoff0
  filter_upwards [hgood] with ω hω x hx
  unfold A
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := ae_iff.2 (by simp)
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ)) ?_, intervalIntegral.integral_zero]
  filter_upwards [hne] with u hu hmem
  rw [Set.uIoc_of_le hx] at hmem
  have hlt : u < 0 := lt_of_le_of_ne hmem.2 hu
  exact Finset.sum_eq_zero fun m hm => W_neg (hω m hm) hlt

theorem Gnorm_eq_Gv {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ} [IsProbabilityMeasure P]
    {src : ℕ → Source Ω} {T : ℝ} (hmod : IsOnOffSuperposition P Fon Foff (M T) src) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Gnorm Fon Foff α M src T t ω = Gv Fon Foff α M src T ω t := by
  have hon0 := hF.on_nonneg
  have hoff0 := hF.off_nonneg
  have hon := mean_on_pos hF
  have hoff := mean_off_pos hF
  have hion := integrable_id_of_heavy hon0 hF.one_lt hF.sv_on
  have hioff := integrable_id_of_heavy hoff0 (by linarith [hF.one_lt, hF.lt_off]) hF.sv_off
  by_cases hT : 0 ≤ T
  · filter_upwards [Gnorm_eq_sum hon0 hoff0 hon hoff hion hioff hT hmod] with ω hω t
    rw [hω t]
    simp only [Gv, hT, if_true]
  · filter_upwards [A_nonpos hon0 hoff0 hmod] with ω hω t
    simp only [Gv, hT, if_false]
    unfold Gnorm
    rw [hω (T * t) (by have := t.2; have := (not_le.1 hT).le; nlinarith)]
    ring

theorem Gv_abs_le {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hT : 0 ≤ T) (ω : Ω) (t : ℝ≥0) :
    |Gv Fon Foff α M src T ω t| ≤ (M T : ℝ) * ((1 + |mean Fon / mu Fon Foff|) * |T * t|) /
      |dT Fon α M T| := by
  simp only [Gv, hT, if_true]
  rw [abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.range (M T))
    (fun k => |Ghat (src k) (mean Fon / mu Fon Foff) (T * t) ω|) _
    (fun k _ => Ghat_abs_le' (src k) _ _ ω)
  rwa [Finset.card_range, nsmul_eq_mul] at this

/-- Increment bound for the law of the continuous path, uniformly for large `T`. -/
theorem lawV_increment {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ}
    (hM : SourceCount M) {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)]
    {P : ∀ T, Measure (Ω T)} [∀ T, IsProbabilityMeasure (P T)] {src : ∀ T, ℕ → Source (Ω T)}
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) {K : ℝ} (hK : 0 < K) :
    ∃ C β T₀ : ℝ, 0 ≤ C ∧ 1 < β ∧ ∀ T, T₀ ≤ T → ∀ s t : ℝ≥0, s ≤ t → (t : ℝ) ≤ K →
      ∫⁻ x, ENNReal.ofReal ((x t - x s) ^ 2) ∂((P T).map (pathV (α := α) (hmodel T))) ≤
        ENNReal.ofReal (C * ((t : ℝ) - s) ^ β) := by
  obtain ⟨C, β, T₀, hβ, hb⟩ := gnorm_increment_bound hF hM hmodel hK
  refine ⟨max C 0, β, max T₀ 0, le_max_right _ _, hβ, fun T hT s t hst htK => ?_⟩
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  have hf : Measurable fun x : C(ℝ≥0, ℝ) => ENNReal.ofReal ((x t - x s) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_eval_sub s t).pow_const 2)
  rw [lintegral_map hf (pathV_measurable _)]
  simp only [pathV_apply]
  have hae := Gnorm_eq_Gv hF (hmodel T)
  set B : ℝ≥0 → ℝ := fun u => (M T : ℝ) * ((1 + |mean Fon / mu Fon Foff|) * |T * u|) /
      |dT Fon α M T| with hB
  have hint : Integrable (fun ω => (Gv Fon Foff α M (src T) T ω t -
      Gv Fon Foff α M (src T) T ω s) ^ 2) (P T) := by
    refine Integrable.of_bound ((((Gv_measurable (hmodel T) t).sub
      (Gv_measurable (hmodel T) s)).pow_const 2).aestronglyMeasurable) ((B t + B s) ^ 2)
      (Eventually.of_forall fun ω => ?_)
    have h1 := abs_sub (Gv Fon Foff α M (src T) T ω t) (Gv Fon Foff α M (src T) T ω s)
    have h2 := Gv_abs_le (α := α) (M := M) (src := src T) (Fon := Fon) (Foff := Foff) hT0 ω t
    have h3 := Gv_abs_le (α := α) (M := M) (src := src T) (Fon := Fon) (Foff := Foff) hT0 ω s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans (add_le_add h2 h3)) 2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg _)]
  have heq : ∫ ω, (Gv Fon Foff α M (src T) T ω t - Gv Fon Foff α M (src T) T ω s) ^ 2 ∂(P T) =
      ∫ ω, (Gnorm Fon Foff α M (src T) T t ω - Gnorm Fon Foff α M (src T) T s ω) ^ 2 ∂(P T) :=
    integral_congr_ae (by filter_upwards [hae] with ω hω; rw [hω t, hω s])
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  refine (hb T (le_trans (le_max_left _ _) hT) s t hst htK).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst)) _)

theorem lawV_isProb {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    [IsProbabilityMeasure P] (hmod : IsOnOffSuperposition P Fon Foff (M T) src) :
    IsProbabilityMeasure (P.map (pathV (α := α) hmod)) :=
  Measure.isProbabilityMeasure_map (pathV_measurable hmod).aemeasurable

theorem lawV_zero {Fon Foff : Measure ℝ} {α : ℝ} {M : ℝ → ℕ} {src : ℕ → Source Ω} {T : ℝ}
    (hmod : IsOnOffSuperposition P Fon Foff (M T) src) :
    P.map (pathV (α := α) hmod) {x | x 0 ≠ 0} = 0 := by
  have hset : MeasurableSet {x : C(ℝ≥0, ℝ) | x 0 ≠ 0} :=
    (measurableSet_eq_fun (continuous_eval_const (0:ℝ≥0)).measurable measurable_const).compl
  rw [Measure.map_apply (pathV_measurable hmod) hset]
  have : pathV (α := α) hmod ⁻¹' {x | x 0 ≠ 0} = ∅ := by
    ext ω
    simp [pathV_apply, Gv_zero]
  rw [this, measure_empty]

/-- **C5: tightness** of the laws of the normalised input paths in `C(ℝ≥0, ℝ)`. -/
theorem tight_lawV {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ}
    (hM : SourceCount M) {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)]
    {P : ∀ T, Measure (Ω T)} [∀ T, IsProbabilityMeasure (P T)] {src : ∀ T, ℕ → Source (Ω T)}
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) {Tn : ℕ → ℝ}
    (hTn : Tendsto Tn atTop atTop) :
    IsTightMeasureSet (Set.range fun n => (P (Tn n)).map (pathV (α := α) (hmodel (Tn n)))) := by
  have : ∀ n, IsProbabilityMeasure ((P (Tn n)).map (pathV (α := α) (hmodel (Tn n)))) :=
    fun n => lawV_isProb _
  apply tight_of_eventually_kolm _ (fun n => lawV_zero _)
  intro p
  obtain ⟨C, β, T₀, hC, hβ, hb⟩ := lawV_increment (α := α) hF hM hmodel
    (K := (p:ℝ) + 1) (by positivity)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hTn T₀)
  exact ⟨C, β, N, hC, hβ, fun n hn s t hst htp => hb (Tn n) (hN n hn) s t hst (by linarith)⟩

end Tight2

end NetTraffic.OnOffFBM.Lib

end F05Part12

-- ==== part Conv_part.lean ====
section F05Part13

/-! ### Weak convergence of the path laws in `C(ℝ≥0, ℝ)` (tightness + fidi characteristic functions). -/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal BoundedContinuousFunction

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section Conv

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma continuous_lin_eval {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    Continuous fun x : C(ℝ≥0, ℝ) => ∑ i, c i * x (t i) :=
  continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_eval_const (t i))

lemma continuous_exp_lin {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    Continuous fun x : C(ℝ≥0, ℝ) => cexp (I * ↑(∑ i, c i * x (t i))) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_lin_eval t c)))

lemma norm_exp_I_mul (r : ℝ) : ‖cexp (I * ↑r)‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I r

/-- `x ↦ exp(i Σ c_i x(t_i))` as a bounded continuous function on the path space. -/
noncomputable def expBCF {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    C(ℝ≥0, ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => cexp (I * ↑(∑ i, c i * x (t i))),
    continuous_exp_lin t c⟩ 2 (fun x y => by
      refine (dist_le_norm_add_norm _ _).trans ?_
      simp only [ContinuousMap.coe_mk, norm_exp_I_mul]
      norm_num)

lemma expBCF_apply {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) (x : C(ℝ≥0, ℝ)) :
    expBCF t c x = cexp (I * ↑(∑ i, c i * x (t i))) := rfl

theorem integral_exp_lawV {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon]
    [IsProbabilityMeasure Foff] {α αoff : ℝ} (hF : HeavyTails Fon Foff α αoff) {M : ℝ → ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {src : ℕ → Source Ω} {T : ℝ} (hmod : IsOnOffSuperposition P Fon Foff (M T) src)
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    ∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(P.map (pathV (α := α) hmod)) =
      ∫ ω, cexp (I * ↑(∑ i, c i * Gnorm Fon Foff α M src T (t i) ω)) ∂P := by
  rw [integral_map (pathV_measurable hmod).aemeasurable
    (continuous_exp_lin t c).aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [Gnorm_eq_Gv hF hmod] with ω hω
  simp only [pathV_apply, hω]

/-- Probability measures on the path space with the same fidi characteristic functions agree. -/
theorem eq_of_expchar (ν₁ ν₂ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂]
    (h : ∀ (s : Finset ℝ≥0) (c : s → ℝ), ∫ x, cexp (I * ↑(∑ i, c i * x i)) ∂ν₁ =
      ∫ x, cexp (I * ↑(∑ i, c i * x i)) ∂ν₂) : ν₁ = ν₂ := by
  classical
  apply ext_of_fidi
  intro s
  have hr : Measurable (fun f : C(ℝ≥0, ℝ) => fun i : s => f i) :=
    measurable_pi_iff.2 fun i => (continuous_eval_const (i : ℝ≥0)).measurable
  apply Measure.ext_of_charFunDual
  ext L
  have hL : ∀ y : s → ℝ, L y = ∑ i, (L fun j => if i = j then 1 else 0) * y i := by
    intro y
    rw [show L y = (L : (s → ℝ) →ₗ[ℝ] ℝ) y from rfl, LinearMap.pi_apply_eq_sum_univ]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]; rfl
  have hc : Continuous fun y : s → ℝ => cexp (↑(L y) * I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)
  rw [charFunDual_apply, charFunDual_apply, integral_map hr.aemeasurable hc.aestronglyMeasurable,
    integral_map hr.aemeasurable hc.aestronglyMeasurable]
  have := h s (fun i => L fun j => if i = j then 1 else 0)
  calc _ = ∫ x, cexp (I * ↑(∑ i, (L fun j => if i = j then 1 else 0) * x i)) ∂ν₁ :=
        integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [hL, mul_comm])
    _ = ∫ x, cexp (I * ↑(∑ i, (L fun j => if i = j then 1 else 0) * x i)) ∂ν₂ := this
    _ = _ := (integral_congr_ae (ae_of_all _ fun x => by rw [hL, mul_comm])).symm

end Conv

section Conv2

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

variable {Fon Foff : Measure ℝ} [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    {α αoff : ℝ} {M : ℝ → ℕ} {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)]
    {P : ∀ T, Measure (Ω T)} [∀ T, IsProbabilityMeasure (P T)] {src : ∀ T, ℕ → Source (Ω T)}

/-- The laws of the continuous normalised paths, as probability measures. -/
noncomputable def lawP (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T))
    (α : ℝ) (Tn : ℕ → ℝ) (n : ℕ) : ProbabilityMeasure C(ℝ≥0, ℝ) :=
  ⟨(P (Tn n)).map (pathV (α := α) (hmodel (Tn n))), lawV_isProb _⟩

theorem limchar (hF : HeavyTails Fon Foff α αoff) (hM : SourceCount M) (hC2 : Condition2 Fon M)
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) {Tn : ℕ → ℝ}
    {φ : ℕ → ℕ} (hTφ : Tendsto (fun n => Tn (φ n)) atTop atTop)
    {ν : ProbabilityMeasure C(ℝ≥0, ℝ)}
    (h : Tendsto (fun n => lawP hmodel α Tn (φ n)) atTop (𝓝 ν))
    {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    ∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(ν : Measure C(ℝ≥0, ℝ)) =
      cexp (-(sigma0sq Fon Foff α * ∑ i, ∑ j, c i * c j * covH (hurst α) (t i) (t j) : ℝ) / 2) := by
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 h (expBCF t c)
  simp only [expBCF_apply] at h1
  have h2 := fidi_charFun hF hM hC2 hmodel hTφ t c
  refine tendsto_nhds_unique h1 ?_
  refine h2.congr fun n => ?_
  exact (integral_exp_lawV hF (hmodel _) t c).symm

/-- **Weak convergence** of the path laws in `C(ℝ≥0, ℝ)`, with the limit's fidi characteristic
functions. -/
theorem lawV_tendsto (hF : HeavyTails Fon Foff α αoff) (hM : SourceCount M)
    (hC2 : Condition2 Fon M) (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T))
    {Tn : ℕ → ℝ} (hTn : Tendsto Tn atTop atTop) :
    ∃ ν : ProbabilityMeasure C(ℝ≥0, ℝ), Tendsto (lawP hmodel α Tn) atTop (𝓝 ν) ∧
      ∀ (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ),
        ∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(ν : Measure C(ℝ≥0, ℝ)) =
          cexp (-(sigma0sq Fon Foff α * ∑ i, ∑ j, c i * c j * covH (hurst α) (t i) (t j) : ℝ) /
            2) := by
  have htight := tight_lawV (α := α) hF hM hmodel hTn
  have hS : IsTightMeasureSet {((μ : ProbabilityMeasure C(ℝ≥0, ℝ)) : Measure C(ℝ≥0, ℝ)) |
      μ ∈ Set.range (lawP hmodel α Tn)} := by
    convert htight using 1
    ext m
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩; exact ⟨lawP hmodel α Tn n, ⟨n, rfl⟩, rfl⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  have hsub : ∀ ns : ℕ → ℕ, ∃ ν : ProbabilityMeasure C(ℝ≥0, ℝ), ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto (fun n => lawP hmodel α Tn (ns (ms n))) atTop (𝓝 ν) := by
    intro ns
    obtain ⟨ν, -, ms, hms, hlim⟩ := hK.tendsto_subseq
      (x := fun n => lawP hmodel α Tn (ns n)) (fun n => subset_closure ⟨ns n, rfl⟩)
    exact ⟨ν, ms, hms, hlim⟩
  obtain ⟨ν, ms, hms, hlim⟩ := hsub id
  have hν := fun (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) =>
    limchar hF hM hC2 hmodel (φ := fun n => ms n) (hTn.comp hms.tendsto_atTop) hlim t c
  refine ⟨ν, ?_, hν⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν', ms', hms', hlim'⟩ := hsub ns
  have hν' := fun (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) =>
    limchar hF hM hC2 hmodel (φ := fun n => ns (ms' n))
      (hTn.comp (hns.comp hms'.tendsto_atTop)) hlim' t c
  have heq : ν' = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    apply eq_of_expchar
    intro s c
    rw [hν' s (fun i => (i : ℝ≥0)) c, hν s (fun i => (i : ℝ≥0)) c]
  exact ⟨ms', heq ▸ hlim'⟩

end Conv2

end NetTraffic.OnOffFBM.Lib

end F05Part13

-- ==== part FBM_part.lean ====
section F05Part14

/-! ### L4: a path-space law with Gaussian fidi characteristic functions gives a standard FBM. -/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section FBM

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

/-- The FBM covariance kernel (equal to `covH` by `rfl`). -/
noncomputable def fbmK (H s t : ℝ) : ℝ :=
  (1 / 2) * (t ^ (2 * H) + s ^ (2 * H) - |t - s| ^ (2 * H))

variable {Ω₀ : Type*} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q]
  {Y : Ω₀ → C(ℝ≥0, ℝ)} {H s0 : ℝ}

/-- Nonnegativity of the quadratic form, from `‖charFun‖ ≤ 1`. -/
theorem quad_nonneg (hY : Measurable Y) (hs : 0 < s0)
    (hν : ∀ (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ),
      ∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(Q.map Y) =
        cexp (-(s0 * ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j) : ℝ) / 2))
    (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j) := by
  haveI : IsProbabilityMeasure (Q.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have h1 : ‖∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(Q.map Y)‖ ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := Q.map Y)
      (f := fun x : C(ℝ≥0, ℝ) => cexp (I * ↑(∑ i, c i * x (t i)))) (C := 1)
      (ae_of_all _ fun x => by rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le)
    simpa using this
  rw [hν, Complex.norm_exp] at h1
  have h2 : (-(↑(s0 * ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j)) : ℂ) / 2).re =
      -(s0 * ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j)) / 2 := by
    simp [Complex.div_re]
  rw [h2, Real.exp_le_one_iff] at h1
  by_contra hneg
  push_neg at hneg
  have : s0 * ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j) < 0 := mul_neg_of_pos_of_neg hs hneg
  linarith

/-- The 1-D laws: every linear combination of the scaled coordinates is centred Gaussian. -/
theorem law_lin (hY : Measurable Y) (hs : 0 < s0)
    (hν : ∀ (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ),
      ∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(Q.map Y) =
        cexp (-(s0 * ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j) : ℝ) / 2))
    (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) :
    Q.map (fun ω => ∑ i, c i * (Y ω (t i) / Real.sqrt s0)) =
      gaussianReal 0 (∑ i, ∑ j, c i * c j * fbmK H (t i) (t j)).toNNReal := by
  set V := ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j) with hVdef
  have hV : 0 ≤ V := quad_nonneg hY hs hν ι t c
  set g : C(ℝ≥0, ℝ) → ℝ := fun x => ∑ i, c i * (x (t i) / Real.sqrt s0) with hg
  have hgc : Continuous g :=
    continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_eval_const (t i)).div_const _)
  have hmap : Q.map (fun ω => ∑ i, c i * (Y ω (t i) / Real.sqrt s0)) = (Q.map Y).map g := by
    rw [Measure.map_map hgc.measurable hY]; rfl
  rw [hmap]
  haveI : IsProbabilityMeasure (Q.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  apply Measure.ext_of_charFun
  ext u
  have hss : Real.sqrt s0 ^ 2 = s0 := Real.sq_sqrt hs.le
  have hsq : Real.sqrt s0 ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  rw [charFun_apply_real, integral_map hgc.measurable.aemeasurable
    (by fun_prop : Continuous fun r : ℝ => cexp (↑u * ↑r * I)).aestronglyMeasurable]
  have hpt : ∀ x : C(ℝ≥0, ℝ), cexp (↑u * ↑(g x) * I) =
      cexp (I * ↑(∑ i, (u * c i / Real.sqrt s0) * x (t i))) := by
    intro x
    have : ∑ i, (u * c i / Real.sqrt s0) * x (t i) = u * g x := by
      rw [hg]; simp only; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; push_cast; ring_nf
  simp_rw [hpt]
  rw [hν, charFun_gaussianReal, Real.coe_toNNReal _ hV]
  congr 1
  have hq : s0 * ∑ i, ∑ j, (u * c i / Real.sqrt s0) * (u * c j / Real.sqrt s0) *
      fbmK H (t i) (t j) = V * u ^ 2 := by
    rw [hVdef, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
    rw [hss]; ring
  rw [hq]; push_cast; ring

/-- L4: the scaled coordinate process is a standard FBM. -/
theorem isStdFBM_of_expchar (hY : Measurable Y) (hs : 0 < s0)
    (hν : ∀ (ι : Type) [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ),
      ∫ x, cexp (I * ↑(∑ i, c i * x (t i))) ∂(Q.map Y) =
        cexp (-(s0 * ∑ i, ∑ j, c i * c j * fbmK H (t i) (t j) : ℝ) / 2)) :
    IsStdFBM H (fun t ω => Y ω t / Real.sqrt s0) Q := by
  classical
  set B : ℝ≥0 → Ω₀ → ℝ := fun t ω => Y ω t / Real.sqrt s0 with hB
  have hBm : ∀ t, Measurable (B t) := fun t =>
    ((continuous_eval_const t).measurable.comp hY).div_const _
  -- single coordinate
  have hone : ∀ t, Q.map (B t) = gaussianReal 0 (fbmK H t t).toNNReal := by
    intro t
    have := law_lin hY hs hν Unit (fun _ => t) (fun _ => 1)
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul] at this
    exact this
  have hmem : ∀ t, MemLp (B t) 2 Q := by
    intro t
    have h := memLp_id_gaussianReal (μ := 0) (v := (fbmK H t t).toNNReal) 2
    rw [← hone t] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hBm t).aemeasurable).1 h
  have hvar : ∀ t, Var[B t; Q] = (fbmK H t t).toNNReal := by
    intro t
    have h := variance_id_gaussianReal (μ := 0) (v := (fbmK H t t).toNNReal)
    rw [← hone t, variance_map aemeasurable_id (hBm t).aemeasurable] at h
    exact h
  refine ⟨⟨fun I => ?_⟩, fun t => ?_, fun s t => ?_, ae_of_all _ fun ω => ?_⟩
  · -- Gaussian process
    have hR : Measurable (fun ω => I.restrict (fun t => B t ω)) :=
      measurable_pi_iff.2 fun i => hBm i
    refine ⟨isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
    have hL : ∀ y : I → ℝ, L y = ∑ i, (L fun j => if i = j then 1 else 0) * y i := by
      intro y
      rw [show L y = (L : (I → ℝ) →ₗ[ℝ] ℝ) y from rfl, LinearMap.pi_apply_eq_sum_univ]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]; rfl
    refine ⟨0, (∑ i : I, ∑ j : I, (L fun k => if i = k then 1 else 0) *
      (L fun k => if j = k then 1 else 0) * fbmK H (i : ℝ≥0) (j : ℝ≥0)).toNNReal, ?_⟩
    rw [Measure.map_map L.measurable hR]
    have := law_lin hY hs hν I (fun i => (i : ℝ≥0)) (fun i => L fun j => if i = j then 1 else 0)
    rw [← this]
    congr 1
    funext ω
    simp only [Function.comp_apply]
    rw [hL]
    rfl
  · -- mean zero
    show ∫ ω, B t ω ∂Q = 0
    calc ∫ ω, B t ω ∂Q = ∫ x, x ∂(Q.map (B t)) :=
          (integral_map (hBm t).aemeasurable aestronglyMeasurable_id).symm
      _ = 0 := by rw [hone t]; exact integral_id_gaussianReal
  · -- covariance
    have h2 := law_lin hY hs hν (Fin 2) ![s, t] ![1, 1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at h2
    have hV2 : 0 ≤ fbmK H s s + fbmK H s t + (fbmK H t s + fbmK H t t) := by
      have := quad_nonneg hY hs hν (Fin 2) ![s, t] ![1, 1]
      simpa [Fin.sum_univ_two] using this
    have hvs : Var[fun ω => B s ω + B t ω; Q] =
        fbmK H s s + fbmK H s t + (fbmK H t s + fbmK H t t) := by
      have h := variance_id_gaussianReal (μ := 0)
        (v := (fbmK H s s + fbmK H s t + (fbmK H t s + fbmK H t t)).toNNReal)
      rw [← h2, variance_map aemeasurable_id (show Measurable (fun ω => (Y ω) s / √s0 +
          (Y ω) t / √s0) from (hBm s).add (hBm t)).aemeasurable,
        Real.coe_toNNReal _ hV2] at h
      exact h
    have hadd := variance_add (hmem s) (hmem t)
    have e : (B s + B t) = fun ω => B s ω + B t ω := rfl
    rw [e, hvs, hvar, hvar] at hadd
    have hss : 0 ≤ fbmK H s s := by
      have := quad_nonneg hY hs hν Unit (fun _ => s) (fun _ => 1); simpa using this
    have htt : 0 ≤ fbmK H t t := by
      have := quad_nonneg hY hs hν Unit (fun _ => t) (fun _ => 1); simpa using this
    rw [Real.coe_toNNReal _ hss, Real.coe_toNNReal _ htt] at hadd
    have hts : fbmK H t s = fbmK H s t := by unfold fbmK; rw [abs_sub_comm]; ring
    have : cov[B s, B t; Q] = fbmK H s t := by linarith
    rw [this]; unfold fbmK; ring
  · exact (Y ω).continuous.div_const _

end FBM

end NetTraffic.OnOffFBM.Lib

end F05Part14

-- ==== part Skor1_part.lean ====
section F05Part15

/-! ### L5a: ingredients of the Skorokhod representation (cells with null frontiers, samplers). -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

section Skor1

theorem frontier_biInter_compl_subset {E : Type*} [TopologicalSpace E] (g : ℕ → Set E) (i : ℕ) :
    frontier (⋂ j < i, (g j)ᶜ) ⊆ ⋃ j < i, frontier (g j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : (⋂ j < i + 1, (g j)ᶜ) = (⋂ j < i, (g j)ᶜ) ∩ (g i)ᶜ := by
      ext z
      simp only [mem_iInter, mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h i (Nat.lt_succ_self i)⟩
      · rintro ⟨h, hi⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h j hj
        · exact hi
    rw [h1]
    refine (frontier_inter_subset _ _).trans ?_
    intro z hz
    simp only [mem_iUnion]
    rcases hz with ⟨hz, _⟩ | ⟨_, hz⟩
    · obtain ⟨j, hj, hz⟩ := by simpa only [mem_iUnion] using ih hz
      exact ⟨j, Nat.lt_succ_of_lt hj, hz⟩
    · rw [frontier_compl] at hz
      exact ⟨i, Nat.lt_succ_self i, hz⟩

/-- Countable Borel partitions into small cells whose frontiers are null. -/
theorem exists_cells {E : Type*} [PseudoMetricSpace E] [TopologicalSpace.SeparableSpace E]
    [Nonempty E] [MeasurableSpace E] [OpensMeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ → Set E, (∀ i, MeasurableSet (B i)) ∧ Pairwise (Function.onFun Disjoint B) ∧
      (⋃ i, B i) = univ ∧ (∀ i, ∀ x ∈ B i, ∀ y ∈ B i, dist x y < ε) ∧
      ∀ i, ν (frontier (B i)) = 0 := by
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq E
  have hab : ε / 4 < ε / 2 := by linarith
  choose r hr hr0 using fun m => exists_null_frontier_thickening ν {x m} hab
  set D : ℕ → Set E := fun m => Metric.ball (x m) (r m) with hDdef
  have hD0 : ∀ m, ν (frontier (D m)) = 0 := fun m => by
    have := hr0 m; rwa [Metric.thickening_singleton] at this
  refine ⟨disjointed D, fun i => MeasurableSet.disjointed (fun m => Metric.isOpen_ball.measurableSet) i,
    disjoint_disjointed D, ?_, ?_, ?_⟩
  · rw [iUnion_disjointed]
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨m, hm⟩ := hx.exists_dist_lt y (by linarith : (0 : ℝ) < ε / 4)
    exact mem_iUnion.2 ⟨m, Metric.mem_ball.2 (by linarith [(hr m).1])⟩
  · intro i a ha b hb
    have ha' := Metric.mem_ball.1 (disjointed_subset D i ha)
    have hb' := Metric.mem_ball.1 (disjointed_subset D i hb)
    have := dist_triangle_right a b (x i)
    linarith [(hr i).2]
  · intro i
    rw [disjointed_eq_inter_compl]
    refine measure_mono_null (frontier_inter_subset _ _) ?_
    refine measure_union_null (measure_mono_null inter_subset_left (hD0 i)) ?_
    refine measure_mono_null (inter_subset_right.trans (frontier_biInter_compl_subset D i)) ?_
    exact measure_iUnion_null fun j => measure_iUnion_null fun _ => hD0 j

/-- Every probability measure on a standard Borel space is the image of Lebesgue measure on `[0,1]`. -/
theorem exists_sampler {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (m : Measure E) [IsProbabilityMeasure m] :
    ∃ f : unitInterval → E, Measurable f ∧ (volume : Measure unitInterval).map f = m := by
  obtain ⟨f, hf, hmap⟩ := ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval
    (Kernel.const Unit m)
  exact ⟨f (), hf.comp (measurable_const.prodMk measurable_id), by simpa using hmap ()⟩

/-- A sampler that lands surely in a set of full measure. -/
theorem exists_sampler_mem {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (m : Measure E) [IsProbabilityMeasure m] {S : Set E} (hS : MeasurableSet S) (hmS : m Sᶜ = 0) :
    ∃ f : unitInterval → E, Measurable f ∧ (volume : Measure unitInterval).map f = m ∧
      ∀ v, f v ∈ S := by
  classical
  obtain ⟨f, hf, hmap⟩ := exists_sampler m
  have hne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hmS
    exact one_ne_zero hmS
  obtain ⟨s0, hs0⟩ := hne
  refine ⟨fun v => if f v ∈ S then f v else s0, Measurable.ite (hf hS) hf measurable_const,
    ?_, fun v => by dsimp only; split_ifs with h; exacts [h, hs0]⟩
  have hae : ∀ᵐ v ∂(volume : Measure unitInterval), f v ∈ S := by
    rw [ae_iff]
    have := Measure.map_apply hf hS.compl (μ := (volume : Measure unitInterval))
    rw [hmap, hmS] at this
    exact this.symm
  rw [← hmap]
  exact Measure.map_congr (hae.mono fun v hv => by simp [hv])

end Skor1

end NetTraffic.OnOffFBM.Lib

end F05Part15

-- ==== part Skor2_part.lean ====
section F05Part16

/-! ### L5b: the law of one Skorokhod coordinate (mixture of conditional cell laws + deficit). -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

section Skor2

variable {E : Type*} [MeasurableSpace E]

/-- Uniform law on `[0,1] ⊆ ℝ`. -/
noncomputable def lamU : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

theorem lamU_isProb : IsProbabilityMeasure lamU := ⟨by simp [lamU]⟩

attribute [local instance] lamU_isProb

theorem lamU_Iic {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : lamU (Iic θ) = ENNReal.ofReal θ := by
  rw [lamU, Measure.restrict_apply measurableSet_Iic]
  have : Iic θ ∩ Icc (0 : ℝ) 1 = Icc 0 θ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨h, h', h.trans h1⟩
  rw [this, Real.volume_Icc, sub_zero]

/-- The cell weights. -/
noncomputable def skW (ν : Measure E) (B : ℕ → Set E) (θ : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal θ * ν (B i)

/-- The kept part of `m`. -/
noncomputable def skS (m ν : Measure E) (B : ℕ → Set E) (J : ℕ) (θ : ℝ) : Measure E :=
  ∑ i ∈ Finset.range J, skW ν B θ i • m[|B i]

/-- The deficit measure. -/
noncomputable def skRho (m ν : Measure E) (B : ℕ → Set E) (J : ℕ) (θ : ℝ) : Measure E :=
  m - skS m ν B J θ

/-- One Skorokhod coordinate. -/
noncomputable def skX (idx : E → ℕ) (J : ℕ) (θ : ℝ) (φ : ℕ → unitInterval → E)
    (ψ : unitInterval → E) : (E × ℝ) × unitInterval → E :=
  fun ω => if idx ω.1.1 < J ∧ ω.1.2 ≤ θ then φ (idx ω.1.1) ω.2 else ψ ω.2

theorem measurable_idx {B : ℕ → Set E} (hBm : ∀ i, MeasurableSet (B i)) {idx : E → ℕ}
    (hidx : ∀ y i, y ∈ B i ↔ idx y = i) : Measurable idx := by
  refine measurable_to_countable' fun i => ?_
  have : idx ⁻¹' {i} = B i := by ext y; simp [hidx]
  rw [this]; exact hBm i

theorem measurableSet_skG {B : ℕ → Set E} (hBm : ∀ i, MeasurableSet (B i)) {idx : E → ℕ}
    (hidx : ∀ y i, y ∈ B i ↔ idx y = i) (J : ℕ) (θ : ℝ) :
    MeasurableSet {p : E × ℝ | idx p.1 < J ∧ p.2 ≤ θ} :=
  ((measurable_idx hBm hidx).comp measurable_fst measurableSet_Iio).inter
    (measurable_snd measurableSet_Iic)

theorem measurable_skX {B : ℕ → Set E} (hBm : ∀ i, MeasurableSet (B i)) {idx : E → ℕ}
    (hidx : ∀ y i, y ∈ B i ↔ idx y = i) (J : ℕ) (θ : ℝ) {φ : ℕ → unitInterval → E}
    (hφm : ∀ i, Measurable (φ i)) {ψ : unitInterval → E} (hψm : Measurable ψ) :
    Measurable (skX idx J θ φ ψ) := by
  have h1 : Measurable fun p : ℕ × unitInterval => φ p.1 p.2 :=
    measurable_from_prod_countable_right fun i => hφm i
  have h2 : Measurable fun ω : (E × ℝ) × unitInterval => φ (idx ω.1.1) ω.2 :=
    h1.comp (((measurable_idx hBm hidx).comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd)
  exact Measurable.ite ((measurableSet_skG hBm hidx J θ).preimage measurable_fst) h2
    (hψm.comp measurable_snd)

theorem skG_eq {B : ℕ → Set E} {idx : E → ℕ} (hidx : ∀ y i, y ∈ B i ↔ idx y = i) (J : ℕ)
    (θ : ℝ) :
    {p : E × ℝ | idx p.1 < J ∧ p.2 ≤ θ} = ⋃ i ∈ Finset.range J, B i ×ˢ Iic θ := by
  ext p
  simp only [mem_setOf_eq, mem_iUnion, Finset.mem_range, mem_prod, mem_Iic, hidx, exists_prop]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨idx p.1, h, rfl, h'⟩
  · rintro ⟨i, hi, rfl, h'⟩; exact ⟨hi, h'⟩

theorem skX_preimage {B : ℕ → Set E} {idx : E → ℕ} (hidx : ∀ y i, y ∈ B i ↔ idx y = i)
    (J : ℕ) (θ : ℝ) (φ : ℕ → unitInterval → E) (ψ : unitInterval → E) (A : Set E) :
    skX idx J θ φ ψ ⁻¹' A =
      (⋃ i ∈ Finset.range J, (B i ×ˢ Iic θ) ×ˢ (φ i ⁻¹' A)) ∪
        ({p : E × ℝ | idx p.1 < J ∧ p.2 ≤ θ}ᶜ ×ˢ (ψ ⁻¹' A)) := by
  ext ω
  simp only [skX, mem_preimage, mem_union, mem_iUnion, Finset.mem_range, mem_prod, mem_Iic,
    hidx, exists_prop, mem_compl_iff, mem_setOf_eq]
  by_cases h : idx ω.1.1 < J ∧ ω.1.2 ≤ θ
  · rw [if_pos h]
    constructor
    · intro hA; exact Or.inl ⟨idx ω.1.1, h.1, ⟨rfl, h.2⟩, hA⟩
    · rintro (⟨i, _, ⟨rfl, _⟩, hA⟩ | ⟨h', _⟩)
      · exact hA
      · exact absurd h h'
  · rw [if_neg h]
    constructor
    · intro hA; exact Or.inr ⟨h, hA⟩
    · rintro (⟨i, hi, ⟨rfl, h2⟩, _⟩ | ⟨_, hA⟩)
      · exact absurd ⟨hi, h2⟩ h
      · exact hA

theorem skS_le (m ν : Measure E) [IsProbabilityMeasure m] {B : ℕ → Set E}
    (hBm : ∀ i, MeasurableSet (B i)) (hBd : Pairwise (Function.onFun Disjoint B)) (J : ℕ)
    (θ : ℝ) (hw : ∀ i < J, skW ν B θ i ≤ m (B i)) : skS m ν B J θ ≤ m := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [skS, Measure.coe_finset_sum, Finset.sum_apply]
  calc ∑ i ∈ Finset.range J, (skW ν B θ i • m[|B i]) A
      ≤ ∑ i ∈ Finset.range J, m (B i ∩ A) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Measure.smul_apply, smul_eq_mul, ← cond_mul_eq_inter (hBm i) A m, mul_comm (m[A|B i])]
        gcongr
        exact hw i (Finset.mem_range.1 hi)
    _ = m (⋃ i ∈ Finset.range J, B i ∩ A) := by
        rw [measure_biUnion_finset]
        · intro i _ j _ hij
          exact (hBd hij).mono inter_subset_left inter_subset_left
        · exact fun i _ => (hBm i).inter hA
    _ ≤ m A := measure_mono (iUnion₂_subset fun i _ => inter_subset_right)

theorem skS_univ (m ν : Measure E) [IsProbabilityMeasure m] {B : ℕ → Set E}
    (hBm : ∀ i, MeasurableSet (B i)) (J : ℕ) (θ : ℝ)
    (hw : ∀ i < J, skW ν B θ i ≤ m (B i)) :
    skS m ν B J θ univ = ∑ i ∈ Finset.range J, skW ν B θ i := by
  rw [skS, Measure.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases h0 : m (B i) = 0
  · have : skW ν B θ i = 0 := le_antisymm ((hw i (Finset.mem_range.1 hi)).trans h0.le) bot_le
    rw [this, zero_mul]
  · haveI := cond_isProbabilityMeasure (μ := m) h0
    rw [measure_univ, mul_one]

/-- The law of one Skorokhod coordinate is `m`. -/
theorem skX_law (m ν : Measure E) [IsProbabilityMeasure m] [IsProbabilityMeasure ν]
    {B : ℕ → Set E} (hBm : ∀ i, MeasurableSet (B i)) (hBd : Pairwise (Function.onFun Disjoint B))
    {idx : E → ℕ} (hidx : ∀ y i, y ∈ B i ↔ idx y = i) (J : ℕ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hw : ∀ i < J, skW ν B θ i ≤ m (B i)) {φ : ℕ → unitInterval → E}
    (hφm : ∀ i, Measurable (φ i)) (hφ : ∀ i < J, m (B i) ≠ 0 → volume.map (φ i) = m[|B i])
    {ψ : unitInterval → E} (hψm : Measurable ψ)
    (hψ : skRho m ν B J θ univ ≠ 0 →
      volume.map ψ = (skRho m ν B J θ univ)⁻¹ • skRho m ν B J θ) :
    ((ν.prod lamU).prod volume).map (skX idx J θ φ ψ) = m := by
  set S := skS m ν B J θ with hS
  set ρ := skRho m ν B J θ with hρ
  set G := {p : E × ℝ | idx p.1 < J ∧ p.2 ≤ θ} with hG
  have hGm : MeasurableSet G := measurableSet_skG hBm hidx J θ
  have hSle : S ≤ m := skS_le m ν hBm hBd J θ hw
  haveI : IsFiniteMeasure S := isFiniteMeasure_of_le m hSle
  haveI : IsFiniteMeasure ρ := isFiniteMeasure_of_le m Measure.sub_le
  have hsumle : ∑ i ∈ Finset.range J, skW ν B θ i ≤ 1 := by
    rw [← skS_univ m ν hBm J θ hw, ← measure_univ (μ := m)]; exact hSle _
  -- mass of G
  have hGmass : (ν.prod lamU) G = ∑ i ∈ Finset.range J, skW ν B θ i := by
    rw [hG, skG_eq hidx, measure_biUnion_finset]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Measure.prod_prod, lamU_Iic hθ0 hθ1, skW, mul_comm]
    · intro i _ j _ hij
      exact Disjoint.set_prod_left (hBd hij) _ _
    · exact fun i _ => (hBm i).prod measurableSet_Iic
  have hGc : (ν.prod lamU) Gᶜ = ρ univ := by
    rw [prob_compl_eq_one_sub hGm, hGmass, hρ, skRho, Measure.sub_apply MeasurableSet.univ hSle,
      measure_univ, skS_univ m ν hBm J θ hw]
  have hρS : ρ + S = m := Measure.sub_add_cancel_of_le hSle
  ext A hA
  rw [Measure.map_apply (measurable_skX hBm hidx J θ hφm hψm) hA, skX_preimage hidx,
    measure_union]
  rotate_left
  · rw [Set.disjoint_left]
    rintro ω h1 ⟨h2, _⟩
    simp only [mem_iUnion, Finset.mem_range, mem_prod, exists_prop] at h1
    obtain ⟨i, hi, ⟨hy, hu⟩, _⟩ := h1
    exact h2 ⟨by rw [(hidx _ _).1 hy]; exact hi, hu⟩
  · exact (hGm.compl).prod (hψm hA)
  rw [measure_biUnion_finset]
  rotate_left
  · intro i _ j _ hij
    exact Disjoint.set_prod_left (Disjoint.set_prod_left (hBd hij) _ _) _ _
  · exact fun i _ => ((hBm i).prod measurableSet_Iic).prod (hφm i hA)
  conv_rhs => rw [← hρS]
  rw [Measure.add_apply, Measure.prod_prod, hGc, hS, skS, Measure.coe_finset_sum,
    Finset.sum_apply, add_comm (ρ A)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Measure.prod_prod, Measure.prod_prod, lamU_Iic hθ0 hθ1, Measure.smul_apply, smul_eq_mul]
    by_cases h0 : m (B i) = 0
    · have : skW ν B θ i = 0 :=
        le_antisymm ((hw i (Finset.mem_range.1 hi)).trans h0.le) bot_le
      rw [skW] at this
      rw [skW, this, mul_comm (ν (B i)), this, zero_mul, zero_mul]
    · rw [← Measure.map_apply (hφm i) hA, hφ i (Finset.mem_range.1 hi) h0, skW, mul_comm (ν (B i))]
  · by_cases h0 : ρ univ = 0
    · have : ρ = 0 := Measure.measure_univ_eq_zero.1 h0
      rw [h0, zero_mul, this, Measure.coe_zero, Pi.zero_apply]
    · rw [← Measure.map_apply hψm hA, hψ h0, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

end Skor2

end NetTraffic.OnOffFBM.Lib

end F05Part16

-- ==== part Skor3_part.lean ====
section F05Part17

/-! ### L5c: Skorokhod representation (Billingsley, Convergence of Probability Measures, Thm 6.7). -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

section Skor3

attribute [local instance] lamU_isProb

/-- Skorokhod representation on a separable pseudometric standard Borel space, with the
convergence hypothesis in null-frontier form. The space is `(E × ℝ) × [0,1]` and the limit
variable is the first coordinate. -/
theorem skorokhod_core {E : Type*} [PseudoMetricSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure E) [IsProbabilityMeasure ν]
    (hconv : ∀ S, MeasurableSet S → ν (frontier S) = 0 → Tendsto (fun n => μ n S) atTop (𝓝 (ν S))) :
    ∃ X : ℕ → (E × ℝ) × unitInterval → E, (∀ n, Measurable (X n)) ∧
      (∀ n, ((ν.prod lamU).prod volume).map (X n) = μ n) ∧
      ∀ᵐ ω ∂((ν.prod lamU).prod volume), Tendsto (fun n => X n ω) atTop (𝓝 ω.1.1) := by
  classical
  set Q : Measure ((E × ℝ) × unitInterval) := (ν.prod lamU).prod volume with hQ
  -- cells
  choose B hBm hBd hBcov hBdiam hBfr using fun k : ℕ =>
    exists_cells ν (ε := 1 / ((k : ℝ) + 1)) (by positivity)
  have hex : ∀ k y, ∃ i, y ∈ B k i := fun k y => mem_iUnion.1 ((hBcov k).symm ▸ mem_univ y)
  set idx : ℕ → E → ℕ := fun k y => Nat.find (hex k y) with hidxdef
  have hidx : ∀ k y i, y ∈ B k i ↔ idx k y = i := by
    intro k y i
    constructor
    · intro hy
      by_contra hne
      exact Set.disjoint_left.1 (hBd k hne) (Nat.find_spec (hex k y)) hy
    · rintro rfl; exact Nat.find_spec (hex k y)
  have hidxm : ∀ k, Measurable (idx k) := fun k => measurable_idx (hBm k) (hidx k)
  -- truncation levels
  have hJex : ∀ k, ∃ J, ν {y | J ≤ idx k y} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    have hanti : Antitone fun J : ℕ => {y | J ≤ idx k y} :=
      fun a b hab y hy => le_trans hab hy
    have hinter : (⋂ J : ℕ, {y | J ≤ idx k y}) = ∅ := by
      ext y; simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall,
        not_le]
      exact ⟨idx k y + 1, Nat.lt_succ_self _⟩
    have ht := tendsto_measure_iInter_atTop (μ := ν)
      (fun J => (measurableSet_le measurable_const (hidxm k)).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at ht
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
      ENNReal.ofReal_pos.2 (by positivity)
    obtain ⟨J, hJ⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
    exact ⟨J, hJ.le⟩
  choose J hJ using hJex
  set θ : ℕ → ℝ := fun k => 1 - (1 / 2 : ℝ) ^ k with hθdef
  have hθ0 : ∀ k, 0 ≤ θ k := fun k => by
    simp only [hθdef, sub_nonneg]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hθ1 : ∀ k, θ k ≤ 1 := fun k => by simp only [hθdef]; linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) k]
  have hθlt : ∀ k, θ k < 1 := fun k => by simp only [hθdef]; linarith [pow_pos (by norm_num : (0:ℝ) < 1 / 2) k]
  -- good levels
  set Good : ℕ → ℕ → Prop := fun n k => ∀ i < J k, skW ν (B k) (θ k) i ≤ μ n (B k i) with hGood
  have hGood0 : ∀ n, Good n 0 := fun n i _ => by
    simp [skW, hθdef]
  have hGoodev : ∀ k, ∀ᶠ n in atTop, Good n k := by
    intro k
    have : ∀ i ∈ Iio (J k), ∀ᶠ n in atTop, skW ν (B k) (θ k) i ≤ μ n (B k i) := by
      intro i _
      by_cases h0 : ν (B k i) = 0
      · exact Eventually.of_forall fun n => by simp [skW, h0]
      · have hlt : skW ν (B k) (θ k) i < ν (B k i) := by
          rw [skW]
          calc ENNReal.ofReal (θ k) * ν (B k i) < 1 * ν (B k i) :=
                ENNReal.mul_lt_mul_left h0 (measure_ne_top _ _)
                  (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff
                    one_pos).2 (hθlt k))
            _ = ν (B k i) := one_mul _
        exact ((hconv _ (hBm k i) (hBfr k i)).eventually (lt_mem_nhds hlt)).mono
          fun n hn => hn.le
    exact ((Filter.eventually_all_finite (finite_Iio (J k))).2 this).mono
      fun n hn i hi => hn i hi
  set L : ℕ → ℕ := fun n => Nat.findGreatest (Good n) n with hLdef
  have hLgood : ∀ n, Good n (L n) := fun n =>
    Nat.findGreatest_spec (P := Good n) (Nat.zero_le n) (hGood0 n)
  have hLtend : Tendsto L atTop atTop := by
    refine tendsto_atTop.2 fun K => ((hGoodev K).and (eventually_ge_atTop K)).mono ?_
    rintro n ⟨h1, h2⟩
    exact Nat.le_findGreatest h2 h1
  -- samplers
  have hφex : ∀ n k i, ∃ f : unitInterval → E, Measurable f ∧
      (μ n (B k i) ≠ 0 → volume.map f = (μ n)[|B k i] ∧ ∀ v, f v ∈ B k i) := by
    intro n k i
    by_cases h : μ n (B k i) = 0
    · exact ⟨fun _ => Classical.arbitrary E, measurable_const, fun h' => absurd h h'⟩
    · haveI := cond_isProbabilityMeasure (μ := μ n) h
      have hc : (μ n)[|B k i] (B k i)ᶜ = 0 := by
        rw [cond_apply (hBm k i), inter_compl_self, measure_empty, mul_zero]
      obtain ⟨f, hf, hmap, hmem⟩ := exists_sampler_mem ((μ n)[|B k i]) (hBm k i) hc
      exact ⟨f, hf, fun _ => ⟨hmap, hmem⟩⟩
  choose φ hφm hφ using hφex
  have hψex : ∀ n k, ∃ f : unitInterval → E, Measurable f ∧
      (skRho (μ n) ν (B k) (J k) (θ k) univ ≠ 0 → volume.map f =
        (skRho (μ n) ν (B k) (J k) (θ k) univ)⁻¹ • skRho (μ n) ν (B k) (J k) (θ k)) := by
    intro n k
    set ρ := skRho (μ n) ν (B k) (J k) (θ k)
    by_cases h : ρ univ = 0
    · exact ⟨fun _ => Classical.arbitrary E, measurable_const, fun h' => absurd h h'⟩
    · have hfin : ρ univ ≠ ∞ :=
        ne_top_of_le_ne_top (measure_ne_top (μ n) univ) (Measure.sub_le (μ := μ n) _ )
      haveI : IsProbabilityMeasure ((ρ univ)⁻¹ • ρ) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h hfin]⟩
      obtain ⟨f, hf, hmap⟩ := exists_sampler ((ρ univ)⁻¹ • ρ)
      exact ⟨f, hf, fun _ => hmap⟩
  choose ψ hψm hψ using hψex
  -- the coupling
  refine ⟨fun n => skX (idx (L n)) (J (L n)) (θ (L n)) (φ n (L n)) (ψ n (L n)),
    fun n => measurable_skX (hBm _) (hidx _) _ _ (hφm n _) (hψm n _),
    fun n => skX_law (μ n) ν (hBm _) (hBd _) (hidx _) (J _) (hθ0 _) (hθ1 _) (hLgood n)
      (hφm n _) (fun i _ h => (hφ n _ i h).1) (hψm n _) (hψ n _), ?_⟩
  -- Borel-Cantelli
  set Bad : ℕ → Set ((E × ℝ) × unitInterval) :=
    fun k => {ω | J k ≤ idx k ω.1.1} ∪ {ω | θ k < ω.1.2} with hBad
  have hQ1 : ∀ k, Q {ω | J k ≤ idx k ω.1.1} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    have : {ω : (E × ℝ) × unitInterval | J k ≤ idx k ω.1.1} =
        ({y | J k ≤ idx k y} ×ˢ univ) ×ˢ univ := by ext ω; simp
    rw [this, hQ, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one,
      mul_one]
    exact hJ k
  have hQ2 : ∀ k, Q {ω | θ k < ω.1.2} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    have : {ω : (E × ℝ) × unitInterval | θ k < ω.1.2} = (univ ×ˢ (Iic (θ k))ᶜ) ×ˢ univ := by
      ext ω; simp
    rw [this, hQ, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one,
      one_mul, prob_compl_eq_one_sub measurableSet_Iic, lamU_Iic (hθ0 k) (hθ1 k)]
    rw [tsub_le_iff_right, ← ENNReal.ofReal_add (by positivity) (hθ0 k), hθdef]
    simp
  have hsum : (∑' k, Q (Bad k)) ≠ ∞ := by
    have hle : ∀ k, Q (Bad k) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
      intro k
      refine (measure_union_le _ _).trans ?_
      rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add (hQ1 k) (hQ2 k)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
      (summable_geometric_two.mul_left 2)]
    exact ENNReal.ofReal_ne_top
  have hBC := ae_eventually_notMem (μ := Q) hsum
  have hnull : ∀ᵐ ω ∂Q, ∀ k i, ν (B k i) = 0 → ω.1.1 ∉ B k i := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro i
    by_cases h : ν (B k i) = 0
    · have hz : Q ((B k i ×ˢ univ) ×ˢ univ) = 0 := by
        rw [hQ, Measure.prod_prod, Measure.prod_prod, h, zero_mul, zero_mul]
      filter_upwards [(measure_eq_zero_iff_ae_notMem.1 hz)] with ω hω _ hmem
      exact hω ⟨⟨hmem, mem_univ _⟩, mem_univ _⟩
    · exact Eventually.of_forall fun ω h' => absurd h' h
  filter_upwards [hBC, hnull] with ω h1 h2
  obtain ⟨K, hK⟩ := eventually_atTop.1 h1
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun n => 1 / ((L n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hLtend
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hlim
  filter_upwards [hLtend.eventually (eventually_ge_atTop (max K 1))] with n hn
  set k := L n with hk
  have hkK : K ≤ k := le_of_max_le_left hn
  have hk1 : 1 ≤ k := le_of_max_le_right hn
  have hnb := hK k hkK
  simp only [hBad, mem_union, mem_setOf_eq, not_or, not_le, not_lt] at hnb
  obtain ⟨hidxJ, hu⟩ := hnb
  set i := idx k ω.1.1 with hi
  have hyi : ω.1.1 ∈ B k i := (hidx k _ i).2 rfl
  have hμ0 : μ n (B k i) ≠ 0 := by
    intro h0
    have hw := hLgood n i hidxJ
    rw [← hk, h0, skW] at hw
    have hθpos : 0 < θ k := by
      simp only [hθdef, sub_pos]
      exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have : ν (B k i) = 0 := by
      rcases mul_eq_zero.1 (le_antisymm hw bot_le) with h | h
      · exact absurd h (ENNReal.ofReal_pos.2 hθpos).ne'
      · exact h
    exact h2 k i this hyi
  have hX : skX (idx k) (J k) (θ k) (φ n k) (ψ n k) ω = φ n k i ω.2 := by
    simp only [skX]; rw [if_pos ⟨hidxJ, hu⟩]
  show dist (skX (idx k) (J k) (θ k) (φ n k) (ψ n k) ω) ω.1.1 ≤ 1 / ((k : ℝ) + 1)
  rw [hX]
  exact (hBdiam k i _ ((hφ n k i hμ0).2 _) _ hyi).le

end Skor3

end NetTraffic.OnOffFBM.Lib

end F05Part17

-- ==== part Skor4_part.lean ====
section F05Part18

/-! ### L5d: Skorokhod representation for weakly convergent probability measures on a Polish space. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

section Skor4

attribute [local instance] lamU_isProb

theorem skorokhod {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E]
    [BorelSpace E] (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (h : Tendsto μ atTop (𝓝 ν)) :
    ∃ X : ℕ → (E × ℝ) × unitInterval → E, (∀ n, Measurable (X n)) ∧
      (∀ n, (((ν : Measure E).prod lamU).prod volume).map (X n) = μ n) ∧
      ∀ᵐ ω ∂(((ν : Measure E).prod lamU).prod volume),
        Tendsto (fun n => X n ω) atTop (𝓝 ω.1.1) := by
  letI : MetricSpace E := TopologicalSpace.completelyMetrizableMetric E
  haveI : Nonempty E := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    have : (ν : Measure E) univ = 0 := by rw [univ_eq_empty_iff.2 hE, measure_empty]
    rw [measure_univ] at this
    exact one_ne_zero this
  refine skorokhod_core (fun n => (μ n : Measure E)) (ν : Measure E) fun S _ hS => ?_
  have hS' : ν (frontier S) = 0 := by
    have := (ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν (frontier S)).trans hS
    exact_mod_cast this
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto h hS'
  have := (ENNReal.tendsto_coe.2 key)
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using this

end Skor4

section PolishTest

example : PolishSpace C(ℝ≥0, ℝ) := inferInstance

end PolishTest

end NetTraffic.OnOffFBM.Lib

end F05Part18

-- ==== part L6_part.lean ====
section F05Part19

/-! ### L6: assembly of Theorem 4 (weak convergence → Skorokhod coupling → FBM limit). -/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal

set_option autoImplicit false

namespace NetTraffic.OnOffFBM.Lib

open NetTraffic.OnOffFBM

section L6

attribute [local instance] borel

local instance : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

attribute [local instance] lamU_isProb

theorem theorem_4_lib
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    (M : ℝ → ℕ) (hM : SourceCount M) (hC2 : Condition2 Fon M)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∀ Tn : ℕ → ℝ, Tendsto Tn atTop atTop →
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → ℝ≥0 → Ω₀ → ℝ)
        (Y' : ℝ≥0 → Ω₀ → ℝ),
        IsProbabilityMeasure Q ∧
        (∀ n, Measurable (fun ω (t : ℝ≥0) => Y n t ω)) ∧
        (∀ n, ∀ᵐ ω ∂Q, Continuous (fun t => Y n t ω)) ∧
        (∀ n, Q.map (fun ω (t : ℝ≥0) => Y n t ω) =
          (P (Tn n)).map (fun ω (t : ℝ≥0) => Gnorm Fon Foff α M (src (Tn n)) (Tn n) t ω)) ∧
        IsStdFBM (hurst α) Y' Q ∧
        ∀ᵐ ω ∂Q, UocTendsto (fun n t => Y n t ω) (fun t => sigma0 Fon Foff α * Y' t ω) := by
  intro Tn hTn
  obtain ⟨ν, hlim, hchar⟩ := lawV_tendsto hF hM hC2 hmodel hTn
  obtain ⟨X, hXm, hXlaw, hXconv⟩ := skorokhod (lawP hmodel α Tn) ν hlim
  set Q := (((ν : Measure C(ℝ≥0, ℝ)).prod lamU).prod (volume : Measure unitInterval)) with hQ
  have hs := sigma0sq_pos hF
  have hσ : sigma0 Fon Foff α ≠ 0 := (Real.sqrt_pos.2 hs).ne'
  refine ⟨(C(ℝ≥0, ℝ) × ℝ) × unitInterval, inferInstance, Q, fun n t ω => X n ω t,
    fun t ω => ω.1.1 t / sigma0 Fon Foff α, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact measurable_coe_path.comp (hXm n)
  · intro n; exact ae_of_all _ fun ω => (X n ω).continuous
  · intro n
    have h1 : Q.map (fun ω (t : ℝ≥0) => X n ω t) =
        (Q.map (X n)).map (fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ)) := by
      rw [Measure.map_map measurable_coe_path (hXm n)]; rfl
    rw [h1, hXlaw n]
    show ((P (Tn n)).map (pathV (α := α) (hmodel (Tn n)))).map _ = _
    rw [Measure.map_map measurable_coe_path (pathV_measurable _)]
    refine Measure.map_congr ?_
    filter_upwards [Gnorm_eq_Gv hF (hmodel (Tn n))] with ω hω
    funext t
    simp only [Function.comp_apply, pathV_apply, hω]
  · have hY : Measurable (fun ω : (C(ℝ≥0, ℝ) × ℝ) × unitInterval => ω.1.1) :=
      measurable_fst.comp measurable_fst
    have hmapY : Q.map (fun ω => ω.1.1) = (ν : Measure C(ℝ≥0, ℝ)) := by
      rw [show (fun ω : (C(ℝ≥0, ℝ) × ℝ) × unitInterval => ω.1.1) = Prod.fst ∘ Prod.fst from rfl,
        ← Measure.map_map measurable_fst measurable_fst, hQ, Measure.map_fst_prod, measure_univ,
        one_smul, Measure.map_fst_prod, measure_univ, one_smul]
    exact isStdFBM_of_expchar (Q := Q) (H := hurst α) (s0 := sigma0sq Fon Foff α) hY hs
      (fun ι _ t c => by rw [hmapY]; exact hchar ι t c)
  · filter_upwards [hXconv] with ω hω
    intro K
    have hK : IsCompact (Set.Icc (0 : ℝ≥0) K) := isCompact_Icc
    have := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hω) _ hK
    have e : (fun t => sigma0 Fon Foff α * (ω.1.1 t / sigma0 Fon Foff α)) = ⇑ω.1.1 := by
      funext t; field_simp
    rw [e]; exact this

end L6

end NetTraffic.OnOffFBM.Lib

end F05Part19

open MeasureTheory ProbabilityTheory Filter Topology NetTraffic.OnOffFBM NNReal ENNReal in
theorem solution
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    (M : ℝ → ℕ) (hM : SourceCount M) (hC2 : Condition2 Fon M)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (src : ∀ T, ℕ → Source (Ω T))
    (hmodel : ∀ T, IsOnOffSuperposition (P T) Fon Foff (M T) (src T)) :
    ∀ Tn : ℕ → ℝ, Tendsto Tn atTop atTop →
      ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (Y : ℕ → ℝ≥0 → Ω₀ → ℝ)
        (Y' : ℝ≥0 → Ω₀ → ℝ),
        IsProbabilityMeasure Q ∧
        (∀ n, Measurable (fun ω (t : ℝ≥0) => Y n t ω)) ∧
        (∀ n, ∀ᵐ ω ∂Q, Continuous (fun t => Y n t ω)) ∧
        (∀ n, Q.map (fun ω (t : ℝ≥0) => Y n t ω) =
          (P (Tn n)).map (fun ω (t : ℝ≥0) => Gnorm Fon Foff α M (src (Tn n)) (Tn n) t ω)) ∧
        IsStdFBM (hurst α) Y' Q ∧
        ∀ᵐ ω ∂Q, UocTendsto (fun n t => Y n t ω) (fun t => sigma0 Fon Foff α * Y' t ω) := by
  exact NetTraffic.OnOffFBM.Lib.theorem_4_lib Fon Foff α αoff hF M hM hC2 Ω P src hmodel
