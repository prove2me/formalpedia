-- Prove2me | solution 2 for Kyprianou.Ch01.lampertiCompoundPoissonToBranchingLawNonexplosive
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T19:04:01.017798+00:00
-- url     : https://prove2.me/submissions/5326122d-afc1-40d8-acf2-fa0d9884852a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false


section Analytic
variable (law : PopulationLaws)

noncomputable def Pr (m k : ℕ) (u : ℝ) : ℝ := (law m u.toNNReal k).toReal

theorem Pr_nonneg (m k : ℕ) (u : ℝ) : 0 ≤ Pr law m k u := ENNReal.toReal_nonneg

theorem Pr_le_one (m k : ℕ) (u : ℝ) : Pr law m k u ≤ 1 := by
  unfold Pr
  have := PMF.coe_le_one (law m u.toNNReal) k
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

theorem markov_tsum (hMarkov : IsPopulationMarkovSemigroup law) (m k : ℕ) (h x : ℝ≥0) :
    law m (h + x) k = ∑' i, law m h i * law i x k := by
  rw [hMarkov m h x, PMF.bind_apply]

theorem law_lip (hMarkov : IsPopulationMarkovSemigroup law) (m k : ℕ) (h x : ℝ≥0) :
    |(law m (h + x) k).toReal - (law m x k).toReal| ≤ 1 - (law m h m).toReal := by
  have hs : law m (h + x) k = law m h m * law m x k +
      ∑' i, ite (i = m) 0 (law m h i * law i x k) := by
    rw [markov_tsum law hMarkov m k h x]
    convert ENNReal.tsum_eq_add_tsum_ite (f := fun i => law m h i * law i x k) m using 2
    refine tsum_congr fun i => ?_; by_cases hi : i = m <;> simp [hi]
  have h1 : (1 : ℝ≥0∞) = law m h m + ∑' i, ite (i = m) 0 (law m h i) := by
    rw [← PMF.tsum_coe (law m h)]
    convert ENNReal.tsum_eq_add_tsum_ite (f := fun i => law m h i) m using 2
    refine tsum_congr fun i => ?_; by_cases hi : i = m <;> simp [hi]
  have hle : ∑' i, ite (i = m) 0 (law m h i * law i x k) ≤ ∑' i, ite (i = m) 0 (law m h i) := by
    refine ENNReal.tsum_le_tsum fun i => ?_
    split_ifs
    · exact le_rfl
    · exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
  have hU : ∑' i, ite (i = m) 0 (law m h i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ le_add_self)
  have hT : ∑' i, ite (i = m) 0 (law m h i * law i x k) ≠ ⊤ := ne_top_of_le_ne_top hU hle
  have ha := PMF.apply_ne_top (law m h) m
  have hb := PMF.apply_ne_top (law m x) k
  have e1 : (law m (h + x) k).toReal = (law m h m).toReal * (law m x k).toReal +
      (∑' i, ite (i = m) 0 (law m h i * law i x k)).toReal := by
    rw [hs, ENNReal.toReal_add (ENNReal.mul_ne_top ha hb) hT, ENNReal.toReal_mul]
  have e2 : (1 : ℝ) = (law m h m).toReal + (∑' i, ite (i = m) 0 (law m h i)).toReal := by
    rw [← ENNReal.toReal_add ha hU, ← h1]; simp
  have e3 := ENNReal.toReal_mono hU hle
  have e4 : (0 : ℝ) ≤ (∑' i, ite (i = m) 0 (law m h i * law i x k)).toReal := ENNReal.toReal_nonneg
  have a0 : (0 : ℝ) ≤ (law m h m).toReal := ENNReal.toReal_nonneg
  have b0 : (0 : ℝ) ≤ (law m x k).toReal := ENNReal.toReal_nonneg
  have b1 : (law m x k).toReal ≤ 1 := by
    have := PMF.coe_le_one (law m x) k
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  rw [abs_le]; constructor <;> nlinarith

variable (rate : ℝ≥0) (offspring : PMF ℕ)

theorem Pr_cont (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring) (m k : ℕ) :
    Continuous (Pr law m k) := by
  have h0 : ContinuousWithinAt (fun t : ℝ => ((law m (Real.toNNReal t)) m).toReal)
      (Set.Ici 0) 0 := (hRates m m).continuousWithinAt
  rw [Metric.continuous_iff]
  intro u ε hε
  rw [Metric.continuousWithinAt_iff] at h0
  obtain ⟨δ, hδ, hδ'⟩ := h0 ε hε
  have key : ∀ a b : ℝ≥0, a ≤ b → (b : ℝ) - a < δ →
      |(law m b k).toReal - (law m a k).toReal| < ε := by
    intro a b hab hba
    have hb : b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
    have hl := law_lip law hMarkov m k (b - a) a
    rw [← hb] at hl
    have hc : ((b - a : ℝ≥0) : ℝ) = (b : ℝ) - a := NNReal.coe_sub hab
    have h2 := hδ' (x := ((b - a : ℝ≥0) : ℝ)) (by simp)
      (by rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _), hc]; exact hba)
    rw [Real.toNNReal_coe] at h2
    simp only [Real.toNNReal_zero, hInitial, PMF.pure_apply, if_true, ENNReal.toReal_one,
      Real.dist_eq] at h2
    have := (abs_lt.1 h2).1
    linarith
  refine ⟨δ, hδ, fun v hv => ?_⟩
  rw [Real.dist_eq] at hv ⊢
  unfold Pr
  have hm : |((v.toNNReal : ℝ≥0) : ℝ) - ((u.toNNReal : ℝ≥0) : ℝ)| < δ := by
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    exact lt_of_le_of_lt (abs_max_sub_max_le_abs _ _ _) hv
  rcases le_total u.toNNReal v.toNNReal with h | h
  · exact key _ _ h (lt_of_le_of_lt (le_abs_self _) hm)
  · rw [abs_sub_comm]
    refine key _ _ h (lt_of_le_of_lt (le_abs_self _) ?_)
    rwa [abs_sub_comm]

theorem markov_fin (hMarkov : IsPopulationMarkovSemigroup law) (m k : ℕ) (h x : ℝ)
    (hh : 0 ≤ h) (hx : 0 ≤ x) (S : Finset ℕ) :
    ∑ i ∈ S, Pr law m i h * Pr law i k x ≤ Pr law m k (h + x) := by
  unfold Pr
  rw [Real.toNNReal_add hh hx]
  have ht := markov_tsum law hMarkov m k h.toNNReal x.toNNReal
  simp_rw [← ENNReal.toReal_mul]
  rw [← ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)), ht]
  exact ENNReal.toReal_mono (ht ▸ PMF.apply_ne_top _ _) (ENNReal.sum_le_tsum S)

open scoped Topology

theorem rate_diag (hRates : IsBranchingRateGenerator law rate offspring) (y : ℕ) :
    HasDerivWithinAt (Pr law y y) (-((rate : ℝ) * y)) (Set.Ici 0) 0 := by
  have := hRates y y
  simp only [if_true] at this
  exact this

theorem rate_off (hRates : IsBranchingRateGenerator law rate offspring)
    (y j : ℕ) (hj : y - 1 + j ≠ y) :
    HasDerivWithinAt (Pr law y (y - 1 + j)) ((rate : ℝ) * y * (offspring j).toReal)
      (Set.Ici 0) 0 := by
  have := hRates y (y - 1 + j)
  rw [if_neg hj, if_pos (by omega)] at this
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy; simp at this ⊢; exact this
  · have e : y - 1 + j + 1 - y = j := by omega
    rw [e] at this; exact this

theorem tendsto_div_of_deriv {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivWithinAt f f' (Set.Ici 0) 0) :
    Tendsto (fun h => (f h - f 0) / h) (𝓝[>] 0) (𝓝 f') := by
  have := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0:ℝ)) (by simp)).1
    (hf.mono Set.Ioi_subset_Ici_self)
  refine this.congr fun h => ?_
  rw [slope_def_field, sub_zero]

noncomputable def gfun (y k : ℕ) (u : ℝ) : ℝ :=
  (rate : ℝ) * y * ∑' j, (offspring j).toReal * Pr law (y - 1 + j) k u

theorem off_summable : Summable (fun j => (offspring j).toReal) :=
  ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)

theorem inner_summable (y k : ℕ) (u : ℝ) :
    Summable (fun j => (offspring j).toReal * Pr law (y - 1 + j) k u) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg ENNReal.toReal_nonneg (Pr_nonneg _ _ _ _))
    (fun j => mul_le_of_le_one_right ENNReal.toReal_nonneg (Pr_le_one _ _ _ _))
    (off_summable offspring)

theorem gfun_cont (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring) (y k : ℕ) :
    Continuous (gfun law rate offspring y k) := by
  unfold gfun
  refine continuous_const.mul (continuous_tsum (fun j => continuous_const.mul
    (Pr_cont law rate offspring hMarkov hInitial hRates _ _)) (off_summable offspring)
    (fun j u => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (Pr_nonneg _ _ _ _))]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (Pr_le_one _ _ _ _)

theorem gfun_nonneg (y k : ℕ) (u : ℝ) : 0 ≤ gfun law rate offspring y k u :=
  mul_nonneg (by positivity) (tsum_nonneg fun j => mul_nonneg ENNReal.toReal_nonneg
    (Pr_nonneg _ _ _ _))

theorem lower_step (hMarkov : IsPopulationMarkovSemigroup law) (y k : ℕ) (x h : ℝ)
    (hx : 0 ≤ x) (hh : 0 < h) (F : Finset ℕ) :
    Real.exp ((rate : ℝ) * y * x) * Pr law y k x *
        (Real.exp ((rate : ℝ) * y * h) * Pr law y y h - 1) +
      Real.exp ((rate : ℝ) * y * (x + h)) * ∑ j ∈ F.filter (fun j => y - 1 + j ≠ y),
        Pr law y (y - 1 + j) h * Pr law (y - 1 + j) k x
    ≤ Real.exp ((rate : ℝ) * y * (x + h)) * Pr law y k (x + h) -
      Real.exp ((rate : ℝ) * y * x) * Pr law y k x := by
  have hm := markov_fin law hMarkov y k h x hh.le hx
    (insert y ((F.filter (fun j => y - 1 + j ≠ y)).image (fun j => y - 1 + j)))
  rw [Finset.sum_insert (by simp), Finset.sum_image (by intro a _ b _ hab; simp at hab; omega)]
    at hm
  rw [add_comm h x] at hm
  have e : Real.exp ((rate : ℝ) * y * (x + h)) =
      Real.exp ((rate : ℝ) * y * x) * Real.exp ((rate : ℝ) * y * h) := by
    rw [mul_add, Real.exp_add]
  have key : 0 ≤ Real.exp ((rate : ℝ) * y * (x + h)) * (Pr law y k (x + h) -
      (Pr law y y h * Pr law y k x + ∑ j ∈ F.filter (fun j => y - 1 + j ≠ y),
        Pr law y (y - 1 + j) h * Pr law (y - 1 + j) k x)) :=
    mul_nonneg (Real.exp_pos _).le (by linarith)
  rw [e] at key ⊢
  linear_combination key

theorem lower_tendsto (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring) (y k : ℕ) (x : ℝ) (F : Finset ℕ) :
    Tendsto (fun h => Real.exp ((rate : ℝ) * y * x) * Pr law y k x *
        ((Real.exp ((rate : ℝ) * y * h) * Pr law y y h - 1) / h) +
      Real.exp ((rate : ℝ) * y * (x + h)) * ∑ j ∈ F.filter (fun j => y - 1 + j ≠ y),
        (Pr law y (y - 1 + j) h / h) * Pr law (y - 1 + j) k x) (𝓝[>] 0)
      (𝓝 (Real.exp ((rate : ℝ) * y * x) * Pr law y k x * 0 +
        Real.exp ((rate : ℝ) * y * x) * ∑ j ∈ F.filter (fun j => y - 1 + j ≠ y),
          ((rate : ℝ) * y * (offspring j).toReal) * Pr law (y - 1 + j) k x)) := by
  have h0 : Pr law y y 0 = 1 := by simp [Pr, hInitial]
  have hd := tendsto_div_of_deriv ((((hasDerivAt_id' (0:ℝ)).const_mul
    ((rate : ℝ) * y)).exp).hasDerivWithinAt.mul (rate_diag law rate offspring hRates y))
  have hd' : Tendsto (fun h => (Real.exp ((rate : ℝ) * y * h) * Pr law y y h - 1) / h)
      (𝓝[>] 0) (𝓝 0) := by
    convert hd using 1
    · funext h; simp [h0]
    · simp [h0]
  have hoff : ∀ j ∈ F.filter (fun j => y - 1 + j ≠ y), Tendsto
      (fun h => (Pr law y (y - 1 + j) h / h) * Pr law (y - 1 + j) k x) (𝓝[>] 0)
      (𝓝 (((rate : ℝ) * y * (offspring j).toReal) * Pr law (y - 1 + j) k x)) := by
    intro j hj
    have hj' : y - 1 + j ≠ y := (Finset.mem_filter.1 hj).2
    have hz : Pr law y (y - 1 + j) 0 = 0 := by simp [Pr, hInitial, PMF.pure_apply, hj']
    have := tendsto_div_of_deriv (rate_off law rate offspring hRates y j hj')
    rw [hz] at this
    simp only [sub_zero] at this
    exact this.mul tendsto_const_nhds
  have hE : Tendsto (fun h => Real.exp ((rate : ℝ) * y * (x + h))) (𝓝[>] 0)
      (𝓝 (Real.exp ((rate : ℝ) * y * x))) := by
    have hc : Continuous (fun h : ℝ => Real.exp ((rate : ℝ) * y * (x + h))) := by fun_prop
    have := (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  exact (tendsto_const_nhds.mul hd').add (hE.mul (tendsto_finset_sum _ hoff))

theorem Pr_zero (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y) (y k : ℕ) :
    Pr law y k 0 = if y = k then 1 else 0 := by
  by_cases h : y = k
  · subst h; simp [Pr, hInitial]
  · simp [Pr, hInitial, PMF.pure_apply, h, Ne.symm h]

theorem law_comparison (hNoZeroJumps : offspring 1 = 0)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring) (y k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (if y = k then (1 : ℝ) else 0) +
        ∫ s in (0 : ℝ)..t, Real.exp ((rate : ℝ) * y * s) * gfun law rate offspring y k s
      ≤ Real.exp ((rate : ℝ) * y * t) * Pr law y k t := by
  have hg := gfun_cont law rate offspring hMarkov hInitial hRates y k
  have hcI : Continuous (fun s => Real.exp ((rate : ℝ) * y * s) * gfun law rate offspring y k s) :=
    (by fun_prop : Continuous fun s : ℝ => Real.exp ((rate : ℝ) * y * s)).mul hg
  have hP := Pr_cont law rate offspring hMarkov hInitial hRates y k
  have hB : ∀ u, HasDerivAt (fun u => -((if y = k then (1 : ℝ) else 0) +
      ∫ s in (0 : ℝ)..u, Real.exp ((rate : ℝ) * y * s) * gfun law rate offspring y k s))
      (-(Real.exp ((rate : ℝ) * y * u) * gfun law rate offspring y k u)) u :=
    fun u => ((hcI.integral_hasStrictDerivAt 0 u).hasDerivAt.const_add _).neg
  have htend : ∀ x : ℝ, Tendsto (fun z => z - x) (𝓝[>] x) (𝓝[>] 0) := by
    intro x
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (fun z : ℝ => z - x) := by fun_prop
      have := (hc.tendsto x).mono_left (nhdsWithin_le_nhds (s := Set.Ioi x))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.2 (Set.mem_Ioi.1 hz)
  have key := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun u => -(Real.exp ((rate : ℝ) * y * u) * Pr law y k u)) (a := 0) (b := t)
    (B := fun u => -((if y = k then (1 : ℝ) else 0) +
      ∫ s in (0 : ℝ)..u, Real.exp ((rate : ℝ) * y * s) * gfun law rate offspring y k s))
    (B' := fun u => -(Real.exp ((rate : ℝ) * y * u) * gfun law rate offspring y k u))
    (((by fun_prop : Continuous fun s : ℝ => Real.exp ((rate : ℝ) * y * s)).mul hP).neg.continuousOn)
    (by simp [Pr_zero law hInitial])
    ((continuous_iff_continuousAt.2 fun u => (hB u).continuousAt).continuousOn)
    (fun x _ => (hB x).hasDerivWithinAt) ?bound (x := t) ⟨ht, le_rfl⟩
  · simpa using key
  intro x hx r hr
  have hx0 : 0 ≤ x := hx.1
  have hsum := (inner_summable law offspring y k x).hasSum
  have hT := (hsum.tendsto_sum_nat.const_mul ((rate : ℝ) * y)).const_mul
    (Real.exp ((rate : ℝ) * y * x))
  have hr' : -r < Real.exp ((rate : ℝ) * y * x) * ((rate : ℝ) * y *
      ∑' j, (offspring j).toReal * Pr law (y - 1 + j) k x) := by
    simp only [gfun] at hr; linarith
  obtain ⟨n, hn⟩ := (hT.eventually (lt_mem_nhds hr')).exists
  have hlim := lower_tendsto law rate offspring hInitial hRates y k x (Finset.range n)
  have hV : Real.exp ((rate : ℝ) * y * x) * Pr law y k x * 0 +
      Real.exp ((rate : ℝ) * y * x) * ∑ j ∈ (Finset.range n).filter (fun j => y - 1 + j ≠ y),
        ((rate : ℝ) * y * (offspring j).toReal) * Pr law (y - 1 + j) k x =
      Real.exp ((rate : ℝ) * y * x) * ((rate : ℝ) * y *
        ∑ j ∈ Finset.range n, (offspring j).toReal * Pr law (y - 1 + j) k x) := by
    rw [mul_zero, zero_add, Finset.sum_filter_of_ne]
    · congr 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    · intro j _ hne heq
      apply hne
      rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy; simp
      · have hj1 : j = 1 := by omega
        subst hj1; simp [hNoZeroJumps]
  rw [hV] at hlim
  have hev := hlim.eventually (lt_mem_nhds hn)
  refine Filter.Eventually.frequently ?_
  filter_upwards [(htend x).eventually hev, self_mem_nhdsWithin] with z hz hzx
  have hpos : 0 < z - x := sub_pos.2 (Set.mem_Ioi.1 hzx)
  have hl := lower_step law rate hMarkov y k x (z - x) hx0 hpos (Finset.range n)
  rw [add_sub_cancel] at hl
  have hdiv := div_le_div_of_nonneg_right hl hpos.le
  have hsd : ∑ j ∈ (Finset.range n).filter (fun j => y - 1 + j ≠ y),
      (Pr law y (y - 1 + j) (z - x) / (z - x)) * Pr law (y - 1 + j) k x =
      (∑ j ∈ (Finset.range n).filter (fun j => y - 1 + j ≠ y),
        Pr law y (y - 1 + j) (z - x) * Pr law (y - 1 + j) k x) / (z - x) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsd] at hz
  rw [slope_def_field]
  have e1 : (Real.exp ((rate : ℝ) * y * x) * Pr law y k x *
        (Real.exp ((rate : ℝ) * y * (z - x)) * Pr law y y (z - x) - 1) +
      Real.exp ((rate : ℝ) * y * z) * ∑ j ∈ (Finset.range n).filter (fun j => y - 1 + j ≠ y),
        Pr law y (y - 1 + j) (z - x) * Pr law (y - 1 + j) k x) / (z - x) =
      Real.exp ((rate : ℝ) * y * x) * Pr law y k x *
        ((Real.exp ((rate : ℝ) * y * (z - x)) * Pr law y y (z - x) - 1) / (z - x)) +
      Real.exp ((rate : ℝ) * y * (x + (z - x))) *
        ((∑ j ∈ (Finset.range n).filter (fun j => y - 1 + j ≠ y),
        Pr law y (y - 1 + j) (z - x) * Pr law (y - 1 + j) k x) / (z - x)) := by
    rw [add_sub_cancel]; ring
  rw [e1] at hdiv
  have e2 : (-(Real.exp ((rate : ℝ) * y * z) * Pr law y k z) -
      -(Real.exp ((rate : ℝ) * y * x) * Pr law y k x)) / (z - x) =
      -((Real.exp ((rate : ℝ) * y * z) * Pr law y k z -
        Real.exp ((rate : ℝ) * y * x) * Pr law y k x) / (z - x)) := by ring
  rw [e2]
  linarith

theorem law_firstJump'
    (hNoZeroJumps : offspring 1 = 0)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring) (y : ℕ) (t : ℝ≥0) (k : ℕ) :
    (if y = k then ENNReal.ofReal (Real.exp (-((rate : ℝ) * y * t))) else 0) +
    ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((rate : ℝ) * y * Real.exp (-((rate : ℝ) * y * s))) *
      ∑' j : ℕ, offspring j * law (y - 1 + j) (Real.toNNReal (t - s)) k ≤ law y t k := by
  have hg := gfun_cont law rate offspring hMarkov hInitial hRates y k
  have hpt : ∀ s : ℝ, ENNReal.ofReal ((rate : ℝ) * y * Real.exp (-((rate : ℝ) * y * s))) *
      ∑' j : ℕ, offspring j * law (y - 1 + j) (Real.toNNReal (t - s)) k =
      ENNReal.ofReal (Real.exp (-((rate : ℝ) * y * s)) * gfun law rate offspring y k (t - s)) := by
    intro s
    have hS : ∑' j : ℕ, offspring j * law (y - 1 + j) (Real.toNNReal (t - s)) k =
        ENNReal.ofReal (∑' j, (offspring j).toReal * Pr law (y - 1 + j) k (t - s)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg ENNReal.toReal_nonneg
        (Pr_nonneg _ _ _ _)) (inner_summable law offspring y k _)]
      refine tsum_congr fun j => ?_
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
        Pr, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    rw [hS, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; unfold gfun; ring
  have hcont : Continuous (fun s : ℝ => Real.exp (-((rate : ℝ) * y * s)) *
      gfun law rate offspring y k (t - s)) :=
    (by fun_prop : Continuous fun s : ℝ => Real.exp (-((rate : ℝ) * y * s))).mul
      (hg.comp (continuous_const.sub continuous_id))
  have hnn : ∀ s : ℝ, 0 ≤ Real.exp (-((rate : ℝ) * y * s)) * gfun law rate offspring y k (t - s) :=
    fun s => mul_nonneg (Real.exp_pos _).le (gfun_nonneg _ _ _ _ _ _)
  rw [lintegral_congr hpt,
    ← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc (Filter.Eventually.of_forall hnn),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  have hite : (if y = k then ENNReal.ofReal (Real.exp (-((rate : ℝ) * y * t))) else 0) =
      ENNReal.ofReal ((if y = k then (1 : ℝ) else 0) * Real.exp (-((rate : ℝ) * y * t))) := by
    split_ifs <;> simp
  have hI0 : 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (-((rate : ℝ) * y * s)) *
      gfun law rate offspring y k (t - s) :=
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun s _ => hnn s
  rw [hite, ← ENNReal.ofReal_add (mul_nonneg (by split_ifs <;> norm_num) (Real.exp_pos _).le) hI0,
    ← ENNReal.ofReal_toReal (PMF.apply_ne_top (law y t) k)]
  refine ENNReal.ofReal_le_ofReal ?_
  have I1 : ∫ s in (0 : ℝ)..t, Real.exp (-((rate : ℝ) * y * s)) *
      gfun law rate offspring y k (t - s) = Real.exp (-((rate : ℝ) * y * t)) *
      ∫ s in (0 : ℝ)..t, Real.exp ((rate : ℝ) * y * s) * gfun law rate offspring y k s := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := (t : ℝ))
      (fun s => Real.exp (-((rate : ℝ) * y * (t - s))) * gfun law rate offspring y k s) (t : ℝ)
    simp only [sub_sub_cancel, sub_self, sub_zero] at this
    rw [this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hc := law_comparison law rate offspring hNoZeroJumps hMarkov hInitial hRates y k t
    (NNReal.coe_nonneg t)
  have hm := mul_le_mul_of_nonneg_left hc (Real.exp_pos (-((rate : ℝ) * y * t))).le
  rw [mul_add, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hm
  have hPt : Pr law y k (t : ℝ) = (law y t k).toReal := by simp [Pr]
  rw [I1, ← hPt]
  linarith

end Analytic

/-- First-jump (backward integral) operator of the branching Q-matrix. -/
noncomputable def firstJumpOp (rate : ℝ≥0) (offspring : PMF ℕ)
    (G : ℕ → ℝ≥0 → ℕ → ℝ≥0∞) (y : ℕ) (t : ℝ≥0) (k : ℕ) : ℝ≥0∞ :=
  (if y = k then ENNReal.ofReal (Real.exp (-((rate : ℝ) * y * t))) else 0) +
  ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal ((rate : ℝ) * y * Real.exp (-((rate : ℝ) * y * s))) *
    ∑' j : ℕ, offspring j * G (y - 1 + j) (Real.toNNReal (t - s)) k

theorem firstJumpOp_mono (rate : ℝ≥0) (offspring : PMF ℕ) {G H : ℕ → ℝ≥0 → ℕ → ℝ≥0∞}
    (h : ∀ y t k, G y t k ≤ H y t k) (y : ℕ) (t : ℝ≥0) (k : ℕ) :
    firstJumpOp rate offspring G y t k ≤ firstJumpOp rate offspring H y t k := by
  unfold firstJumpOp
  gcongr with s hs j
  exact h _ _ _

/-- Backward Kolmogorov inequality (integral form) for the branching transition function. -/
theorem law_firstJump
    (rate : ℝ≥0) (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0) (law : PopulationLaws)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring) (y : ℕ) (t : ℝ≥0) (k : ℕ) :
    firstJumpOp rate offspring (fun y t k => law y t k) y t k ≤ law y t k := by
  unfold firstJumpOp
  exact law_firstJump' law rate offspring hNoZeroJumps hMarkov hInitial hRates y t k

theorem eq_of_le_of_tsum_eq {f g : ℕ → ℝ≥0∞} (h : ∀ k, f k ≤ g k) (hf : ∑' k, f k = 1)
    (hg : ∑' k, g k = 1) (k : ℕ) : f k = g k := by
  by_contra hne
  have hlt : f k < g k := lt_of_le_of_ne (h k) hne
  have := ENNReal.tsum_lt_tsum (by rw [hf]; exact ENNReal.one_ne_top) h hlt
  rw [hf, hg] at this
  exact lt_irrefl _ this

theorem recOcc_pos {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (δ : ℝ≥0) (hδ : 0 < δ)
    (hX : ∀ t : ℝ≥0, t < δ → X t ω = X 0 ω) (s : ℝ≥0) (hs : 0 < s) :
    0 < reciprocalOccupation X s ω := by
  unfold reciprocalOccupation
  set m : ℝ := min (s : ℝ) ((δ:ℝ)/2) with hm
  have hd : (0:ℝ) < δ := by exact_mod_cast hδ
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hm0 : 0 < m := lt_min hs' (by linarith)
  have hsub : Set.Ioc (0:ℝ) m ⊆ Set.Ioc (0:ℝ) s := Set.Ioc_subset_Ioc_right (min_le_left _ _)
  have hc : ∫⁻ x in Set.Ioc (0:ℝ) m, (ENNReal.ofReal (X (Real.toNNReal x) ω : ℝ))⁻¹ ∂volume =
      (ENNReal.ofReal (X 0 ω : ℝ))⁻¹ * ENNReal.ofReal m := by
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (ENNReal.ofReal (X 0 ω : ℝ))⁻¹)]
    · simp
    · intro x hx
      have : Real.toNNReal x < δ := by
        have hd : (0:ℝ) < δ := by exact_mod_cast hδ
        have h1 : x < δ := lt_of_le_of_lt hx.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        exact (Real.toNNReal_lt_iff_lt_coe hx.1.le).2 h1
      simp only [hX _ this]
  refine lt_of_lt_of_le ?_ (lintegral_mono_set hsub)
  rw [hc]
  exact ENNReal.mul_pos (by simp) (by simpa using hm0)

theorem cpb_zero {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) (δ : ℝ≥0) (hδ : 0 < δ)
    (hX : ∀ t : ℝ≥0, t < δ → X t ω = X 0 ω) :
    compoundPoissonToBranching X 0 ω = X 0 ω := by
  have h1 : inverseReciprocalOccupation X 0 ω = ((0:ℝ≥0) : WithTop ℝ≥0) := by
    unfold inverseReciprocalOccupation
    have hpos := recOcc_pos X ω δ hδ hX
    have hex : ∃ s : ℝ≥0, ((0:ℝ≥0) : ℝ≥0∞) < reciprocalOccupation X s ω := ⟨1, by simpa using hpos 1 one_pos⟩
    rw [if_pos hex]
    congr 1
    apply le_antisymm _ (zero_le)
    by_contra hcon
    have hlt : 0 < sInf {s : ℝ≥0 | ((0:ℝ≥0) : ℝ≥0∞) < reciprocalOccupation X s ω} := not_le.1 hcon
    have hhalf : sInf {s : ℝ≥0 | ((0:ℝ≥0) : ℝ≥0∞) < reciprocalOccupation X s ω} / 2 <
        sInf {s : ℝ≥0 | ((0:ℝ≥0) : ℝ≥0∞) < reciprocalOccupation X s ω} := NNReal.half_lt_self hlt.ne'
    have := csInf_le (OrderBot.bddBelow _) (show (sInf {s : ℝ≥0 | ((0:ℝ≥0) : ℝ≥0∞) < reciprocalOccupation X s ω} / 2) ∈ {s : ℝ≥0 | ((0:ℝ≥0) : ℝ≥0∞) < reciprocalOccupation X s ω} from by
      simpa using hpos _ (by positivity))
    exact absurd hhalf (not_lt.2 this)
  unfold compoundPoissonToBranching
  rw [h1, min_eq_left (by exact bot_le)]

theorem jc_zero {Ω : Type*} (τ : ℕ → Ω → ℝ) (ω : Ω) (u : ℝ)
    (hu : u < τ 0 ω) : ProbabilityTheory.jumpCount (fun n => ProbabilityTheory.arrival τ n ω) u = 0 := by
  unfold ProbabilityTheory.jumpCount
  refine Nat.sInf_eq_zero.2 (Or.inl ?_)
  show u < ProbabilityTheory.arrival τ 0 ω
  simpa [ProbabilityTheory.arrival] using hu

theorem cp_const {Ω : Type*} (y : ℕ) (τ marks : ℕ → Ω → ℝ) (ω : Ω)
    (h : 0 < τ 0 ω) : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
      integerCompoundPoisson y τ marks t ω = integerCompoundPoisson y τ marks 0 ω := by
  refine ⟨(τ 0 ω).toNNReal, by simpa using h, fun t ht => ?_⟩
  have ht' : (t:ℝ) < τ 0 ω := Real.lt_toNNReal_iff_coe_lt.1 ht
  have h0 : ((0:ℝ≥0):ℝ) < τ 0 ω := by simpa using h
  unfold integerCompoundPoisson ProbabilityTheory.compoundPoisson ProbabilityTheory.piecewisePath
  rw [jc_zero τ ω _ ht', jc_zero τ ω _ h0]
  simp

theorem cp_zero {Ω : Type*} (y : ℕ) (τ marks : ℕ → Ω → ℝ) (ω : Ω)
    (h : 0 < τ 0 ω) : integerCompoundPoisson y τ marks 0 ω = (y : ℤ) := by
  have h0 : ((0:ℝ≥0):ℝ) < τ 0 ω := by simpa using h
  unfold integerCompoundPoisson ProbabilityTheory.compoundPoisson ProbabilityTheory.piecewisePath
  rw [jc_zero τ ω _ h0]
  simp

theorem tau_pos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (τ : ℕ → Ω → ℝ) (r : ℝ≥0)
  (hr0 : 0 < r) (h : HasLaw (τ 0) (expMeasure r) μ) : ∀ᵐ ω ∂μ, 0 < τ 0 ω := by
  have h1 : μ {ω | τ 0 ω ≤ 0} = 0 := by
    have := h.map_eq
    have hm := h.aemeasurable
    have e : μ {ω | τ 0 ω ≤ 0} = (μ.map (τ 0)) (Set.Iic 0) := by
      rw [Measure.map_apply_of_aemeasurable hm measurableSet_Iic]; rfl
    rw [e, this]
    have hr : (0:ℝ) < r := by exact_mod_cast hr0
    have := isProbabilityMeasure_expMeasure hr
    have hc := cdf_expMeasure_eq hr 0
    rw [cdf_eq_real (expMeasure r) 0] at hc
    simp at hc
    exact (ENNReal.toReal_eq_zero_iff _).1 hc |>.resolve_right (measure_ne_top _ _)
  have : ∀ᵐ ω ∂μ, ¬ (τ 0 ω ≤ 0) := measure_eq_zero_iff_ae_notMem.1 h1
  filter_upwards [this] with ω hω using not_le.1 hω

theorem jc_preimage_eq {Ω : Type*} (T : ℕ → Ω → ℝ) (n : ℕ) :
    (fun p : ℝ≥0 × Ω => jumpCount (fun i => T i p.2) (p.1 : ℝ)) ⁻¹' {n} =
      ({p | p.1 < T n p.2} ∩ ⋂ m ∈ Finset.range n, {p | T m p.2 ≤ p.1}) ∪
      ({p | n = 0} ∩ ⋂ m : ℕ, {p | T m p.2 ≤ p.1}) := by
  ext ⟨s, ω⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
    Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, jumpCount]
  constructor
  · intro h
    by_cases hS : ({i | (s : ℝ) < T i ω} : Set ℕ).Nonempty
    · left
      refine ⟨?_, fun m hm => ?_⟩
      · have := Nat.sInf_mem hS; rw [h] at this; exact this
      · have := Nat.notMem_of_lt_sInf (s := {i | (s : ℝ) < T i ω}) (by rw [h]; exact hm)
        simpa using this
    · right
      rw [Set.not_nonempty_iff_eq_empty] at hS
      rw [hS, Nat.sInf_empty] at h
      refine ⟨h.symm, fun m => ?_⟩
      have : m ∉ ({i | (s : ℝ) < T i ω} : Set ℕ) := by rw [hS]; simp
      simpa using this
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine le_antisymm (Nat.sInf_le h1) (le_csInf ⟨n, h1⟩ fun m hm => ?_)
      by_contra hc
      exact absurd (h2 m (by omega)) (not_le.2 hm)
    · have : ({i | (s : ℝ) < T i ω} : Set ℕ) = ∅ := by
        ext m; simp [h2 m]
      rw [this, Nat.sInf_empty, h1]

theorem jc_measurable {Ω : Type*} [MeasurableSpace Ω] (T : ℕ → Ω → ℝ)
    (hT : ∀ n, Measurable (T n)) :
    Measurable (fun p : ℝ≥0 × Ω => jumpCount (fun i => T i p.2) (p.1 : ℝ)) := by
  refine measurable_to_countable' fun n => ?_
  rw [jc_preimage_eq]
  have hle : ∀ m, MeasurableSet {p : ℝ≥0 × Ω | T m p.2 ≤ p.1} := fun m =>
    measurableSet_le ((hT m).comp measurable_snd) (measurable_coe_nnreal_real.comp measurable_fst)
  refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_lt (measurable_coe_nnreal_real.comp measurable_fst)
      ((hT n).comp measurable_snd)
  · exact Finset.measurableSet_biInter _ fun m _ => hle m
  · by_cases h : n = 0 <;> simp [h]
  · exact MeasurableSet.iInter hle

theorem jc_right (T : ℕ → ℝ) (s : ℝ) :
    ∃ ε > 0, ∀ s', s ≤ s' → s' < s + ε → jumpCount T s' = jumpCount T s := by
  by_cases hS : ({i | s < T i} : Set ℕ).Nonempty
  · set N := jumpCount T s with hN
    have hNm : s < T N := Nat.sInf_mem hS
    refine ⟨T N - s, by linarith, fun s' h1 h2 => ?_⟩
    have hNm' : s' < T N := by linarith
    refine le_antisymm (Nat.sInf_le hNm') (le_csInf ⟨N, hNm'⟩ fun m hm => ?_)
    by_contra hc
    have := Nat.notMem_of_lt_sInf (s := {i | s < T i}) (lt_of_not_ge hc)
    simp only [Set.mem_setOf_eq, not_lt] at this hm
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    refine ⟨1, one_pos, fun s' h1 _ => ?_⟩
    have : ({i | s' < T i} : Set ℕ) = ∅ := by
      ext m
      have : m ∉ ({i | s < T i} : Set ℕ) := by rw [hS]; simp
      simp only [Set.mem_setOf_eq, not_lt] at this
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith
    simp only [jumpCount, this, hS]

theorem icp_eq {Ω : Type*} (y : ℕ) (τ marks : ℕ → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :
    integerCompoundPoisson y τ marks s ω =
      Int.floor ((y : ℝ) + ∑ i ∈ Finset.range
        (jumpCount (fun n => ProbabilityTheory.arrival τ n ω) (s : ℝ)), marks i ω) := by
  simp [integerCompoundPoisson, compoundPoisson, piecewisePath]

theorem icp_measurable {Ω : Type*} [MeasurableSpace Ω] (y : ℕ) (τ marks : ℕ → Ω → ℝ)
    (hτ : ∀ n, Measurable (τ n)) (hm : ∀ n, Measurable (marks n)) :
    Measurable (fun p : ℝ≥0 × Ω => integerCompoundPoisson y τ marks p.1 p.2) := by
  simp only [icp_eq]
  have hF : Measurable (fun q : Ω × ℕ =>
      Int.floor ((y : ℝ) + ∑ i ∈ Finset.range q.2, marks i q.1)) := by
    refine measurable_from_prod_countable_left fun n => ?_
    have h : Measurable (fun ω => (y : ℝ) + ∑ i ∈ Finset.range n, marks i ω) :=
      measurable_const.add (Finset.measurable_sum _ fun i _ => hm i)
    exact h.floor
  have hA : ∀ n, Measurable (ProbabilityTheory.arrival τ n) := fun n =>
    Finset.measurable_sum _ fun i _ => hτ i
  exact hF.comp (measurable_snd.prodMk (jc_measurable _ hA))

theorem icp_right {Ω : Type*} (y : ℕ) (τ marks : ℕ → Ω → ℝ) (ω : Ω) (s : ℝ≥0) :
    ∃ ε > 0, ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε →
      integerCompoundPoisson y τ marks s' ω = integerCompoundPoisson y τ marks s ω := by
  obtain ⟨ε, hε, h⟩ := jc_right (fun n => ProbabilityTheory.arrival τ n ω) (s : ℝ)
  refine ⟨ε.toNNReal, by simpa using hε, fun s' h1 h2 => ?_⟩
  rw [icp_eq, icp_eq, h (s' : ℝ) (by exact_mod_cast h1)]
  have : (s' : ℝ) < (s : ℝ) + ε := by
    have := (NNReal.coe_lt_coe.2 h2); simpa [hε.le] using this
  exact this

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℤ)

theorem recOcc_measurable (hXm : Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2)) (s : ℝ≥0) :
    Measurable (fun ω => reciprocalOccupation X s ω) := by
  unfold reciprocalOccupation
  have hf : Measurable (fun q : Ω × ℝ => (ENNReal.ofReal (X (Real.toNNReal q.2) q.1 : ℝ))⁻¹) :=
    (measurable_of_countable (fun z : ℤ => (ENNReal.ofReal (z : ℝ))⁻¹)).comp
      (hXm.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  exact hf.lintegral_prod_right'

omit [MeasurableSpace Ω] in
theorem recOcc_mono (ω : Ω) {s s' : ℝ≥0} (h : s ≤ s') :
    reciprocalOccupation X s ω ≤ reciprocalOccupation X s' ω :=
  lintegral_mono_set (Set.Ioc_subset_Ioc_right (by exact_mod_cast h))

omit [MeasurableSpace Ω] in
theorem iro_lt_iff (ω : Ω) (t : ℝ≥0) (x : ℝ≥0∞) :
    ((inverseReciprocalOccupation X t ω : WithTop ℝ≥0) : ℝ≥0∞) < x ↔
      ∃ q : ℚ, (0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < x) ∧
        (t : ℝ≥0∞) < reciprocalOccupation X (q : ℝ).toNNReal ω := by
  unfold inverseReciprocalOccupation
  split_ifs with h
  · constructor
    · intro hlt
      obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      have hq1' : sInf {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} <
          (q : ℝ).toNNReal := ENNReal.coe_lt_coe.1 hq1
      obtain ⟨s, hs, hsq⟩ := (csInf_lt_iff (OrderBot.bddBelow _) h).1 hq1'
      exact ⟨q, ⟨hq0, hq2⟩, lt_of_lt_of_le hs (recOcc_mono X ω hsq.le)⟩
    · rintro ⟨q, ⟨_, hq⟩, hI⟩
      refine lt_of_le_of_lt ?_ hq
      have : sInf {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} ≤ (q : ℝ).toNNReal :=
        csInf_le (OrderBot.bddBelow _) hI
      exact ENNReal.coe_le_coe.2 this
  · constructor
    · intro hlt; exact absurd hlt (not_lt.2 le_top)
    · rintro ⟨q, _, hI⟩; exact absurd ⟨_, hI⟩ h

omit [MeasurableSpace Ω] in
theorem fnp_lt_iff
    (hXr : ∀ ω s, ∃ ε > 0, ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε → X s' ω = X s ω)
    (ω : Ω) (x : ℝ≥0∞) :
    ((firstNegativePassage X ω : WithTop ℝ≥0) : ℝ≥0∞) < x ↔
      ∃ q : ℚ, (0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < x) ∧
        (0 < (q : ℝ).toNNReal ∧ X (q : ℝ).toNNReal ω < 0) := by
  unfold firstNegativePassage
  split_ifs with h
  · constructor
    · intro hlt
      obtain ⟨q1, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      have hq1' : sInf {t : ℝ≥0 | 0 < t ∧ X t ω < 0} < (q1 : ℝ).toNNReal := ENNReal.coe_lt_coe.1 hq1
      obtain ⟨s, ⟨hs0, hs⟩, hsq⟩ := (csInf_lt_iff (OrderBot.bddBelow _) h).1 hq1'
      obtain ⟨ε, hε, hX⟩ := hXr ω s
      have hb : ((s : ℝ≥0) : ℝ≥0∞) < ((min (q1 : ℝ).toNNReal (s + ε) : ℝ≥0) : ℝ≥0∞) := by
        exact_mod_cast lt_min hsq (lt_add_of_pos_right s hε)
      obtain ⟨q, hq0, hq3, hq4⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hb
      have hq3' : s < (q : ℝ).toNNReal := by exact_mod_cast hq3
      have hq4' : (q : ℝ).toNNReal < min (q1 : ℝ).toNNReal (s + ε) := by exact_mod_cast hq4
      refine ⟨q, ⟨hq0, lt_trans ?_ hq2⟩, lt_trans hs0 hq3', ?_⟩
      · exact_mod_cast lt_of_lt_of_le hq4' (min_le_left _ _)
      · rw [hX _ hq3'.le (lt_of_lt_of_le hq4' (min_le_right _ _))]; exact hs
    · rintro ⟨q, ⟨_, hq⟩, hI⟩
      refine lt_of_le_of_lt ?_ hq
      have : sInf {t : ℝ≥0 | 0 < t ∧ X t ω < 0} ≤ (q : ℝ).toNNReal :=
        csInf_le (OrderBot.bddBelow _) hI
      exact ENNReal.coe_le_coe.2 this
  · constructor
    · intro hlt; exact absurd hlt (not_lt.2 le_top)
    · rintro ⟨q, _, hI⟩; exact absurd ⟨_, hI⟩ h

omit [MeasurableSpace Ω] in
theorem cpb_eq_H (t : ℝ≥0) (ω : Ω) :
    compoundPoissonToBranching X t ω =
      (if (min ((inverseReciprocalOccupation X t ω : WithTop ℝ≥0) : ℝ≥0∞)
          ((firstNegativePassage X ω : WithTop ℝ≥0) : ℝ≥0∞)) = ⊤ then 0 else
        X (ENNReal.toNNReal (min ((inverseReciprocalOccupation X t ω : WithTop ℝ≥0) : ℝ≥0∞)
          ((firstNegativePassage X ω : WithTop ℝ≥0) : ℝ≥0∞))) ω) := by
  unfold compoundPoissonToBranching
  change _ = (if ((min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) :
      WithTop ℝ≥0) : ℝ≥0∞) = ⊤ then 0 else
      X (ENNReal.toNNReal ((min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) :
      WithTop ℝ≥0) : ℝ≥0∞)) ω)
  generalize min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) = m
  rcases m with _ | s
  · rfl
  · change _ = (if (s : ℝ≥0∞) = ⊤ then 0 else X (ENNReal.toNNReal (s : ℝ≥0∞)) ω)
    simp

theorem cpb_measurable (hXm : Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2))
    (hXr : ∀ ω s, ∃ ε > 0, ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε → X s' ω = X s ω) (t : ℝ≥0) :
    Measurable (compoundPoissonToBranching X t) := by
  have hA : Measurable (fun ω => ((inverseReciprocalOccupation X t ω : WithTop ℝ≥0) : ℝ≥0∞)) := by
    refine measurable_of_Iio fun x => ?_
    have : (fun ω => ((inverseReciprocalOccupation X t ω : WithTop ℝ≥0) : ℝ≥0∞)) ⁻¹' Iio x =
        ⋃ q : ℚ, ⋃ (_ : 0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < x),
          {ω | (t : ℝ≥0∞) < reciprocalOccupation X (q : ℝ).toNNReal ω} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]; exact iro_lt_iff X ω t x
    rw [this]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const (recOcc_measurable X hXm _)
  have hB : Measurable (fun ω => ((firstNegativePassage X ω : WithTop ℝ≥0) : ℝ≥0∞)) := by
    refine measurable_of_Iio fun x => ?_
    have : (fun ω => ((firstNegativePassage X ω : WithTop ℝ≥0) : ℝ≥0∞)) ⁻¹' Iio x =
        ⋃ q : ℚ, ⋃ (_ : 0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < x),
          ⋃ (_ : 0 < (q : ℝ).toNNReal), {ω | X (q : ℝ).toNNReal ω < 0} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]; exact fnp_lt_iff X hXr ω x
    rw [this]
    have hs : ∀ u : ℝ≥0, Measurable (fun ω => X u ω) := fun u =>
      hXm.comp (measurable_const.prodMk measurable_id)
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
      measurableSet_lt (hs _) measurable_const
  have hm := hA.min hB
  have heq : compoundPoissonToBranching X t = fun ω => _ := funext (cpb_eq_H X t)
  rw [heq]
  refine Measurable.ite (hm (measurableSet_singleton ⊤)) measurable_const ?_
  exact hXm.comp (hm.ennreal_toNNReal.prodMk measurable_id)

end Generic

section Shift
variable {Ω Ω' : Type*} (X : ℝ≥0 → Ω → ℤ) (X' : ℝ≥0 → Ω' → ℤ) (ω : Ω) (ω' : Ω')

theorem recOcc_before (a : ℝ≥0) (y : ℕ) (hpre : ∀ s : ℝ≥0, s < a → X s ω = y)
    (s : ℝ≥0) (hs : s ≤ a) :
    reciprocalOccupation X s ω = (s : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ := by
  unfold reciprocalOccupation
  rw [← setLIntegral_congr (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := (s:ℝ)))]
  rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => (y : ℝ≥0∞)⁻¹) ?_]
  · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_coe_nnreal, mul_comm]
  · intro u hu
    have hlt : u.toNNReal < a := by
      rw [Real.toNNReal_lt_iff_lt_coe hu.1.le]
      exact lt_of_lt_of_le hu.2 (by exact_mod_cast hs)
    show (ENNReal.ofReal (X u.toNNReal ω : ℝ))⁻¹ = (y : ℝ≥0∞)⁻¹
    rw [hpre _ hlt]
    simp

theorem recOcc_after (a : ℝ≥0) (y : ℕ) (hpre : ∀ s : ℝ≥0, s < a → X s ω = y)
    (hpost : ∀ s : ℝ≥0, a ≤ s → X s ω = X' (s - a) ω') (s : ℝ≥0) (hs : a ≤ s) :
    reciprocalOccupation X s ω = (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ +
      reciprocalOccupation X' (s - a) ω' := by
  have hsplit : Set.Ioc (0 : ℝ) (s : ℝ) = Set.Ioc 0 (a : ℝ) ∪ Set.Ioc (a : ℝ) (s : ℝ) :=
    (Set.Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg a) (by exact_mod_cast hs)).symm
  have h1 := recOcc_before X ω a y hpre a le_rfl
  unfold reciprocalOccupation at h1 ⊢
  rw [hsplit, lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl), h1]
  congr 1
  have := (measurePreserving_add_right (volume : Measure ℝ) (a : ℝ)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (a : ℝ))
    (fun u => (ENNReal.ofReal (X (Real.toNNReal u) ω : ℝ))⁻¹) (Set.Ioc (a : ℝ) (s : ℝ))
  rw [← this, Set.preimage_add_const_Ioc, sub_self, NNReal.coe_sub hs]
  refine setLIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  have hv0 : 0 ≤ v := hv.1.le
  have e : (v + a).toNNReal = v.toNNReal + a := by
    rw [Real.toNNReal_add hv0 (NNReal.coe_nonneg a), Real.toNNReal_coe]
  rw [e, hpost _ (le_add_self), add_tsub_cancel_right]

theorem sInf_image_add (a : ℝ≥0) (S : Set ℝ≥0) (hS : S.Nonempty) :
    sInf ((fun s => a + s) '' S) = a + sInf S :=
  ((Monotone.map_csInf_of_continuousAt (f := fun s : ℝ≥0 => a + s)
    (continuous_const.add continuous_id).continuousAt (fun _ _ h => by dsimp only; gcongr)
    hS (OrderBot.bddBelow S))).symm

/-- `if ∃ s ∈ S then sInf S else ⊤` commutes with translation. -/
theorem ifInf_image_add (a : ℝ≥0) (S : Set ℝ≥0) [Decidable (∃ s, s ∈ (fun s => a + s) '' S)]
    [Decidable (∃ s, s ∈ S)] :
    (if ∃ s, s ∈ (fun s => a + s) '' S then ((sInf ((fun s => a + s) '' S) : ℝ≥0) : WithTop ℝ≥0)
      else ⊤) = WithTop.map (fun s => a + s)
      (if ∃ s, s ∈ S then ((sInf S : ℝ≥0) : WithTop ℝ≥0) else ⊤) := by
  by_cases h : ∃ s, s ∈ S
  · have h' : ∃ s, s ∈ (fun s => a + s) '' S := by
      obtain ⟨s, hs⟩ := h; exact ⟨a + s, s, hs, rfl⟩
    rw [if_pos h, if_pos h', sInf_image_add a S h, WithTop.map_coe]
  · have h' : ¬ ∃ s, s ∈ (fun s => a + s) '' S := by
      rintro ⟨_, s, hs, _⟩; exact h ⟨s, hs⟩
    rw [if_neg h, if_neg h', WithTop.map_top]

theorem iro_after (a : ℝ≥0) (y : ℕ) (hy : 1 ≤ y) (hpre : ∀ s : ℝ≥0, s < a → X s ω = y)
    (hpost : ∀ s : ℝ≥0, a ≤ s → X s ω = X' (s - a) ω') (t : ℝ≥0)
    (ht : (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ ≤ t) :
    inverseReciprocalOccupation X t ω = WithTop.map (fun s => a + s)
      (inverseReciprocalOccupation X' (t - (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal ω') := by
  have hc : (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast (by omega : y ≠ 0)))
  have htc : (((t - (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞) =
      (t : ℝ≥0∞) - (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ :=
    ENNReal.coe_toNNReal (ENNReal.sub_ne_top ENNReal.coe_ne_top)
  have hS : {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} = (fun s => a + s) ''
      {s : ℝ≥0 | (((t - (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞) <
        reciprocalOccupation X' s ω'} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hs
      have has : a ≤ s := by
        by_contra hlt
        push_neg at hlt
        rw [recOcc_before X ω a y hpre s hlt.le] at hs
        have : (s : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ ≤ (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ := by
          gcongr
        exact absurd (lt_of_lt_of_le hs (this.trans ht)) (lt_irrefl _)
      refine ⟨s - a, ?_, add_tsub_cancel_of_le has⟩
      rw [recOcc_after X X' ω ω' a y hpre hpost s has] at hs
      rw [htc, ENNReal.sub_lt_iff_lt_right hc ht, add_comm]
      exact hs
    · rintro ⟨s', hs', rfl⟩
      rw [recOcc_after X X' ω ω' a y hpre hpost _ le_self_add, add_tsub_cancel_left]
      rw [htc, ENNReal.sub_lt_iff_lt_right hc ht, add_comm] at hs'
      exact hs'
  unfold inverseReciprocalOccupation
  have key := @ifInf_image_add a {s : ℝ≥0 | (((t - (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal : ℝ≥0) :
    ℝ≥0∞) < reciprocalOccupation X' s ω'} (Classical.propDecidable _) (Classical.propDecidable _)
  rw [← hS] at key
  exact key

theorem fnp_after (a : ℝ≥0) (y : ℕ) (hpre : ∀ s : ℝ≥0, s < a → X s ω = y)
    (hpost : ∀ s : ℝ≥0, a ≤ s → X s ω = X' (s - a) ω') (h0 : 0 ≤ X' 0 ω') :
    firstNegativePassage X ω = WithTop.map (fun s => a + s) (firstNegativePassage X' ω') := by
  have hS : {t : ℝ≥0 | 0 < t ∧ X t ω < 0} =
      (fun s => a + s) '' {t : ℝ≥0 | 0 < t ∧ X' t ω' < 0} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hs0, hs⟩
      have has : a ≤ s := by
        by_contra hlt
        push_neg at hlt
        rw [hpre s hlt] at hs
        exact absurd hs (by simp)
      rw [hpost s has] at hs
      refine ⟨s - a, ⟨?_, hs⟩, add_tsub_cancel_of_le has⟩
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s - a) with h | h
      · rw [← h] at hs; exact absurd h0 (not_le.2 hs)
      · exact h
    · rintro ⟨s', ⟨hs0, hs⟩, rfl⟩
      refine ⟨lt_of_lt_of_le hs0 le_add_self, ?_⟩
      rw [hpost _ le_self_add, add_tsub_cancel_left]; exact hs
  unfold firstNegativePassage
  have key := @ifInf_image_add a {t : ℝ≥0 | 0 < t ∧ X' t ω' < 0}
    (Classical.propDecidable _) (Classical.propDecidable _)
  rw [← hS] at key
  exact key

theorem iro_before (a : ℝ≥0) (y : ℕ) (hy : 1 ≤ y) (hpre : ∀ s : ℝ≥0, s < a → X s ω = y)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) < (a : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹) :
    inverseReciprocalOccupation X t ω = ((t * y : ℝ≥0) : WithTop ℝ≥0) ∧ t * y < a := by
  have hy0 : (y : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have hyt : (y : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top y
  have key : ∀ s : ℝ≥0, (t : ℝ≥0∞) < (s : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ ↔ t * y < s := by
    intro s
    rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl hy0) (Or.inl hyt)]
    rw [show (y : ℝ≥0∞) = ((y : ℝ≥0) : ℝ≥0∞) by simp, ← ENNReal.coe_mul, ENNReal.coe_lt_coe]
  have hta : t * y < a := (key a).1 ht
  refine ⟨?_, hta⟩
  have hS : {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} = Set.Ioi (t * y) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    rcases le_or_gt s a with hs | hs
    · rw [recOcc_before X ω a y hpre s hs]; exact key s
    · constructor
      · intro _; exact lt_trans hta hs
      · intro _
        refine lt_of_lt_of_le ht ?_
        rw [← recOcc_before X ω a y hpre a le_rfl]
        exact lintegral_mono_set (Set.Ioc_subset_Ioc_right (by exact_mod_cast hs.le))
  unfold inverseReciprocalOccupation
  have hne : ∃ s : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X s ω := by
    refine ⟨t * y + 1, ?_⟩
    have : t * y + 1 ∈ {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} := by
      rw [hS]; exact Set.mem_Ioi.2 (lt_add_one (t * (y : ℝ≥0)))
    exact this
  rw [if_pos hne]
  rw [hS, csInf_Ioi]

theorem iro_zero (a : ℝ≥0) (ha : 0 < a) (hpre : ∀ s : ℝ≥0, s < a → X s ω = 0) (t : ℝ≥0) :
    inverseReciprocalOccupation X t ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
  have htop : ∀ s : ℝ≥0, 0 < s → reciprocalOccupation X s ω = ⊤ := by
    intro s hs
    unfold reciprocalOccupation
    refine eq_top_iff.2 ?_
    have hsub : Set.Ioo (0 : ℝ) (min (s : ℝ) a) ⊆ Set.Ioc (0 : ℝ) s :=
      fun u hu => ⟨hu.1, hu.2.le.trans (min_le_left _ _)⟩
    refine le_trans ?_ (lintegral_mono_set hsub)
    rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => (⊤ : ℝ≥0∞)) ?_]
    · rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Ioo, ENNReal.top_mul]
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_zero]
      exact lt_min (by exact_mod_cast hs) (by exact_mod_cast ha)
    · intro u hu
      have hlt : u.toNNReal < a := by
        rw [Real.toNNReal_lt_iff_lt_coe hu.1.le]
        exact lt_of_lt_of_le hu.2 (min_le_right _ _)
      show (ENNReal.ofReal (X u.toNNReal ω : ℝ))⁻¹ = ⊤
      rw [hpre _ hlt]
      simp
  have hS : {s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    constructor
    · intro h
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
      · subst hs
        unfold reciprocalOccupation at h
        simp at h
      · exact hs
    · intro hs; rw [htop s hs]; exact ENNReal.coe_lt_top
  unfold inverseReciprocalOccupation
  have hne : ∃ s : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X s ω := by
    refine ⟨1, ?_⟩
    rw [htop 1 one_pos]; exact ENNReal.coe_lt_top
  rw [if_pos hne]
  rw [hS, csInf_Ioi]

end Shift

theorem jc_shift (T T' : ℕ → ℝ) (a u : ℝ) (hu : 0 ≤ u) (h0 : T 0 = a)
    (hs : ∀ n, T (n + 1) = a + T' n) (hex : ∃ n, u < T' n) :
    jumpCount T (a + u) = jumpCount T' u + 1 := by
  unfold jumpCount
  have hne : ({n | u < T' n} : Set ℕ).Nonempty := hex
  have hm : u < T' (sInf {n | u < T' n}) := Nat.sInf_mem hne
  apply le_antisymm
  · exact Nat.sInf_le (show a + u < T (sInf {n | u < T' n} + 1) by rw [hs]; linarith)
  · have hne2 : ({n | a + u < T n} : Set ℕ).Nonempty := by
      obtain ⟨n, hn⟩ := hex; exact ⟨n + 1, by show a + u < T (n + 1); rw [hs]; linarith⟩
    have hm2 : a + u < T (sInf {n | a + u < T n}) := Nat.sInf_mem hne2
    rcases Nat.eq_zero_or_eq_succ_pred (sInf {n | a + u < T n}) with h | h
    · rw [h, h0] at hm2
      linarith
    · rw [h]
      apply Nat.succ_le_succ
      apply Nat.sInf_le
      show u < T' _
      have := hm2; rw [h, hs] at this; linarith

theorem cpb_of_min {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (t : ℝ≥0) (ω : Ω) (s : ℝ≥0)
    (h : min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) = (s : WithTop ℝ≥0)) :
    compoundPoissonToBranching X t ω = X s ω := by
  unfold compoundPoissonToBranching; rw [h]

theorem cpb_of_min_top {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (t : ℝ≥0) (ω : Ω)
    (h : min (inverseReciprocalOccupation X t ω) (firstNegativePassage X ω) = ⊤) :
    compoundPoissonToBranching X t ω = 0 := by
  unfold compoundPoissonToBranching; rw [h]

theorem map_add_mono (a : ℝ≥0) : Monotone (WithTop.map (fun s : ℝ≥0 => a + s)) := by
  intro p q hpq
  induction q using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    induction p using WithTop.recTopCoe with
    | top => exact absurd hpq (not_le.2 (WithTop.coe_lt_top q))
    | coe p =>
      simp only [WithTop.map_coe, WithTop.coe_le_coe] at hpq ⊢
      exact add_le_add_right hpq a

theorem le_map_add (a : ℝ≥0) (p : WithTop ℝ≥0) : ((a : ℝ≥0) : WithTop ℝ≥0) ≤ WithTop.map (fun s => a + s) p := by
  induction p using WithTop.recTopCoe with
  | top => exact le_top
  | coe p => simp only [WithTop.map_coe, WithTop.coe_le_coe]; exact le_self_add

/-- The time-changed driver event: at `k` at time `t` with fewer than `N` jumps. -/
def evt {Ω : Type*} (y : ℕ) (τ m : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (k : ℕ) (ω : Ω) : Prop :=
  (compoundPoissonToBranching (integerCompoundPoisson y τ m) t ω).toNat = k ∧
    ∃ s : ℝ≥0, min (inverseReciprocalOccupation (integerCompoundPoisson y τ m) t ω)
      (firstNegativePassage (integerCompoundPoisson y τ m) ω) = (s : WithTop ℝ≥0) ∧
      jumpCount (fun i => ProbabilityTheory.arrival τ i ω) (s : ℝ) < N

section ShiftICP
variable {Ω Ω' : Type*} (τ m : ℕ → Ω → ℝ) (τ' m' : ℕ → Ω' → ℝ) (ω : Ω) (ω' : Ω')

theorem arrival_shift (hτ : ∀ i, τ' i ω' = τ (i + 1) ω) (n : ℕ) :
    ProbabilityTheory.arrival τ (n + 1) ω = τ 0 ω + ProbabilityTheory.arrival τ' n ω' := by
  unfold ProbabilityTheory.arrival
  rw [Finset.sum_range_succ']; simp only [hτ]; ring

theorem icp_pre (y : ℕ) (s : ℝ≥0) (hs : s < (τ 0 ω).toNNReal) :
    integerCompoundPoisson y τ m s ω = y := by
  have hs' : (s : ℝ) < τ 0 ω := Real.lt_toNNReal_iff_coe_lt.1 hs
  rw [icp_eq, jc_zero τ ω _ hs']
  simp

theorem icp_post (hτ : ∀ i, τ' i ω' = τ (i + 1) ω) (hm : ∀ i, m' i ω' = m (i + 1) ω)
    (hpos : ∀ i, 0 < τ i ω) (hT : Tendsto (fun n => ProbabilityTheory.arrival τ n ω) atTop atTop)
    (y : ℕ) (hy : 1 ≤ y) (j : ℕ) (hj : m 0 ω = j - 1) (s : ℝ≥0) (hs : (τ 0 ω).toNNReal ≤ s) :
    integerCompoundPoisson y τ m s ω =
      integerCompoundPoisson (y - 1 + j) τ' m' (s - (τ 0 ω).toNNReal) ω' := by
  have h0 := hpos 0
  have ha : (((τ 0 ω).toNNReal : ℝ≥0) : ℝ) = τ 0 ω := Real.coe_toNNReal _ h0.le
  have hsr : (s : ℝ) = τ 0 ω + ((s - (τ 0 ω).toNNReal : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_sub hs, ha]; ring
  have hex : ∃ n, ((s - (τ 0 ω).toNNReal : ℝ≥0) : ℝ) < ProbabilityTheory.arrival τ' n ω' := by
    obtain ⟨n, hn⟩ := (hT.eventually_gt_atTop (s : ℝ)).exists
    refine ⟨n, ?_⟩
    have h1 := arrival_shift τ τ' ω ω' hτ n
    have h2 : ProbabilityTheory.arrival τ n ω ≤ ProbabilityTheory.arrival τ (n + 1) ω := by
      unfold ProbabilityTheory.arrival
      rw [Finset.sum_range_succ _ (n + 1)]
      linarith [hpos (n + 1)]
    linarith
  have hjc := jc_shift (fun n => ProbabilityTheory.arrival τ n ω)
    (fun n => ProbabilityTheory.arrival τ' n ω') (τ 0 ω) _ (NNReal.coe_nonneg _)
    (by simp [ProbabilityTheory.arrival]) (fun n => arrival_shift τ τ' ω ω' hτ n) hex
  rw [icp_eq, icp_eq, hsr, hjc, Finset.sum_range_succ', hj]
  simp only [hm]
  congr 1
  have : ((y - 1 + j : ℕ) : ℝ) = (y : ℝ) - 1 + j := by
    rw [Nat.cast_add, Nat.cast_sub hy]; simp
  rw [this]; ring

theorem jc_post (hτ : ∀ i, τ' i ω' = τ (i + 1) ω) (hpos : ∀ i, 0 < τ i ω)
    (hT : Tendsto (fun n => ProbabilityTheory.arrival τ n ω) atTop atTop) (u : ℝ≥0) :
    jumpCount (fun i => ProbabilityTheory.arrival τ i ω) ((((τ 0 ω).toNNReal + u : ℝ≥0)) : ℝ) =
      jumpCount (fun i => ProbabilityTheory.arrival τ' i ω') (u : ℝ) + 1 := by
  have ha : (((τ 0 ω).toNNReal : ℝ≥0) : ℝ) = τ 0 ω := Real.coe_toNNReal _ (hpos 0).le
  have hex : ∃ n, (u : ℝ) < ProbabilityTheory.arrival τ' n ω' := by
    obtain ⟨n, hn⟩ := (hT.eventually_gt_atTop (τ 0 ω + u)).exists
    refine ⟨n, ?_⟩
    have h1 := arrival_shift τ τ' ω ω' hτ n
    have h2 : ProbabilityTheory.arrival τ n ω ≤ ProbabilityTheory.arrival τ (n + 1) ω := by
      unfold ProbabilityTheory.arrival
      rw [Finset.sum_range_succ _ (n + 1)]
      linarith [hpos (n + 1)]
    linarith
  rw [NNReal.coe_add, ha]
  exact jc_shift (fun n => ProbabilityTheory.arrival τ n ω)
    (fun n => ProbabilityTheory.arrival τ' n ω') (τ 0 ω) _ (NNReal.coe_nonneg _)
    (by simp [ProbabilityTheory.arrival]) (fun n => arrival_shift τ τ' ω ω' hτ n) hex

theorem evt_shift (hτ : ∀ i, τ' i ω' = τ (i + 1) ω) (hm : ∀ i, m' i ω' = m (i + 1) ω)
    (hpos : ∀ i, 0 < τ i ω) (hT : Tendsto (fun n => ProbabilityTheory.arrival τ n ω) atTop atTop)
    (j : ℕ) (hj : m 0 ω = j - 1) (N y : ℕ) (t : ℝ≥0) (k : ℕ) (h : evt y τ m (N + 1) t k ω) :
    (y = k ∧ (t : ℝ≥0∞) < ((τ 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹) ∨
    (1 ≤ y ∧ ((τ 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ ≤ t ∧
      evt (y - 1 + j) τ' m' N
        ((t : ℝ≥0∞) - ((τ 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal k ω') := by
  have ha : 0 < (τ 0 ω).toNNReal := by simpa using hpos 0
  have hpre : ∀ s : ℝ≥0, s < (τ 0 ω).toNNReal → integerCompoundPoisson y τ m s ω = y :=
    fun s hs => icp_pre τ m ω y s hs
  obtain ⟨hk, s, hs, hjc⟩ := h
  rcases Nat.eq_zero_or_pos y with hy0 | hy1
  · subst hy0
    left
    have hiro := iro_zero (integerCompoundPoisson 0 τ m) ω (τ 0 ω).toNNReal ha
      (fun s hs => by rw [hpre s hs]; simp) t
    have hmin : min (inverseReciprocalOccupation (integerCompoundPoisson 0 τ m) t ω)
        (firstNegativePassage (integerCompoundPoisson 0 τ m) ω) = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hiro]
      refine min_eq_left ?_
      induction (firstNegativePassage (integerCompoundPoisson 0 τ m) ω) using WithTop.recTopCoe with
      | top => exact le_top
      | coe p => exact WithTop.coe_le_coe.2 (zero_le : (0 : ℝ≥0) ≤ p)
    rw [cpb_of_min _ _ _ _ hmin, hpre 0 ha] at hk
    refine ⟨by simpa using hk, ?_⟩
    simp only [Nat.cast_zero, ENNReal.inv_zero]
    rw [ENNReal.mul_top (by exact_mod_cast ha.ne')]
    exact ENNReal.coe_lt_top
  have hy : 1 ≤ y := hy1
  have hpost : ∀ s : ℝ≥0, (τ 0 ω).toNNReal ≤ s → integerCompoundPoisson y τ m s ω =
      integerCompoundPoisson (y - 1 + j) τ' m' (s - (τ 0 ω).toNNReal) ω' :=
    fun s hs => icp_post τ m τ' m' ω ω' hτ hm hpos hT y hy j hj s hs
  have h0' : 0 ≤ integerCompoundPoisson (y - 1 + j) τ' m' 0 ω' := by
    rw [cp_zero (y - 1 + j) τ' m' ω' (by rw [hτ]; exact hpos 1)]; positivity
  have hfnp := fnp_after (integerCompoundPoisson y τ m) (integerCompoundPoisson (y - 1 + j) τ' m')
    ω ω' (τ 0 ω).toNNReal y hpre hpost h0'
  by_cases hc : (t : ℝ≥0∞) < ((τ 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹
  · left
    obtain ⟨hiro, hta⟩ := iro_before (integerCompoundPoisson y τ m) ω (τ 0 ω).toNNReal y hy hpre t hc
    have hmin : min (inverseReciprocalOccupation (integerCompoundPoisson y τ m) t ω)
        (firstNegativePassage (integerCompoundPoisson y τ m) ω) = ((t * y : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hiro, hfnp]
      refine min_eq_left (le_trans ?_ (le_map_add _ _))
      exact WithTop.coe_le_coe.2 hta.le
    rw [cpb_of_min _ _ _ _ hmin, hpre _ hta] at hk
    exact ⟨by simpa using hk, hc⟩
  · right
    push_neg at hc
    refine ⟨hy, hc, ?_⟩
    have hiro := iro_after (integerCompoundPoisson y τ m) (integerCompoundPoisson (y - 1 + j) τ' m')
      ω ω' (τ 0 ω).toNNReal y hy hpre hpost t hc
    have hmin : min (inverseReciprocalOccupation (integerCompoundPoisson y τ m) t ω)
        (firstNegativePassage (integerCompoundPoisson y τ m) ω) = WithTop.map
          (fun s => (τ 0 ω).toNNReal + s)
          (min (inverseReciprocalOccupation (integerCompoundPoisson (y - 1 + j) τ' m')
            ((t : ℝ≥0∞) - ((τ 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal ω')
            (firstNegativePassage (integerCompoundPoisson (y - 1 + j) τ' m') ω')) := by
      rw [hiro, hfnp, (map_add_mono _).map_min]
    rw [hmin] at hs
    generalize hM : min (inverseReciprocalOccupation (integerCompoundPoisson (y - 1 + j) τ' m')
            ((t : ℝ≥0∞) - ((τ 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal ω')
            (firstNegativePassage (integerCompoundPoisson (y - 1 + j) τ' m') ω') = M at hs hmin
    induction M using WithTop.recTopCoe with
    | top => rw [WithTop.map_top] at hs; exact absurd hs.symm WithTop.coe_ne_top
    | coe s' =>
      rw [WithTop.map_coe, WithTop.coe_eq_coe] at hs
      subst hs
      rw [cpb_of_min _ _ _ _ hmin, hpost _ le_self_add, add_tsub_cancel_left] at hk
      refine ⟨?_, s', hM, ?_⟩
      · rw [cpb_of_min _ _ _ _ hM]; exact hk
      · rw [jc_post τ τ' ω ω' hτ hpos hT s'] at hjc
        omega

end ShiftICP

section Law
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  (rate : ℝ≥0) (arrival marks : ℕ → Ω → ℝ) (jumpLaw : Measure ℝ)

/-- The driver as one random element of `ℕ ⊕ ℕ → ℝ`. -/
def Zc (ω : Ω) : ℕ ⊕ ℕ → ℝ := fun i => Sum.elim arrival marks i ω

/-- Drop the first interarrival time and the first mark. -/
def shc (z : ℕ ⊕ ℕ → ℝ) : ℕ ⊕ ℕ → ℝ := fun i => z (Sum.map Nat.succ Nat.succ i)

theorem shc_measurable : Measurable shc :=
  measurable_pi_iff.2 fun i => measurable_pi_apply _

theorem Zc_measurable (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    Measurable (Zc arrival marks) := by
  refine measurable_pi_iff.2 fun i => ?_
  cases i with
  | inl n => exact hdriver.measurable_interarrival n
  | inr n => exact hdriver.measurable_mark n

theorem split_indep (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    IndepFun (fun ω => (arrival 0 ω, marks 0 ω)) (fun ω => shc (Zc arrival marks ω)) Q := by
  have hind := (iIndepFun_iff_iIndep (fun _ => (inferInstance : MeasurableSpace ℝ)) _ _).1
    hdriver.indep
  have hmeas : ∀ i, Measurable (Sum.elim arrival marks i) := by
    intro i; cases i with
    | inl n => exact hdriver.measurable_interarrival n
    | inr n => exact hdriver.measurable_mark n
  have hle : ∀ i, MeasurableSpace.comap (Sum.elim arrival marks i)
      (inferInstance : MeasurableSpace ℝ) ≤ ‹MeasurableSpace Ω› := fun i => (hmeas i).comap_le
  let S : Set (ℕ ⊕ ℕ) := {Sum.inl 0, Sum.inr 0}
  have h := indep_iSup_of_disjoint hle hind (S := S) (T := Sᶜ) disjoint_compl_right
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
  · show MeasurableSpace.comap (fun ω => shc (Zc arrival marks ω)) MeasurableSpace.pi ≤ _
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    have hi : Sum.map Nat.succ Nat.succ i ∈ Sᶜ := by
      cases i <;> simp [S]
    exact le_iSup₂ (f := fun i (_ : i ∈ Sᶜ) => MeasurableSpace.comap (Sum.elim arrival marks i)
        (inferInstance : MeasurableSpace ℝ)) _ hi
  · refine Measurable.comap_le ?_
    refine Measurable.prodMk ?_ ?_
    · exact (comap_measurable (Sum.elim arrival marks (Sum.inl 0))).mono
        (le_iSup₂ (f := fun i (_ : i ∈ S) => MeasurableSpace.comap (Sum.elim arrival marks i)
          (inferInstance : MeasurableSpace ℝ)) (Sum.inl 0) (by simp [S])) le_rfl
    · exact (comap_measurable (Sum.elim arrival marks (Sum.inr 0))).mono
        (le_iSup₂ (f := fun i (_ : i ∈ S) => MeasurableSpace.comap (Sum.elim arrival marks i)
          (inferInstance : MeasurableSpace ℝ)) (Sum.inr 0) (by simp [S])) le_rfl

theorem split_law (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    Q.map (fun ω => ((arrival 0 ω, marks 0 ω), shc (Zc arrival marks ω))) =
      ((expMeasure rate).prod jumpLaw).prod (Q.map (Zc arrival marks)) := by
  have hZ := Zc_measurable Q rate arrival marks jumpLaw hdriver
  have hmeas : ∀ i, Measurable (Sum.elim arrival marks i) := by
    intro i; cases i with
    | inl n => exact hdriver.measurable_interarrival n
    | inr n => exact hdriver.measurable_mark n
  rw [(split_indep Q rate arrival marks jumpLaw hdriver).map_prod_eq_prod_map_map
    ((hdriver.measurable_interarrival 0).prodMk (hdriver.measurable_mark 0)).aemeasurable
    (show AEMeasurable (fun ω => shc (Zc arrival marks ω)) Q from
      (shc_measurable.comp hZ).aemeasurable)]
  congr 1
  · have hi : IndepFun (arrival 0) (marks 0) Q :=
      hdriver.indep.indepFun (i := Sum.inl 0) (j := Sum.inr 0) (by simp)
    rw [hi.map_prod_eq_prod_map_map (hdriver.measurable_interarrival 0).aemeasurable
      (hdriver.measurable_mark 0).aemeasurable, (hdriver.law_interarrival 0).map_eq,
      (hdriver.law_mark 0).map_eq]
  · have h1 := (hdriver.indep.precomp (g := Sum.map Nat.succ Nat.succ)
      (Sum.map_injective.2 ⟨Nat.succ_injective, Nat.succ_injective⟩)).map_fun_eq_infinitePi_map
      (fun i => hmeas _)
    have h2 := hdriver.indep.map_fun_eq_infinitePi_map hmeas
    change Q.map (fun ω i => Sum.elim arrival marks (Sum.map Nat.succ Nat.succ i) ω) =
      Q.map (fun ω i => Sum.elim arrival marks i ω)
    rw [h1, h2]
    congr 1
    funext i
    cases i with
    | inl n => simp [(hdriver.law_interarrival _).map_eq]
    | inr n => simp [(hdriver.law_mark _).map_eq]

end Law

section Driver
variable {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (offspring : PMF ℕ)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]

/-- Level sets of the time-changed driver are null measurable. -/
theorem driverNullMeasurable_claim
    (hrate : 0 < rate) (hNoZeroJumps : offspring 1 = 0)
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) < reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (y : ℕ) (t : ℝ≥0) (k : ℕ) :
    NullMeasurableSet {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k} Q := by
  have hY := cpb_measurable (integerCompoundPoisson y arrival marks)
    (icp_measurable y arrival marks hdriver.measurable_interarrival hdriver.measurable_mark)
    (fun ω s => icp_right y arrival marks ω s) t
  exact (((measurable_of_countable Int.toNat).comp hY) (measurableSet_singleton k)).nullMeasurableSet

theorem driverInitial_claim
    (hrate : 0 < rate) (hNoZeroJumps : offspring 1 = 0)
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (y : ℕ) :
    ∀ᵐ ω ∂Q, (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) 0 ω).toNat = y := by
  filter_upwards [tau_pos Q arrival rate hrate (hdriver.law_interarrival 0)] with ω hω
  obtain ⟨δ, hδ, hX⟩ := cp_const y arrival marks ω hω
  rw [cpb_zero _ ω δ hδ hX, cp_zero y arrival marks ω hω]
  simp

/-- Probability that the time-changed driver is at `k` at time `t` having made fewer than `N`
jumps by its clock `min θ_t τ⁻`. -/
noncomputable def drvF (Q : Measure Ω) (arrival marks : ℕ → Ω → ℝ) (N y : ℕ) (t : ℝ≥0) (k : ℕ) :
    ℝ≥0∞ :=
  Q {ω | (compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
    ∃ s : ℝ≥0, min (inverseReciprocalOccupation (integerCompoundPoisson y arrival marks) t ω)
      (firstNegativePassage (integerCompoundPoisson y arrival marks) ω) = (s : WithTop ℝ≥0) ∧
      jumpCount (fun i => ProbabilityTheory.arrival arrival i ω) (s : ℝ) < N}

/-- Canonical coordinates on `ℕ ⊕ ℕ → ℝ`. -/
def A0 (i : ℕ) (z : ℕ ⊕ ℕ → ℝ) : ℝ := z (Sum.inl i)
def M0 (i : ℕ) (z : ℕ ⊕ ℕ → ℝ) : ℝ := z (Sum.inr i)

/-- Offspring number read off a mark `j - 1`. -/
noncomputable def jf (v : ℝ) : ℕ := (⌊v⌋ + 1).toNat

theorem jf_spec (j : ℕ) : jf ((j : ℝ) - 1) = j := by
  unfold jf
  have : ⌊(j : ℝ) - 1⌋ = (j : ℤ) - 1 := by
    rw [show ((j : ℝ) - 1) = ((((j : ℤ) - 1 : ℤ)) : ℝ) by push_cast; ring, Int.floor_intCast]
  rw [this]; simp

theorem jf_measurable : Measurable jf :=
  (measurable_of_countable (fun z : ℤ => (z + 1).toNat)).comp Int.measurable_floor

theorem evtGen_measurable {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℤ) (τ : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i)) (hXm : Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2))
    (hXr : ∀ ω s, ∃ ε > 0, ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε → X s' ω = X s ω) (N k : ℕ) :
    MeasurableSet {p : ℝ≥0 × Ω | (compoundPoissonToBranching X p.1 p.2).toNat = k ∧
      ∃ s : ℝ≥0, min (inverseReciprocalOccupation X p.1 p.2) (firstNegativePassage X p.2) =
        (s : WithTop ℝ≥0) ∧ jumpCount (fun i => ProbabilityTheory.arrival τ i p.2) (s : ℝ) < N} := by
  have hA : Measurable (fun p : ℝ≥0 × Ω =>
      ((inverseReciprocalOccupation X p.1 p.2 : WithTop ℝ≥0) :
        ℝ≥0∞)) := by
    refine measurable_of_Iio fun x => ?_
    have : (fun p : ℝ≥0 × Ω => ((inverseReciprocalOccupation X
        p.1 p.2 : WithTop ℝ≥0) : ℝ≥0∞)) ⁻¹' Iio x =
        ⋃ q : ℚ, ⋃ (_ : 0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < x),
          {p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) < reciprocalOccupation X
            (q : ℝ).toNNReal p.2} := by
      ext p; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]; exact iro_lt_iff _ p.2 p.1 x
    rw [this]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
      measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst)
        ((recOcc_measurable _ hXm _).comp measurable_snd)
  have hB : Measurable (fun ω => ((firstNegativePassage X ω :
      WithTop ℝ≥0) : ℝ≥0∞)) := by
    refine measurable_of_Iio fun x => ?_
    have : (fun ω => ((firstNegativePassage X ω : WithTop ℝ≥0) :
        ℝ≥0∞)) ⁻¹' Iio x =
        ⋃ q : ℚ, ⋃ (_ : 0 ≤ q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < x),
          ⋃ (_ : 0 < (q : ℝ).toNNReal), {ω | X (q : ℝ).toNNReal ω < 0} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq,
        exists_prop]; exact fnp_lt_iff X hXr ω x
    rw [this]
    have hs : ∀ u : ℝ≥0, Measurable (fun ω => X u ω) := fun u =>
      hXm.comp (measurable_const.prodMk measurable_id)
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
      measurableSet_lt (hs _) measurable_const
  have hB' : Measurable (fun p : ℝ≥0 × Ω => ((firstNegativePassage X
      p.2 : WithTop ℝ≥0) : ℝ≥0∞)) := hB.comp measurable_snd
  have hσ : Measurable (fun p : ℝ≥0 × Ω => min ((inverseReciprocalOccupation
      X p.1 p.2 : WithTop ℝ≥0) : ℝ≥0∞)
      ((firstNegativePassage X p.2 : WithTop ℝ≥0) : ℝ≥0∞)) :=
    hA.min hB'
  have hY : Measurable (fun p : ℝ≥0 × Ω =>
      compoundPoissonToBranching X p.1 p.2) := by
    have : (fun p : ℝ≥0 × Ω => compoundPoissonToBranching X p.1 p.2)
        = fun p => (if (min ((inverseReciprocalOccupation X p.1 p.2 :
          WithTop ℝ≥0) : ℝ≥0∞) ((firstNegativePassage X p.2 :
          WithTop ℝ≥0) : ℝ≥0∞)) = ⊤ then 0 else
        X (ENNReal.toNNReal (min ((inverseReciprocalOccupation
          X p.1 p.2 : WithTop ℝ≥0) : ℝ≥0∞)
          ((firstNegativePassage X p.2 : WithTop ℝ≥0) : ℝ≥0∞))) p.2) :=
      funext fun p => cpb_eq_H X p.1 p.2
    rw [this]
    exact Measurable.ite (hσ (measurableSet_singleton ⊤)) measurable_const
      (hXm.comp (hσ.ennreal_toNNReal.prodMk measurable_snd))
  have harr : ∀ i, Measurable (fun ω => ProbabilityTheory.arrival τ i ω) := fun i =>
    Finset.measurable_sum _ fun j _ => hτ j
  have hJ := (jc_measurable (fun i ω => ProbabilityTheory.arrival τ i ω) harr).comp
    (hσ.ennreal_toNNReal.prodMk measurable_snd)
  have e : {p : ℝ≥0 × Ω | (compoundPoissonToBranching X p.1 p.2).toNat = k ∧
      ∃ s : ℝ≥0, min (inverseReciprocalOccupation X p.1 p.2) (firstNegativePassage X p.2) =
        (s : WithTop ℝ≥0) ∧ jumpCount (fun i => ProbabilityTheory.arrival τ i p.2) (s : ℝ) < N} =
      {p | (compoundPoissonToBranching X p.1 p.2).toNat = k} ∩
      ({p | min ((inverseReciprocalOccupation X p.1 p.2 :
          WithTop ℝ≥0) : ℝ≥0∞) ((firstNegativePassage X p.2 :
          WithTop ℝ≥0) : ℝ≥0∞) ≠ ⊤} ∩
       {p | jumpCount (fun i => ProbabilityTheory.arrival τ i p.2)
          ((ENNReal.toNNReal (min ((inverseReciprocalOccupation X p.1 p.2 :
          WithTop ℝ≥0) : ℝ≥0∞) ((firstNegativePassage X p.2 :
          WithTop ℝ≥0) : ℝ≥0∞)) : ℝ≥0) : ℝ) < N}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, s, hs, h2⟩
      have hs' : min ((inverseReciprocalOccupation X p.1 p.2 :
          WithTop ℝ≥0) : ℝ≥0∞) ((firstNegativePassage X p.2 :
          WithTop ℝ≥0) : ℝ≥0∞) = (s : ℝ≥0∞) := hs
      refine ⟨h1, by rw [hs']; exact ENNReal.coe_ne_top, ?_⟩
      convert h2 using 3
      exact (congrArg ENNReal.toNNReal hs').trans (ENNReal.toNNReal_coe s)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, _, ?_, h3⟩
      exact (ENNReal.coe_toNNReal h2).symm
  rw [e]
  exact (((measurable_of_countable Int.toNat).comp hY) (measurableSet_singleton k)).inter
    ((hσ (measurableSet_singleton ⊤)).compl.inter (hJ measurableSet_Iio))

theorem evtJoint_measurable {Ω : Type*} [MeasurableSpace Ω] (y : ℕ) (τ m : ℕ → Ω → ℝ)
    (hτ : ∀ i, Measurable (τ i)) (hm : ∀ i, Measurable (m i)) (N k : ℕ) :
    MeasurableSet {p : ℝ≥0 × Ω | evt y τ m N p.1 k p.2} :=
  evtGen_measurable (integerCompoundPoisson y τ m) τ hτ (icp_measurable y τ m hτ hm)
    (fun ω s => icp_right y τ m ω s) N k

theorem jl_sum (offspring : PMF ℕ) (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) (f : ℕ → ℝ≥0∞) :
    ∫⁻ v, f (jf v) ∂jumpLaw = ∑' j, offspring j * f j := by
  have hSe : {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = Set.range (fun j : ℕ => (j : ℝ) - 1) := by
    ext x; simp [eq_comm]
  have hSc : (Set.range (fun j : ℕ => (j : ℝ) - 1)).Countable := Set.countable_range _
  have hae : ∀ᵐ x ∂jumpLaw, x ∈ Set.range (fun j : ℕ => (j : ℝ) - 1) := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff hSc.measurableSet).2 (hSe ▸ hSupport)
    exact this
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_countable _ hSc,
    tsum_range (fun x => f (jf x) * jumpLaw {x})
      (fun a b h => by simpa using h)]
  refine tsum_congr fun j => ?_
  rw [jf_spec, hJumpMass, mul_comm]

theorem lintegral_mul_subst (c : ℝ) (hc : 0 < c) (φ : ℝ → ℝ≥0∞) :
    ∫⁻ u, φ u = ENNReal.ofReal c * ∫⁻ s, φ (c * s) := by
  have h1 := lintegral_map_equiv φ (MeasurableEquiv.mulLeft₀ c hc.ne') (μ := volume)
  have h2 : Measure.map (MeasurableEquiv.mulLeft₀ c hc.ne') volume =
      ENNReal.ofReal |c⁻¹| • volume := Real.map_volume_mul_left hc.ne'
  rw [h2, lintegral_smul_measure, smul_eq_mul] at h1
  have h3 : ∀ a, (MeasurableEquiv.mulLeft₀ c hc.ne') a = c * a := fun a => rfl
  simp only [h3] at h1
  rw [← h1, ← mul_assoc, ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.2 hc),
    mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]

theorem exp_tail (r : ℝ≥0) (hr : 0 < r) (x : ℝ) (hx : 0 ≤ x) :
    expMeasure (r : ℝ) (Set.Ioi x) = ENNReal.ofReal (Real.exp (-((r : ℝ) * x))) := by
  haveI := isProbabilityMeasure_expMeasure (r := (r : ℝ)) (by exact_mod_cast hr)
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq (by exact_mod_cast hr), if_pos hx]
  have h1 : Real.exp (-((r : ℝ) * x)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ (r : ℝ) * x := mul_nonneg (NNReal.coe_nonneg r) hx
    linarith)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

theorem conv_le (y : ℕ) (hy : 1 ≤ y) (u : ℝ) (t : ℝ≥0) :
    (u.toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ ≤ t ↔ u ≤ y * t := by
  have hy0 : (y : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  rw [← div_eq_mul_inv, ENNReal.div_le_iff hy0 (ENNReal.natCast_ne_top y)]
  rw [show (t : ℝ≥0∞) * y = ((t * y : ℝ≥0) : ℝ≥0∞) by push_cast; ring, ENNReal.coe_le_coe,
    Real.toNNReal_le_iff_le_coe]
  push_cast
  rw [mul_comm]

theorem conv_sub (y : ℕ) (hy : 1 ≤ y) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0) :
    ((t : ℝ≥0∞) - (u.toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹).toNNReal = ((t : ℝ) - u / y).toNNReal := by
  have hy0 : (y : ℝ≥0) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have e : (u.toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹ = ((u.toNNReal / (y : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_div hy0, div_eq_mul_inv]; simp
  rw [e, ← ENNReal.coe_sub, ENNReal.toNNReal_coe]
  apply NNReal.eq
  rw [NNReal.coe_sub_def, Real.coe_toNNReal', NNReal.coe_div, Real.coe_toNNReal _ hu]
  simp

theorem drvF_step' {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (offspring : PMF ℕ) (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hrate : 0 < rate) (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (N y : ℕ) (t : ℝ≥0) (k : ℕ) :
    drvF Q arrival marks (N + 1) y t k ≤
      firstJumpOp rate offspring (drvF Q arrival marks N) y t k := by
  have hZ := Zc_measurable Q rate arrival marks jumpLaw hdriver
  have hA0 : ∀ i, Measurable (A0 i) := fun i => measurable_pi_apply _
  have hM0 : ∀ i, Measurable (M0 i) := fun i => measurable_pi_apply _
  have hcan : ∀ N y t k, drvF Q arrival marks N y t k =
      (Q.map (Zc arrival marks)) {z | evt y A0 M0 N t k z} := by
    intro N y t k
    have hS : MeasurableSet {z | evt y A0 M0 N t k z} :=
      measurable_prodMk_left (evtJoint_measurable y A0 M0 hA0 hM0 N k)
    rw [Measure.map_apply hZ hS]; rfl
  have hSe : {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = Set.range (fun j : ℕ => (j : ℝ) - 1) := by
    ext x; simp [eq_comm]
  have hSm : MeasurableSet (Set.range (fun j : ℕ => (j : ℝ) - 1)) :=
    (Set.countable_range _).measurableSet
  have hgood : ∀ᵐ ω ∂Q, (∀ i, 0 < arrival i ω) ∧
      Tendsto (fun n => ProbabilityTheory.arrival arrival n ω) atTop atTop ∧
      marks 0 ω ∈ Set.range (fun j : ℕ => (j : ℝ) - 1) := by
    have h1 : ∀ᵐ ω ∂Q, ∀ i, 0 < arrival i ω := ae_all_iff.2 fun i => by
      have := tau_pos Q (fun n => arrival (n + i)) rate hrate
        (by simpa using hdriver.law_interarrival i)
      simpa using this
    have h2 := hdriver.ae_tendsto_arrival hrate
    have h3 : ∀ᵐ ω ∂Q, marks 0 ω ∈ Set.range (fun j : ℕ => (j : ℝ) - 1) := by
      rw [ae_iff]
      have : (Q.map (marks 0)) (Set.range (fun j : ℕ => (j : ℝ) - 1))ᶜ = 0 := by
        rw [(hdriver.law_mark 0).map_eq, prob_compl_eq_zero_iff hSm, ← hSe, hSupport]
      rw [Measure.map_apply (hdriver.measurable_mark 0) hSm.compl] at this
      exact this
    filter_upwards [h1, h2, h3] with ω a b c
    exact ⟨a, b, c⟩
  let E1 : Set Ω := {ω | y = k ∧ (t : ℝ≥0∞) < ((arrival 0 ω).toNNReal : ℝ≥0∞) * (y : ℝ≥0∞)⁻¹}
  let D : Set ((ℝ × ℝ) × (ℕ ⊕ ℕ → ℝ)) := {p | 1 ≤ y ∧ 0 ≤ p.1.1 ∧ p.1.1 ≤ y * t ∧
    evt (y - 1 + jf p.1.2) A0 M0 N ((t : ℝ) - p.1.1 / y).toNNReal k p.2}
  let F : Ω → (ℝ × ℝ) × (ℕ ⊕ ℕ → ℝ) := fun ω => ((arrival 0 ω, marks 0 ω),
    shc (Zc arrival marks ω))
  have hF : Measurable F := ((hdriver.measurable_interarrival 0).prodMk
    (hdriver.measurable_mark 0)).prodMk (shc_measurable.comp hZ)
  have hD : MeasurableSet D := by
    have hD' : D = ⋃ n : ℕ, ({p : (ℝ × ℝ) × (ℕ ⊕ ℕ → ℝ) | 1 ≤ y ∧ 0 ≤ p.1.1 ∧ p.1.1 ≤ y * t} ∩
        {p | jf p.1.2 = n} ∩ ((fun p : (ℝ × ℝ) × (ℕ ⊕ ℕ → ℝ) =>
          (((t : ℝ) - p.1.1 / y).toNNReal, p.2)) ⁻¹'
          {q : ℝ≥0 × (ℕ ⊕ ℕ → ℝ) | evt (y - 1 + n) A0 M0 N q.1 k q.2})) := by
      ext p
      simp only [D, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨jf p.1.2, ⟨⟨h1, h2, h3⟩, rfl⟩, h4⟩
      · rintro ⟨n, ⟨⟨h1, h2, h3⟩, h5⟩, h4⟩; subst h5; exact ⟨h1, h2, h3, h4⟩
    rw [hD']
    refine MeasurableSet.iUnion fun n => ?_
    refine ((MeasurableSet.const _).inter ((measurableSet_le measurable_const
      (measurable_fst.comp measurable_fst)).inter (measurableSet_le
      (measurable_fst.comp measurable_fst) measurable_const))).inter ?_ |>.inter ?_
    · exact (jf_measurable.comp (measurable_snd.comp measurable_fst)) (measurableSet_singleton n)
    · refine (evtJoint_measurable (y - 1 + n) A0 M0 hA0 hM0 N k).preimage ?_
      refine Measurable.prodMk ?_ measurable_snd
      exact measurable_real_toNNReal.comp (measurable_const.sub
        ((measurable_fst.comp measurable_fst).div_const _))
  have hsub : {ω | evt y arrival marks (N + 1) t k ω} ≤ᵐ[Q] (E1 ∪ F ⁻¹' D : Set Ω) := by
    filter_upwards [hgood] with ω hg hmem
    obtain ⟨hpos, hT, j, hj⟩ := hg
    have := evt_shift arrival marks A0 M0 ω (shc (Zc arrival marks ω)) (fun i => rfl)
      (fun i => rfl) hpos hT j hj.symm N y t k hmem
    rcases this with h | ⟨hy, hc, he⟩
    · exact Or.inl h
    · right
      have hu : 0 ≤ arrival 0 ω := (hpos 0).le
      refine ⟨hy, hu, (conv_le y hy _ t).1 hc, ?_⟩
      have hjf : jf (marks 0 ω) = j := by rw [← hj]; exact jf_spec j
      show evt (y - 1 + jf (marks 0 ω)) A0 M0 N ((t : ℝ) - arrival 0 ω / y).toNNReal k
        (shc (Zc arrival marks ω))
      rw [hjf, ← conv_sub y hy _ hu t]; exact he
  have hE1 : Q E1 ≤ if y = k then ENNReal.ofReal (Real.exp (-((rate : ℝ) * y * t))) else 0 := by
    split_ifs with hyk
    · calc Q E1 ≤ Q {ω | (y : ℝ) * t < arrival 0 ω} := by
            refine measure_mono fun ω hω => ?_
            obtain ⟨_, hω⟩ := hω
            show (y : ℝ) * t < arrival 0 ω
            rcases Nat.eq_zero_or_pos y with h0 | h1
            · subst h0
              simp only [CharP.cast_eq_zero, zero_mul]
              by_contra hle
              push_neg at hle
              rw [Real.toNNReal_of_nonpos hle] at hω
              simp at hω
            · exact lt_of_not_ge fun hle => (not_lt.2 ((conv_le y h1 _ t).2 hle)) hω
        _ = expMeasure (rate : ℝ) (Set.Ioi ((y : ℝ) * t)) := by
            rw [← (hdriver.law_interarrival 0).map_eq,
              Measure.map_apply (hdriver.measurable_interarrival 0) measurableSet_Ioi]; rfl
        _ = _ := by
            rw [exp_tail rate hrate _ (by positivity)]; congr 2; ring
    · have : E1 = ∅ := by ext ω; simp [E1, hyk]
      rw [this, measure_empty]
  have hE2 : Q (F ⁻¹' D) ≤ ∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal ((rate : ℝ) * y * Real.exp (-((rate : ℝ) * y * s))) *
      ∑' j : ℕ, offspring j * drvF Q arrival marks N (y - 1 + j) (Real.toNNReal (t - s)) k := by
    rw [← Measure.map_apply hF hD, split_law Q rate arrival marks jumpLaw hdriver,
      Measure.prod_apply hD, lintegral_prod _ (measurable_measure_prodMk_left hD).aemeasurable]
    by_cases hy : 1 ≤ y
    swap
    · have h0 : ∀ x : ℝ × ℝ, (Q.map (Zc arrival marks)) (Prod.mk x ⁻¹' D) = 0 := fun x => by
        have : Prod.mk x ⁻¹' D = ∅ := by ext z; simp [D, hy]
        rw [this, measure_empty]
      simp [h0]
    have hyr : (0 : ℝ) < y := by exact_mod_cast hy
    let I : Set ℝ := Set.Icc 0 ((y : ℝ) * t)
    have hslice : ∀ u v, (Q.map (Zc arrival marks)) (Prod.mk (u, v) ⁻¹' D) =
        if u ∈ I then drvF Q arrival marks N (y - 1 + jf v) ((t : ℝ) - u / y).toNNReal k
        else 0 := by
      intro u v
      split_ifs with hu
      · rw [hcan]; congr 1; ext z
        simp only [D, Set.mem_preimage, Set.mem_setOf_eq]
        exact ⟨fun h => h.2.2.2, fun h => ⟨hy, hu.1, hu.2, h⟩⟩
      · have : Prod.mk (u, v) ⁻¹' D = ∅ := by
          ext z
          simp only [D, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hu ⟨h.2.1, h.2.2.1⟩
        rw [this, measure_empty]
    have hinner : ∀ u, ∫⁻ v, (Q.map (Zc arrival marks)) (Prod.mk (u, v) ⁻¹' D) ∂jumpLaw =
        if u ∈ I then ∑' j, offspring j * drvF Q arrival marks N (y - 1 + j)
          ((t : ℝ) - u / y).toNNReal k else 0 := by
      intro u
      simp_rw [hslice u]
      split_ifs
      · exact jl_sum offspring jumpLaw hSupport hJumpMass
          (fun j => drvF Q arrival marks N (y - 1 + j) ((t : ℝ) - u / y).toNNReal k)
      · simp
    simp_rw [hinner]
    let K : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal ((rate : ℝ) * Real.exp (-((rate : ℝ) * u))) *
      ∑' j, offspring j * drvF Q arrival marks N (y - 1 + j) ((t : ℝ) - u / y).toNNReal k
    calc ∫⁻ u, (if u ∈ I then ∑' j, offspring j * drvF Q arrival marks N (y - 1 + j)
          ((t : ℝ) - u / y).toNNReal k else 0) ∂(expMeasure (rate : ℝ))
        ≤ ∫⁻ u, (gammaPDF 1 rate * fun u => (if u ∈ I then ∑' j, offspring j *
          drvF Q arrival marks N (y - 1 + j) ((t : ℝ) - u / y).toNNReal k else 0)) u :=
          lintegral_withDensity_le_lintegral_mul volume
            (by unfold gammaPDF; exact (measurable_gammaPDFReal 1 rate).ennreal_ofReal) _
      _ = ∫⁻ u, I.indicator K u := by
          refine lintegral_congr fun u => ?_
          simp only [Pi.mul_apply]
          by_cases hu : u ∈ I
          · rw [if_pos hu, Set.indicator_of_mem hu]
            show exponentialPDF rate u * _ = _
            rw [exponentialPDF_of_nonneg hu.1]
          · rw [if_neg hu, Set.indicator_of_notMem hu, mul_zero]
      _ = ENNReal.ofReal y * ∫⁻ s, I.indicator K (y * s) := lintegral_mul_subst y hyr _
      _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_indicator measurableSet_Icc]
          refine lintegral_congr fun s => ?_
          by_cases hs : s ∈ Set.Icc (0 : ℝ) t
          · have hys : (y : ℝ) * s ∈ I := ⟨mul_nonneg hyr.le hs.1,
              mul_le_mul_of_nonneg_left hs.2 hyr.le⟩
            rw [Set.indicator_of_mem hys, Set.indicator_of_mem hs]
            simp only [K]
            rw [mul_div_cancel_left₀ _ hyr.ne', ← mul_assoc, ← ENNReal.ofReal_mul hyr.le]
            have e : (y : ℝ) * ((rate : ℝ) * Real.exp (-((rate : ℝ) * (y * s)))) =
                (rate : ℝ) * y * Real.exp (-((rate : ℝ) * y * s)) := by
              rw [← mul_assoc (rate : ℝ) (y : ℝ) s]; ring
            rw [e]
          · have hys : (y : ℝ) * s ∉ I := by
              intro h; apply hs
              exact ⟨nonneg_of_mul_nonneg_right h.1 hyr |> fun h' => by
                  nlinarith [h.1], le_of_mul_le_mul_left h.2 hyr⟩
            rw [Set.indicator_of_notMem hys, Set.indicator_of_notMem hs, mul_zero]
  unfold firstJumpOp
  calc drvF Q arrival marks (N + 1) y t k = Q {ω | evt y arrival marks (N + 1) t k ω} := rfl
    _ ≤ Q (E1 ∪ F ⁻¹' D) := measure_mono_ae hsub
    _ ≤ Q E1 + Q (F ⁻¹' D) := measure_union_le _ _
    _ ≤ _ := add_le_add hE1 hE2

/-- First-jump recursion for the driver's `N`-jump probabilities. -/
theorem drvF_step
    (hrate : 0 < rate) (hNoZeroJumps : offspring 1 = 0)
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ, jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (N y : ℕ) (t : ℝ≥0) (k : ℕ) :
    drvF Q arrival marks (N + 1) y t k ≤
      firstJumpOp rate offspring (drvF Q arrival marks N) y t k :=
  drvF_step' Q rate offspring arrival marks jumpLaw hrate hdriver hSupport hJumpMass N y t k

/-- Non-explosion: the `N`-jump probabilities exhaust the level set. -/
theorem drvF_exhaust
    (hrate : 0 < rate)
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) < reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (y : ℕ) (t : ℝ≥0) (k : ℕ) :
    Q {ω | (compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω).toNat = k}
      ≤ ⨆ N, drvF Q arrival marks N y t k := by
  unfold drvF
  rw [← Monotone.measure_iUnion]
  · refine measure_mono_ae ?_
    filter_upwards [hNoExplosion y, hdriver.ae_tendsto_arrival hrate] with ω hω hT hk
    obtain ⟨s0, hs0⟩ := hω t
    have hθ : inverseReciprocalOccupation (integerCompoundPoisson y arrival marks) t ω ≠ ⊤ := by
      unfold inverseReciprocalOccupation
      rw [if_pos ⟨s0, hs0⟩]
      exact WithTop.coe_ne_top
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1
      (ne_top_of_le_ne_top hθ (min_le_left _ (firstNegativePassage
        (integerCompoundPoisson y arrival marks) ω)))
    obtain ⟨n, hn⟩ := (hT.eventually_gt_atTop (s : ℝ)).exists
    refine Set.mem_iUnion.2 ⟨n + 1, hk, s, hs.symm, ?_⟩
    exact Nat.lt_succ_of_le (Nat.sInf_le hn)
  · intro N M hNM ω hω
    obtain ⟨h1, s, h2, h3⟩ := hω
    exact ⟨h1, s, h2, lt_of_lt_of_le h3 hNM⟩

theorem drvF_zero (y : ℕ) (t : ℝ≥0) (k : ℕ) : drvF Q arrival marks 0 y t k = 0 := by
  unfold drvF
  simp

end Driver

/-- The driver's level-set masses form a PMF. -/
theorem driverPMF_exists
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (V : ℕ → ℝ≥0 → Ω → ℤ) (hV : ∀ y t k, NullMeasurableSet {ω | (V y t ω).toNat = k} Q) :
    ∃ L : PopulationLaws, ∀ y t k, L y t k = Q {ω | (V y t ω).toNat = k} := by
  have key : ∀ y t, HasSum (fun k : ℕ => Q {ω | (V y t ω).toNat = k}) 1 := by
    intro y t
    have h := measure_iUnion₀ (μ := Q) (f := fun k : ℕ => {ω | (V y t ω).toNat = k})
      (fun i j hij => ?_) (fun k => hV y t k)
    · have hU : (⋃ k : ℕ, {ω | (V y t ω).toNat = k}) = Set.univ := by
        ext ω; simp
      rw [hU, measure_univ] at h
      rw [h]; exact ENNReal.summable.hasSum
    · exact (Set.disjoint_left.2 fun ω h1 h2 => hij (h1.symm.trans h2)).aedisjoint
  exact ⟨fun y t => ⟨fun k => Q {ω | (V y t ω).toNat = k}, key y t⟩, fun _ _ _ => rfl⟩


theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω) :
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  obtain ⟨L, hL⟩ := driverPMF_exists Q
    (fun y t ω => compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω)
    (fun y t k => driverNullMeasurable_claim Q rate offspring arrival marks jumpLaw hrate
      hNoZeroJumps hdriver hSupport hJumpMass hNoExplosion y t k)
  have hF : ∀ N y t k, drvF Q arrival marks N y t k ≤ law y t k := by
    intro N
    induction N with
    | zero => intro y t k; rw [drvF_zero]; exact bot_le
    | succ N ih =>
      intro y t k
      calc drvF Q arrival marks (N + 1) y t k
          ≤ firstJumpOp rate offspring (drvF Q arrival marks N) y t k :=
            drvF_step Q rate offspring arrival marks jumpLaw hrate hNoZeroJumps hdriver
              hSupport hJumpMass N y t k
        _ ≤ firstJumpOp rate offspring (fun y t k => law y t k) y t k :=
            firstJumpOp_mono rate offspring ih y t k
        _ ≤ law y t k :=
            law_firstJump rate offspring hNoZeroJumps law hMarkov hInitial hRates y t k
  have hle : ∀ y t k, L y t k ≤ law y t k := by
    intro y t k
    rw [hL]
    exact (drvF_exhaust Q rate arrival marks jumpLaw hrate hdriver hNoExplosion y t k).trans
      (iSup_le fun N => hF N y t k)
  intro y t k
  rw [← hL]
  exact (eq_of_le_of_tsum_eq (hle y t) (PMF.tsum_coe _) (PMF.tsum_coe _) k).symm
