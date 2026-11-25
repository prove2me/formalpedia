-- Prove2me | solution 1 for ManyServerQED.Scheduling.abandonment_noise_vanishes_uoc
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:25:41.698352+00:00
-- url     : https://prove2.me/submissions/91856b36-b66a-4953-af4b-30fcc4dbb86e

import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_DurrettProbability_kolmogorov_maximal_inequality
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_queue_time_changes_uoc

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem poisson_inc_moments {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : IsPoissonProcess P N a) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    let g : Ω → ℝ := fun ω => N ω t - N ω s - a * (t - s)
    MemLp g 2 P ∧ (∫ ω, g ω ∂P) = 0 ∧ variance g P = a * (t - s) := by
  let d : Ω → ℝ := fun ω => N ω t - N ω s
  let F : Ω → ℕ := fun ω => ⌊d ω⌋₊
  let r : ℝ≥0 := (a * (t - s)).toNNReal
  have hr : (r : ℝ) = a * (t - s) := Real.coe_toNNReal _ (mul_nonneg hN.rate_nonneg (sub_nonneg.mpr hst))
  have hd : Measurable d := (hN.meas t).sub (hN.meas s)
  have hF : Measurable F := hd.nat_floor
  have hcast (ω : Ω) : (F ω : ℝ) = d ω := by
    obtain ⟨m, hm⟩ := hN.nat_valued ω s hs
    obtain ⟨n, hn⟩ := hN.nat_valued ω t (hs.trans hst)
    have hmn : m ≤ n := by
      have h := hN.mono ω hs (hs.trans hst) hst
      rw [hm, hn] at h
      exact_mod_cast h
    have heq : d ω = (n - m : ℕ) := by
      dsimp [d]
      rw [hn, hm, Nat.cast_sub hmn]
    simp [F, heq]
  have hmap : Measure.map F P = poissonMeasure r := by
    apply Measure.ext_of_singleton
    intro j
    rw [Measure.map_apply hF (measurableSet_singleton j)]
    convert hN.law s t hs hst j using 2
    ext ω
    change F ω = j ↔ d ω = (j : ℝ)
    rw [← hcast]
    exact Nat.cast_inj.symm
  let b : ℕ → ℝ := fun j => (j : ℝ) - r
  have hb : Measurable b := Measurable.of_discrete
  have hbsq : Integrable (fun j => b j ^ 2) (poissonMeasure r) := by
    apply integrable_poissonMeasure_iff.mpr
    have h := (AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum r).summable
    simpa only [poissonMeasure_real_singleton, b, Real.norm_eq_abs, abs_pow, sq_abs,
      mul_comm] using h
  have hblp : MemLp b 2 (poissonMeasure r) := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).2 hbsq
  have hbmean : ∫ j, b j ∂(poissonMeasure r) = 0 := by
    have hint : Integrable (fun j : ℕ => (j : ℝ)) (poissonMeasure r) := by
      rw [show (fun j : ℕ => (j : ℝ)) = b + (fun _ : ℕ => (r : ℝ)) from by
        funext j; change (j : ℝ) = (j : ℝ) - r + r; ring]
      exact (hblp.integrable (by norm_num)).add (integrable_const (r : ℝ))
    change (∫ j : ℕ, ((j : ℝ) - r) ∂(poissonMeasure r)) = 0
    rw [integral_sub hint (integrable_const _), AvramDividend.Classical.poisson_count_expected_rate_ws01b]
    simp
  have hbst : ∫ j, b j ^ 2 ∂(poissonMeasure r) = (r : ℝ) := by
    rw [integral_poissonMeasure]
    have h := (AvramDividend.Classical.avram_wave4_p1_poisson_centered_count_variance_hasSum r).tsum_eq
    simpa only [poissonMeasure_real_singleton, b, smul_eq_mul, mul_comm] using h
  have hcomp : (fun ω => N ω t - N ω s - a * (t - s)) = b ∘ F := by
    funext ω
    simp only [Function.comp_apply, b, hr, hcast, d]
  dsimp only
  rw [hcomp]
  have hmeas : Measurable (b ∘ F) := hb.comp hF
  have hmu : (∫ ω, (b ∘ F) ω ∂P) = 0 := by
    change (∫ ω, b (F ω) ∂P) = 0
    rw [← integral_map hF.aemeasurable hb.aestronglyMeasurable, hmap, hbmean]
  refine ⟨?_, hmu, ?_⟩
  · rw [← memLp_map_measure_iff hb.aestronglyMeasurable hF.aemeasurable, hmap]
    exact hblp
  · rw [variance_eq_integral hmeas.aemeasurable, hmu]
    simp only [sub_zero]
    change (∫ ω, b (F ω) ^ 2 ∂P) = _
    calc
      _ = ∫ j, b j ^ 2 ∂(Measure.map F P) :=
        (integral_map (μ := P) (φ := F) (f := fun j => b j ^ 2) hF.aemeasurable
          (hb.pow_const 2).aestronglyMeasurable).symm
      _ = _ := by rw [hmap, hbst, hr]

private theorem poisson_grid_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : IsPoissonProcess P N a) (m : ℕ) (b : ℝ) (hb : 0 < b) :
    P {ω | ∃ j : ℕ, j ≤ m ∧ b ≤ |N ω (j : ℝ) - a * (j : ℝ)|} ≤
      ENNReal.ofReal (a * m / b ^ 2) := by
  let X : ℕ → Ω → ℝ := fun j ω => N ω ((j + 1 : ℕ) : ℝ) - N ω (j : ℝ) - a
  have hmeas (j : ℕ) : Measurable (X j) := ((hN.meas _).sub (hN.meas _)).sub_const _
  have hXi (j : ℕ) : MemLp (X j) 2 P ∧ (∫ ω, X j ω ∂P) = 0 := by
    have hm := poisson_inc_moments hN (j : ℝ) ((j + 1 : ℕ) : ℝ) (by positivity) (by norm_cast; omega)
    dsimp only at hm
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one] at hm
    simpa only [X, Nat.cast_add, Nat.cast_one] using And.intro hm.1 hm.2.1
  have hind : iIndepFun X P := by
    rw [iIndepFun_iff_finset]
    intro q
    let g : q → Fin (q.sup id + 1) := fun j => ⟨j.1, Nat.lt_succ_of_le (Finset.le_sup (f := id) j.2)⟩
    have hg : Function.Injective g := fun _ _ h => Subtype.ext (congrArg Fin.val h)
    let time : Fin (q.sup id + 2) → ℝ := fun j => (j.val : ℝ)
    have ht : Monotone time := fun _ _ h => Nat.cast_le.mpr h
    have hh := hN.indep_incr (q.sup id + 1) time (by positivity) ht
    have hn := (hh.precomp hg).comp (fun (_ : q) (w : ℝ) => w - a)
      (fun _ => measurable_id.sub_const a)
    exact hn
  have hsum (j : ℕ) (ω : Ω) :
      DurrettProbability.partialSum X j ω = N ω (j : ℝ) - a * (j : ℝ) := by
    induction j with
    | zero => simp [DurrettProbability.partialSum, hN.zero ω]
    | succ j h =>
      rw [show DurrettProbability.partialSum X (j + 1) ω =
          DurrettProbability.partialSum X j ω + X j ω by
        exact Finset.sum_range_succ _ _]
      rw [h]
      dsimp [X]
      push_cast
      ring
  have hvar : variance (DurrettProbability.partialSum X m) P = a * (m : ℝ) := by
    have hm := (poisson_inc_moments hN 0 (m : ℝ) le_rfl (by positivity)).2.2
    simp only [hN.zero, sub_zero] at hm
    convert hm using 2
    funext ω
    exact hsum m ω
  have hk := DurrettProbability.kolmogorov_maximal_inequality X hmeas hind
    (fun j => (hXi j).1) (fun j => (hXi j).2) m b hb
  rw [hvar] at hk
  have heq : {ω | ∃ j : ℕ, j ≤ m ∧ b ≤ |N ω (j : ℝ) - a * (j : ℝ)|} =
      {ω | ∃ j ∈ Finset.Icc 1 m, b ≤ |DurrettProbability.partialSum X j ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.mem_Icc, hsum]
    constructor
    · rintro ⟨j, hj, hjb⟩
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp [hN.zero] at hjb
        linarith
      exact ⟨j, ⟨Nat.one_le_iff_ne_zero.mpr hj0, hj⟩, hjb⟩
    · rintro ⟨j, hj, hjb⟩
      exact ⟨j, hj.2, hjb⟩
  rw [heq, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hk

private theorem poisson_small_clock_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : IsPoissonProcess P N a) (n : ℕ) (hn : 1 ≤ n)
    (A T R : ℝ) (ha : a ≤ A) (hT : 0 ≤ T) (hR : 0 < R) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, R + A / Real.sqrt n <
      |(N ω (n * t) - n * a * t) / Real.sqrt n|} ≤ ENNReal.ofReal (A * (T + 1 / (n : ℝ)) / R ^ 2) := by
  let m : ℕ := ⌊(n : ℝ) * T⌋₊ + 1
  let b : ℝ := R * Real.sqrt n
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  have hb : 0 < b := mul_pos hR hs
  calc
    _ ≤ P {ω | ∃ j : ℕ, j ≤ m ∧ b ≤ |N ω (j : ℝ) - a * (j : ℝ)|} := by
      apply measure_mono
      intro ω hω
      obtain ⟨t, ht, htbad⟩ := hω
      by_contra hg
      have gh (j : ℕ) (hj : j ≤ m) : |N ω (j : ℝ) - a * (j : ℝ)| ≤ b :=
        (lt_of_not_ge fun h => hg ⟨j, hj, h⟩).le
      let j : ℕ := ⌊(n : ℝ) * t⌋₊
      have h₀ : (j : ℝ) ≤ (n : ℝ) * t := Nat.floor_le (mul_nonneg hn₀.le ht.1)
      have h₁ : (n : ℝ) * t ≤ ((j + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one ((n : ℝ) * t)).le
      have hj : j + 1 ≤ m := Nat.succ_le_succ (Nat.floor_mono
        (mul_le_mul_of_nonneg_left ht.2 hn₀.le))
      have hl := (abs_le.mp (gh j (Nat.le_of_succ_le hj))).1
      have hu := (abs_le.mp (gh (j + 1) hj)).2
      have hmono₀ := hN.mono ω (show 0 ≤ (j : ℝ) by positivity)
        (mul_nonneg hn₀.le ht.1) h₀
      have hmono₁ := hN.mono ω (mul_nonneg hn₀.le ht.1)
        (show 0 ≤ ((j + 1 : ℕ) : ℝ) by positivity) h₁
      have hl' : - (b + a) ≤ N ω (n * t) - a * (n * t) := by
        have h := mul_le_mul_of_nonneg_left h₁ hN.rate_nonneg
        push_cast at h
        linarith
      have hu' : N ω (n * t) - a * (n * t) ≤ b + a := by
        have h := mul_le_mul_of_nonneg_left h₀ hN.rate_nonneg
        push_cast at hmono₁ hu
        linarith
      apply (not_le_of_gt htbad)
      rw [abs_div, abs_of_pos hs, mul_comm (n : ℝ) a, mul_assoc]
      apply (div_le_iff₀ hs).2
      refine (abs_le.mpr ⟨hl', hu'⟩).trans ?_
      dsimp [b]
      rw [add_mul, div_mul_cancel₀ _ hs.ne']
      linarith
    _ ≤ ENNReal.ofReal (a * m / b ^ 2) := poisson_grid_bounds hN m b hb
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hbound : (m : ℝ) ≤ (n : ℝ) * (T + 1 / (n : ℝ)) := by
        dsimp [m]
        push_cast
        rw [mul_add, mul_one_div_cancel hn₀.ne']
        exact add_le_add_left (Nat.floor_le (mul_nonneg hn₀.le hT)) 1
      have hA := hN.rate_nonneg.trans ha
      have h1 := mul_le_mul ha hbound (Nat.cast_nonneg m) hA
      have hb_sq : b ^ 2 = R ^ 2 * n := by
        dsimp [b]
        rw [mul_pow, Real.sq_sqrt hn₀.le]
      rw [hb_sq, div_mul_eq_div_div_swap]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [div_le_iff₀ hn₀]
      linear_combination h1

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    UocInProb M.P
      (fun n ω t i => M.Rhat n ω (queueTime (X n) (Ψ n) ω i t / (n : ℝ)) i)
      (fun _ => 0) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  intro T hT ε hε
  refine tendsto_order.2 ⟨fun _ h => (not_lt_zero h).elim, fun η hη => ?_⟩
  let η' : ℝ := (min η 1).toReal
  have hηmin : 0 < min η (1 : ℝ≥0∞) := lt_min hη (by simp)
  have hηfin : min η (1 : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hη' : 0 < η' := ENNReal.toReal_pos (ne_of_gt hηmin) hηfin
  have hηle : ENNReal.ofReal η' ≤ η := (ENNReal.ofReal_toReal hηfin).trans_le (min_le_left _ _)
  let R : ℝ := ε / (4 * ((k : ℝ) + 1))
  have hR : 0 < R := div_pos hε (by positivity)
  have hFraction (a : ℝ) (ha : 0 < a) :
      (k : ℝ) * (a / (4 * ((k : ℝ) + 1))) < a / 4 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  let A : ℝ := 1 + ∑ i, M.theta i
  have hA : 0 < A := by
    dsimp [A]
    exact add_pos_of_pos_of_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => M.theta_nonneg i))
  have hRate : ∀ᶠ n : ℕ in atTop, ∀ i, M.thetaN n i ≤ A := by
    rw [eventually_all]
    intro i
    have hSmall : M.theta i < A := by
      dsimp [A]
      linarith [Finset.single_le_sum (f := M.theta) (fun j _ => M.theta_nonneg j) (Finset.mem_univ i)]
    exact ((tendsto_order.1 (M.theta_lim i)).2 A hSmall).mono (fun _ h => h.le)
  let δ := η' * R ^ 2 / (8 * ((k : ℝ) + 1) * A)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let Cl (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) := queueTime (X n) (Ψ n) ω i t / (n : ℝ)
  let Z (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) := M.Rhat n ω (Cl n ω t i) i
  let ECl (n : ℕ) : Set Ω := {ω | ENNReal.ofReal δ ≤ supDist (Cl n ω) (fun _ => 0) T}
  let ER (n : ℕ) (i : Fin k) : Set Ω :=
    {ω | ∃ t ∈ Icc (0 : ℝ) δ, R + A / Real.sqrt n < |M.Rhat n ω t i|}
  have hClS : Tendsto (fun n => M.P (ECl n)) atTop (𝓝 0) :=
    (queue_time_changes_uoc M X0 x hX0 X Ψ hC hWork).2 T hT δ hδ
  have hClEv : ∀ᶠ n in atTop, M.P (ECl n) < ENNReal.ofReal (η'/2) :=
    (tendsto_order.1 hClS).2 _ (ENNReal.ofReal_pos.mpr (by positivity))
  have hRSmall : ∀ᶠ n : ℕ in atTop, A / Real.sqrt n ≤ R := by
    have hroot : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => A / Real.sqrt n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hroot
    exact ((tendsto_order.1 hdiv).2 R hR).mono (fun _ h => h.le)
  have hNSmall : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ δ := by
    have hdiv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    exact ((tendsto_order.1 hdiv).2 δ hδ).mono (fun _ h => h.le)
  filter_upwards [hClEv, hRate, hRSmall, hNSmall, eventually_ge_atTop (1 : ℕ)]
    with n hClEv hnRate hnSmall hnTiny hn
  have hZ : {ω | ENNReal.ofReal ε ≤ supDist (Z n ω) (fun _ => 0) T} ⊆
      ECl n ∪ ⋃ i, ER n i := by
    intro ω hω
    by_contra hnω
    have hl (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) : Cl n ω t i ∈ Icc 0 δ := by
      have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      refine ⟨div_nonneg (intervalIntegral.integral_nonneg ht.1
        (fun s hs => (hC n hn).phi_nonneg ω s i hs.1)) hpos, ?_⟩
      by_contra! hT'
      have hf : ENNReal.ofReal δ ≤ ENNReal.ofReal (∑ j, |Cl n ω t j - (fun _ : Fin k => (0 : ℝ)) j|) :=
        ENNReal.ofReal_le_ofReal (hT'.le.trans ((le_abs_self _).trans (by
          simpa only [sub_zero] using (Finset.single_le_sum (f := fun j => |Cl n ω t j|)
            (fun j _ => abs_nonneg _) (Finset.mem_univ i)))))
      have hsup : ENNReal.ofReal δ ≤ supDist (Cl n ω) (fun _ => 0) T :=
        hf.trans (le_iSup₂_of_le t ht le_rfl)
      exact hnω (Or.inl hsup)
    have hBound (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) : |Z n ω t i| ≤ 2 * R := by
      have le : |Z n ω t i| ≤ R + A / Real.sqrt n := le_of_not_gt (fun h =>
        hnω (Or.inr (mem_iUnion.2 ⟨i, Cl n ω t i, hl t ht i, h⟩)))
      linarith
    have hsup : supDist (Z n ω) (fun _ => 0) T ≤ ENNReal.ofReal ((k : ℝ) * (2 * R)) := by
      unfold supDist
      refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
      simp only [Pi.zero_apply, sub_zero]
      exact (Finset.sum_le_sum (fun i _ => hBound t ht i)).trans_eq (by simp)
    have hεR : (k : ℝ) * (2 * R) < ε := by
      have hh := mul_lt_mul_of_pos_left (hFraction ε hε) (by norm_num : 0 < (2 : ℝ))
      unfold R
      rw [mul_left_comm]
      linarith
    exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff hε).2 hεR)) (hω.trans hsup)
  have hER (i : Fin k) : M.P (ER n i) ≤ ENNReal.ofReal (η' / (4 * ((k : ℝ) + 1))) := by
    refine (poisson_small_clock_bound (M.R_poisson n i) n hn A δ R (hnRate i) hδ.le hR).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have ha : A * (δ + 1 / (n : ℝ)) ≤ A * (2 * δ) := by
      gcongr
      linarith
    calc
      _ ≤ A * (2 * δ) / R ^ 2 := div_le_div_of_nonneg_right ha (sq_nonneg _)
      _ = η' / (4 * ((k : ℝ) + 1)) := by
        dsimp [δ]
        field_simp
        <;> ring
  have hUnion : M.P (⋃ i, ER n i) ≤ ENNReal.ofReal ((k : ℝ) * (η' / (4 * ((k : ℝ) + 1)))) := by
    refine (measure_iUnion_le _).trans ?_
    rw [tsum_fintype]
    exact (Finset.sum_le_sum (fun i _ => hER i)).trans_eq (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_nsmul]
      rw [nsmul_eq_mul])
  have hηR : η'/2 + (k : ℝ) * (η' / (4 * ((k : ℝ) + 1))) < η' := by
    linarith [hFraction η' hη']
  refine ((measure_mono hZ).trans (measure_union_le _ _)).trans_lt ?_
  refine (add_le_add hClEv.le hUnion).trans_lt ?_
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ η'/2)
    (by positivity : 0 ≤ (k : ℝ) * (η' / (4 * ((k : ℝ) + 1))))]
  exact ((ENNReal.ofReal_lt_ofReal_iff hη').2 hηR).trans_le hηle
