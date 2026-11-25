-- Prove2me | solution 1 for ManyServerQED.Scheduling.centered_poisson_scaled_sup_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:49:13.737422+00:00
-- url     : https://prove2.me/submissions/9e157500-d8d5-485d-b3d1-1c076d1825f3

import Theorems.Thm_AvramDividend_Classical_avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indep_naturalFiltration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
import Definitions.Def_ManyServerQED_Scheduling_Model

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

private theorem count_increment_nat {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ j : ℕ, N ω t - N ω s = j := by
  obtain ⟨a, ha⟩ := hN.nat_valued ω s hs
  obtain ⟨b, hb⟩ := hN.nat_valued ω t (hs.trans hst)
  have hab : a ≤ b := by
    exact_mod_cast (show (a : ℝ) ≤ (b : ℝ) from ha ▸ hb ▸ hN.mono ω hs (hs.trans hst) hst)
  exact ⟨b - a, by rw [ha, hb, Nat.cast_sub hab]⟩

private theorem nat_floor_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (ω : Ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (⌊N ω t - N ω s⌋₊ : ℝ) = N ω t - N ω s := by
  obtain ⟨j, hj⟩ := count_increment_nat hN ω hs hst
  rw [hj, Nat.floor_natCast]

private theorem map_floor_increment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Measure.map (fun ω => ⌊N ω t - N ω s⌋₊) P = poissonMeasure (rate * (t - s)).toNNReal := by
  apply Measure.ext_of_singleton
  intro j
  have hm : Measurable (fun ω => ⌊N ω t - N ω s⌋₊) := ((hN.meas t).sub (hN.meas s)).nat_floor
  rw [Measure.map_apply hm (measurableSet_singleton j)]
  convert hN.law s t hs hst j using 2
  ext ω
  change ⌊N ω t - N ω s⌋₊ = j ↔ N ω t - N ω s = j
  constructor
  · intro h
    rw [← nat_floor_increment hN ω hs hst, h]
  · intro h
    rw [h, Nat.floor_natCast]

private theorem count_increment_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IdentDistrib (fun ω => N ω t - N ω s) (fun ω => N ω (t - s)) P P := by
  have ht0 : 0 ≤ t - s := sub_nonneg.mpr hst
  have h1 := ((hN.meas t).sub (hN.meas s))
  have h2 := (hN.meas (t - s)).sub (hN.meas 0)
  have hmap : Measure.map (fun ω => ⌊N ω t - N ω s⌋₊) P =
      Measure.map (fun ω => ⌊N ω (t - s) - N ω 0⌋₊) P := by
    rw [map_floor_increment hN hs hst, map_floor_increment hN le_rfl ht0, sub_zero]
  have hId : IdentDistrib (fun ω => ⌊N ω t - N ω s⌋₊) (fun ω => ⌊N ω (t - s) - N ω 0⌋₊) P P :=
    ⟨h1.nat_floor.aemeasurable, h2.nat_floor.aemeasurable, hmap⟩
  have hC := hId.comp (measurable_of_countable (fun j : ℕ => (j : ℝ)))
  have hR (ω : Ω) : (⌊N ω (t - s) - N ω 0⌋₊ : ℝ) = N ω (t - s) := by
    rw [nat_floor_increment hN ω le_rfl ht0, hN.zero, sub_zero]
  simpa only [Function.comp_def, nat_floor_increment hN _ hs hst, hR] using hC

private theorem poisson_count_exp (r : ℝ≥0) (θ : ℝ) :
    Integrable (fun n : ℕ => Real.exp (θ * n)) (poissonMeasure r) ∧
    (∫ n : ℕ, Real.exp (θ * n) ∂poissonMeasure r) =
      Real.exp ((r : ℝ) * (Real.exp θ - 1)) := by
  let z := (r : ℝ) * Real.exp θ
  have hs : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℝ)) (Real.exp z) := by
    have h := (NormedSpace.expSeries_div_summable z).hasSum
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact h
  have ht (j : ℕ) : Real.exp (-↑r) * (r : ℝ)^j / (j.factorial : ℝ) * Real.exp (θ * (j : ℝ)) =
      Real.exp (-↑r) * (z ^ j / (j.factorial : ℝ)) := by
    rw [mul_comm θ, Real.exp_nat_mul]
    unfold z
    rw [mul_pow]
    ring
  have Has : HasSum (fun j : ℕ => Real.exp (-↑r) * (r : ℝ)^j / (j.factorial : ℝ) * Real.exp (θ * (j : ℝ)))
      (Real.exp (-↑r) * Real.exp z) := by
    simpa only [ht] using hs.mul_left (Real.exp (-↑r))
  have hInt : Integrable (fun n : ℕ => Real.exp (θ * n)) (poissonMeasure r) := by
    apply integrable_poissonMeasure_iff.mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using Has.summable
  refine ⟨hInt, ?_⟩
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [Has.tsum_eq, ← Real.exp_add]
  congr 1
  unfold z
  ring

private theorem centered_poisson_exp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate)
    (θ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    let D (ω : Ω) := N ω t - N ω s - rate * (t - s)
    Integrable (fun ω => Real.exp (θ * D ω)) P ∧
    (∫ ω, Real.exp (θ * D ω) ∂P) = Real.exp (rate * (t - s) * (Real.exp θ - 1 - θ)) := by
  let r : ℝ≥0 := (rate * (t - s)).toNNReal
  have hr : (r : ℝ) = rate * (t - s) :=
    Real.coe_toNNReal _ (mul_nonneg hN.rate_nonneg (sub_nonneg.mpr hst))
  let F (ω : Ω) := ⌊N ω t - N ω s⌋₊
  have hF : Measurable F := ((hN.meas t).sub (hN.meas s)).nat_floor
  have hMap : Measure.map F P = poissonMeasure r := map_floor_increment hN hs hst
  let f (j : ℕ) := Real.exp (θ * (j : ℝ))
  have hfM : Measurable f := measurable_of_countable _
  have hfI : Integrable f (Measure.map F P) := by rw [hMap]; exact (poisson_count_exp r θ).1
  have hEq (ω : Ω) : Real.exp (θ * (N ω t - N ω s - rate * (t - s))) =
      Real.exp (-θ * r) * f (F ω) := by
    rw [← hr, mul_sub, Real.exp_sub, div_eq_mul_inv, mul_comm, ← Real.exp_neg, neg_mul]
    dsimp only [f]
    rw [show (F ω : ℝ) = N ω t - N ω s from nat_floor_increment hN ω hs hst]
  dsimp only
  simp_rw [hEq]
  refine ⟨(hfI.comp_measurable hF).const_mul _, ?_⟩
  rw [integral_const_mul, ← integral_map hF.aemeasurable hfM.aestronglyMeasurable,
    hMap, (poisson_count_exp r θ).2, ← Real.exp_add]
  congr 1
  rw [← hr]
  ring

private theorem moment_le_exp_pair {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    |x| ^ p ≤ (⌈p⌉₊.factorial : ℝ) * (Real.exp x + Real.exp (-x)) := by
  let m := ⌈p⌉₊
  have hF : 1 ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hExp (a : ℝ) (ha : 0 ≤ a) : a ^ p ≤ (m.factorial : ℝ) * Real.exp a := by
    rcases le_total a 1 with h | h
    · refine (Real.rpow_le_one ha h hp).trans ?_
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (m.factorial : ℝ) * Real.exp a :=
          mul_le_mul hF (Real.one_le_exp_iff.mpr ha) zero_le_one (zero_le_one.trans hF)
    · have h := Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil p)
      rw [Real.rpow_natCast] at h
      have hf : 0 < (m.factorial : ℝ) := by positivity
      exact h.trans (by simpa [mul_comm] using (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp a ha m))
  have hPos : |x| ≥ 0 := abs_nonneg _
  refine (hExp |x| hPos).trans ?_
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hF)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_nonpos hx]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

open ManyServerQED.Scheduling

private theorem poisson_inc_moments {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N a) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
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


private theorem centered_grid_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {rate : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N rate) (d : ℝ) :
    Martingale (fun (j : ℕ) ω => (N ω (j : ℝ) - rate*j) / d)
      (Filtration.natural (fun (j : ℕ) ω => N ω (j : ℝ))
        (fun j => (hN.meas j).stronglyMeasurable)) P := by
  let X (j : ℕ) (ω : Ω) := N ω (j : ℝ)
  have hX : ∀ j, Measurable (X j) := fun j => hN.meas j
  let ℱ := Filtration.natural X (fun j => (hX j).stronglyMeasurable)
  let f (j : ℕ) (ω : Ω) := (X j ω - rate*j) / d
  have hZ : X 0 = fun _ => 0 := by funext ω; simpa only [X, Nat.cast_zero] using hN.zero ω
  have hIncr : HasIndependentIncrements X P := by
    intro m s hs
    exact hN.indep_incr m (fun j => (s j : ℝ)) (Nat.cast_nonneg _) (fun _ _ hij =>
      Nat.cast_le.mpr (hs hij))
  change Martingale f ℱ P
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro j
    have hle : MeasurableSpace.comap (X j) inferInstance ≤ ℱ j :=
      le_iSup₂_of_le j le_rfl le_rfl
    have h : Measurable[ℱ j] (X j) := measurable_iff_comap_le.2 hle
    exact ((h.sub_const _).div_const _).stronglyMeasurable
  · intro j
    have h := (poisson_inc_moments hN 0 j le_rfl (Nat.cast_nonneg _)).1.integrable (by norm_num)
    have hf : (fun ω => X j ω - rate*j) = (fun ω => N ω (j : ℝ) - N ω 0 - rate * (j - 0)) := by
      funext ω
      rw [hN.zero, sub_zero, sub_zero]
    exact (hf.symm ▸ h).div_const d
  · intro j
    let Δ (ω : Ω) := X (j+1) ω - X j ω
    have hi : Indep (MeasurableSpace.comap Δ inferInstance) (ℱ j) P :=
      hIncr.indep_naturalFiltration _ hZ (fun _ => Nat.zero_le _) (Nat.le_succ _)
    have hm : Measurable Δ := (hX _).sub (hX _)
    let C := MeasurableSpace.comap Δ inferInstance
    let g (ω : Ω) := (Δ ω - rate) / d
    have hgM : StronglyMeasurable[C] g :=
      (((comap_measurable Δ).sub_const _).div_const _).stronglyMeasurable
    have heq : f (j+1) - f j = g := by
      funext ω
      simp only [Pi.sub_apply, f, g, Δ, Nat.cast_add, Nat.cast_one, ← sub_div]
      ring_nf
    have hExp := (@poisson_inc_moments Ω mΩ P _ N rate hN (j : ℝ) ((j + 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.le_succ j)).2.1
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one] at hExp
    have hg : ∫ ω, g ω ∂P = 0 := by
      unfold g Δ X
      rw [integral_div]
      push_cast
      rw [hExp, zero_div]
    rw [heq]
    refine (condExp_indep_eq hm.comap_le (ℱ.le _) hgM hi).trans ?_
    rw [hg]
    exact Filter.EventuallyEq.rfl

open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

private theorem grid_max_lintegral {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) {p : ℝ} (hp : 1 < p) (m : ℕ) :
    let g (ω : Ω) := (Finset.range (m+1)).sup' Finset.nonempty_range_add_one (fun j => |f j ω|)
    (∫⁻ ω, ENNReal.ofReal (g ω)^p ∂P) ≤
      ENNReal.ofReal ((p / (p-1))^p) * ∫⁻ ω, ENNReal.ofReal |f m ω| ^ p ∂P := by
  let g (ω : Ω) := (Finset.range (m+1)).sup' Finset.nonempty_range_add_one (fun j => |f j ω|)
  have hg (ω : Ω) : 0 ≤ g ω :=
    (abs_nonneg (f 0 ω)).trans (Finset.le_sup' (fun j => |f j ω|) (Finset.mem_range.2 (by omega : 0 < m+1)))
  have h0p : 0 < p := zero_lt_one.trans hp
  have h := AvramDividend.Classical.avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal hf hp m
  simp only [Real.norm_eq_abs] at h
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr h0p) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr h0p) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal h0p.le] at h
  have h' := ENNReal.rpow_le_rpow h h0p.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0p.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    one_div_mul_cancel h0p.ne', ENNReal.rpow_one, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (div_nonneg h0p.le (sub_nonneg.mpr hp.le)) h0p.le] at h'
  have hAbs (ω : Ω) : |(Finset.range (m+1)).sup' Finset.nonempty_range_add_one (fun j => |f j ω|)| = g ω :=
    abs_of_nonneg (hg ω)
  simpa only [Real.enorm_eq_ofReal_abs, hAbs] using h' 

private theorem normalized_poisson_terminal_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → ℝ → ℝ} {a : ℝ} (hN : ManyServerQED.Scheduling.IsPoissonProcess P N a)
    (p A : ℝ) (hp : 0 ≤ p) (v θ : ℝ) (hv : 0 ≤ v) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hSmall : a * v * θ^2 ≤ A) :
    ∫⁻ ω, ENNReal.ofReal |θ * (N ω v - a * v)| ^ p ∂P ≤
      ENNReal.ofReal (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) := by
  let F (ω : Ω) := θ * (N ω v - a * v)
  let B := (⌈p⌉₊.factorial : ℝ)
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have H (s : ℝ) (hs : |s| ≤ θ) :
      Integrable (fun ω => Real.exp (s * (N ω v - a*v))) P ∧
      (∫ ω, Real.exp (s * (N ω v - a*v)) ∂P) ≤ Real.exp A := by
    have h := centered_poisson_exp hN s (s := 0) (t := v) le_rfl hv
    dsimp only at h
    simp only [hN.zero, sub_zero] at h
    refine ⟨h.1, h.2.le.trans ?_⟩
    apply Real.exp_le_exp.mpr
    have hdev := (le_abs_self (Real.exp s - 1 - s)).trans (Real.abs_exp_sub_one_sub_id_le (hs.trans hθ1))
    have hss : s^2 ≤ θ^2 := by
      rw [← sq_abs s]
      exact pow_le_pow_left₀ (abs_nonneg s) hs _
    exact (mul_le_mul_of_nonneg_left (hdev.trans hss) (mul_nonneg hN.rate_nonneg hv)).trans hSmall
  have hplus := H θ (by simp [abs_of_nonneg hθ])
  have hminus := H (-θ) (by simp [abs_of_nonneg hθ])
  have hi1 : Integrable (fun ω => Real.exp (F ω)) P := hplus.1
  have hi2 : Integrable (fun ω => Real.exp (-F ω)) P := by
    simpa only [F, neg_mul] using hminus.1
  let G (ω : Ω) := B * (Real.exp (F ω) + Real.exp (-F ω))
  have hGi : Integrable G P := (hi1.add hi2).const_mul B
  have hG0 : 0 ≤ᵐ[P] G := ae_of_all _ (fun ω => mul_nonneg hB (add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (G ω) ∂P := lintegral_mono (fun ω => by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp]
      exact ENNReal.ofReal_le_ofReal (moment_le_exp_pair hp (F ω)))
    _ = ENNReal.ofReal (∫ ω, G ω ∂P) := (ofReal_integral_eq_lintegral_ofReal hGi hG0).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      unfold G
      rw [integral_const_mul, integral_add hi1 hi2]
      have hNeg : (∫ ω, Real.exp (-F ω) ∂P) ≤ Real.exp A := by simpa only [F, neg_mul] using hminus.2
      have h := mul_le_mul_of_nonneg_left (add_le_add hplus.2 hNeg) hB
      exact h.trans_eq (by ring)

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : ManyServerQED.Scheduling.IsPoissonProcess P N a) (p A : ℝ) (hp : 1 < p)
    (hA : a ≤ A) (n : ℕ) (hn : 1 ≤ n) (T : ℝ) (hT : 0 ≤ T) :
    let C := (2 : ℝ)^p * (((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A) + A^p)
    ∫⁻ ω, (⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 T),
      ENNReal.ofReal |(N ω ((n : ℝ)*t) - a*(n : ℝ)*t) / Real.sqrt n|)^p ∂P ≤
      ENNReal.ofReal (C * (1+T)^p) := by
  let b := Real.sqrt (n : ℝ)
  let d := b*(1+T)
  let θ := 1/d
  let m : ℕ := ⌊(n : ℝ)*T⌋₊ + 1
  let F (j : ℕ) (ω : Ω) := (N ω (j : ℝ) - a*j)/d
  let g (ω : Ω) := (Finset.range (m+1)).sup' Finset.nonempty_range_add_one (fun j => |F j ω|)
  have hp0 : 0 ≤ p := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hb1 : 1 ≤ b := by simpa only [b, Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  have hb0 : 0 < b := Real.sqrt_pos.2 hn0
  have hd1 : 1 ≤ d := by
    have h : b ≤ b*(1+T) := le_mul_of_one_le_right hb0.le (by linarith)
    exact hb1.trans h
  have hd0 : 0 < d := zero_lt_one.trans_le hd1
  have hA0 : 0 ≤ A := hN.rate_nonneg.trans hA
  have hm : (m : ℝ) ≤ (n : ℝ) * (1+T) := by
    dsimp [m]
    push_cast
    have h := Nat.floor_le (mul_nonneg hn0.le hT)
    nlinarith
  have hθ0 : 0 ≤ θ := one_div_nonneg.mpr hd0.le
  have hθ1 : θ ≤ 1 := (div_le_iff₀ hd0).2 (by simpa using hd1)
  have hSmall : a*(m : ℝ)*θ^2 ≤ A := by
    have hnum : a*(m : ℝ) ≤ A*((n : ℝ)*(1+T)) :=
      mul_le_mul hA hm (Nat.cast_nonneg _) hA0
    have hnum2 : A*((n : ℝ)*(1+T)) ≤ A*((n : ℝ)*(1+T)^2) := by
      gcongr
      have h : 1 ≤ 1+T := by linarith
      nlinarith
    have hd2 : d^2 = (n : ℝ)*(1+T)^2 := by
      rw [show d = b*(1+T) from rfl, mul_pow, Real.sq_sqrt hn0.le]
    rw [show θ = 1/d from rfl, div_pow, one_pow, mul_one_div]
    exact (div_le_iff₀ (sq_pos_of_pos hd0)).2 (by rw [hd2]; exact hnum.trans hnum2)
  let B := ((p/(p-1))^p) * (2 * (⌈p⌉₊.factorial : ℝ) * Real.exp A)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hG : ∫⁻ ω, ENNReal.ofReal (g ω)^p ∂P ≤ ENNReal.ofReal B := by
    have hD := grid_max_lintegral (centered_grid_martingale hN d) hp m
    have hTer := normalized_poisson_terminal_moment hN p A hp0 (m : ℝ) θ (Nat.cast_nonneg _)
      hθ0 hθ1 hSmall
    have hFmt : ∀ ω, F m ω = θ * (N ω (m : ℝ) - a * (m : ℝ)) := by
      intro ω
      simp only [F, θ, div_eq_mul_inv, one_mul, mul_comm]
    dsimp only at hD
    simp only [← hFmt] at hTer
    refine hD.trans ((mul_le_mul_right hTer _).trans_eq ?_)
    exact (ENNReal.ofReal_mul (by positivity)).symm
  have hg0 (ω : Ω) : 0 ≤ g ω :=
    (abs_nonneg (F 0 ω)).trans (Finset.le_sup' (fun j => |F j ω|) (Finset.mem_range.2 (by omega : 0 < m+1)))
  have hgU (ω : Ω) (j : ℕ) (hj : j ≤ m) : |F j ω| ≤ g ω :=
    Finset.le_sup' (fun j => |F j ω|) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hscale (ω : Ω) (j : ℕ) (hj : j ≤ m) :
      |N ω (j : ℝ) - a * (j : ℝ)| ≤ d * g ω := by
    have h := hgU ω j hj
    change |(N ω (j : ℝ) - a * (j : ℝ)) / d| ≤ _ at h
    rw [abs_div, abs_of_pos hd0] at h
    exact ((div_le_iff₀ hd0).1 h).trans_eq (mul_comm _ _)
  have hpoint (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 T) :
      |(N ω ((n : ℝ)*t) - a*(n : ℝ)*t) / b| ≤ (1+T) * g ω + A := by
    let j : ℕ := ⌊(n : ℝ)*t⌋₊
    have hj0 : (j : ℝ) ≤ (n : ℝ)*t := Nat.floor_le (mul_nonneg hn0.le ht.1)
    have hj1 : (n : ℝ)*t ≤ ((j+1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one ((n : ℝ)*t)).le
    have hj : j+1 ≤ m := Nat.succ_le_succ (Nat.floor_mono (mul_le_mul_of_nonneg_left ht.2 hn0.le))
    have h0 := (abs_le.1 (hscale ω j (Nat.le_of_succ_le hj))).1
    have h1 := (abs_le.1 (hscale ω (j+1) hj)).2
    have hnt : (n : ℝ)*t ∈ Ici (0 : ℝ) := mul_nonneg hn0.le ht.1
    have hja : (j : ℝ) ∈ Ici (0 : ℝ) := by
      change (0 : ℝ) ≤ (j : ℝ)
      exact Nat.cast_nonneg j
    have hjb : ((j+1 : ℕ) : ℝ) ∈ Ici (0 : ℝ) := by
      change (0 : ℝ) ≤ ((j+1 : ℕ) : ℝ)
      exact Nat.cast_nonneg (j+1)
    have hm0 := hN.mono ω hja hnt hj0
    have hm1 := hN.mono ω hnt hjb hj1
    have hL := mul_le_mul_of_nonneg_left hj0 hN.rate_nonneg
    have hU := mul_le_mul_of_nonneg_left hj1 hN.rate_nonneg
    push_cast at h1 hm1 hU
    rw [abs_div, abs_of_pos hb0, div_le_iff₀ hb0, abs_le]
    have hA' : a ≤ A*b := hA.trans (le_mul_of_one_le_right hA0 hb1)
    dsimp only [d] at h0 h1
    constructor <;> nlinarith
  let V (ω : Ω) := ⨆ t : ℝ, ⨆ (_ : t ∈ Icc 0 T),
    ENNReal.ofReal |(N ω ((n : ℝ)*t) - a*(n : ℝ)*t) / b|
  have hV (ω : Ω) : V ω ≤ ENNReal.ofReal ((1+T) * g ω + A) :=
    iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal (hpoint ω t ht)
  let aT := ENNReal.ofReal ((1+T)^p)
  let aP := ENNReal.ofReal (2^p)
  have hVW (ω : Ω) : V ω ^ p ≤
      aP * aT * (ENNReal.ofReal (g ω)^p + ENNReal.ofReal (A^p)) := by
    refine (ENNReal.rpow_le_rpow (hV ω) hp0).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg (by linarith) (hg0 ω)) hA0,
      ENNReal.ofReal_mul (by linarith : 0 ≤ 1+T)]
    refine (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp0).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.ofReal_rpow_of_nonneg hA0 hp0]
    unfold aP aT
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp0,
      ← ENNReal.ofReal_rpow_of_nonneg (by linarith : 0 ≤ 1+T) hp0]
    have hpow : 1 ≤ ENNReal.ofReal (1+T) ^ p := by
      have haT : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1+T) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow haT hp0
    have hh : ENNReal.ofReal A ^ p ≤ ENNReal.ofReal (1+T) ^ p * ENNReal.ofReal A ^ p :=
      le_mul_of_one_le_left' hpow
    simp only [ENNReal.ofReal_ofNat]
    calc
      _ ≤ (2:ℝ≥0∞)^p * ((ENNReal.ofReal (1+T)^p) * ENNReal.ofReal (g ω)^p +
          (ENNReal.ofReal (1+T)^p) * ENNReal.ofReal A ^ p) :=
        mul_le_mul_right (add_le_add le_rfl hh) _
      _ = _ := by
        rw [← mul_add, ← mul_assoc]
  dsimp only
  change (∫⁻ ω, V ω ^ p ∂P) ≤ _
  refine (lintegral_mono hVW).trans ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  calc
    _ ≤ aP * aT * (ENNReal.ofReal B + ENNReal.ofReal (A^p)) := by gcongr
    _ = _ := by
      unfold aP aT
      rw [← ENNReal.ofReal_add hB (Real.rpow_nonneg hA0 _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _))]
      congr 1
      unfold B
      ring
