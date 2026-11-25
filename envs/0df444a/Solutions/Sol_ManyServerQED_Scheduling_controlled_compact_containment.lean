-- Prove2me | solution 1 for ManyServerQED.Scheduling.controlled_compact_containment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:53:34.001818+00:00
-- url     : https://prove2.me/submissions/3dbc6b0a-475b-4cf4-bf94-2bfee6ad93f6

import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_DurrettProbability_kolmogorov_maximal_inequality
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_TeschlODE_IVP_gronwall_generalized

open MeasureTheory ProbabilityTheory Filter Topology
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

private theorem poisson_scaled_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ} {a : ℝ}
    (hN : IsPoissonProcess P N a) (n : ℕ) (hn : 1 ≤ n)
    (A T R : ℝ) (ha : a ≤ A) (hT : 0 ≤ T) (hR : 0 < R) :
    P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, R + A <
      |(N ω (n * t) - n * a * t) / Real.sqrt n|} ≤ ENNReal.ofReal (A * (T + 2) / R ^ 2) := by
  let m : ℕ := ⌊(n : ℝ) * T⌋₊ + 1
  let b : ℝ := R * Real.sqrt n
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  have hs₁ : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn₁
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
      have hA := hN.rate_nonneg.trans ha
      have h := mul_le_mul_of_nonneg_left hs₁ hA
      dsimp [b]
      rw [add_mul]
      linarith
    _ ≤ ENNReal.ofReal (a * m / b ^ 2) := poisson_grid_bounds hN m b hb
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hbound : (m : ℝ) ≤ (n : ℝ) * (T + 2) := by
        dsimp [m]
        push_cast
        have := Nat.floor_le (mul_nonneg hn₀.le hT)
        nlinarith
      have hA := hN.rate_nonneg.trans ha
      have h1 := mul_le_mul ha hbound (Nat.cast_nonneg m) hA
      have hb_sq : b ^ 2 = R ^ 2 * n := by
        dsimp [b]
        rw [mul_pow, Real.sq_sqrt hn₀.le]
      rw [hb_sq, div_mul_eq_div_div_swap]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [div_le_iff₀ hn₀]
      linear_combination h1

private theorem renewal_bracket {e : ℕ → ℝ} (he : StrictMono e) {s : ℝ} {m : ℕ}
    (h0 : e 0 ≤ s) (hm : s < e m) :
    ∃ j < m, e j ≤ s ∧ s < e (j + 1) ∧ renewalCount e s = j := by
  have hExists : ∃ i, s < e i := ⟨m, hm⟩
  let b := Nat.find hExists
  have hb : s < e b := Nat.find_spec hExists
  have hb_le : b ≤ m := Nat.find_min' hExists hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  have hj : e j ≤ s := le_of_not_gt (Nat.find_min hExists hj_lt)
  have hj_succ : s < e (j + 1) := by rwa [hsucc]
  refine ⟨j, hj_lt.trans_le hb_le, hj, hj_succ, le_antisymm ?_ ?_⟩
  · unfold renewalCount
    refine iSup_le fun r => iSup_le fun hr => ?_
    have h : r ≤ j := by
      by_contra! hjr
      exact (not_lt_of_ge hr) (hj_succ.trans_le (he.monotone hjr))
    exact_mod_cast h
  · unfold renewalCount
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

private theorem partialSum_shift {Ω : Type*} (U : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    DurrettProbability.partialSum (fun j ω => U (j + 1) ω - 1) m ω =
      partialSum (fun j => U j ω) m - m := by
  rw [DurrettProbability.partialSum, Finset.sum_sub_distrib]
  have hs : (∑ j ∈ Finset.range m, U (j + 1) ω) = ∑ j ∈ Finset.Icc 1 m, U j ω := by
    rw [show Finset.Icc 1 m = Finset.Ico 1 (m + 1) from by ext; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, add_comm]
  rw [hs]
  simp [partialSum]

private theorem renewal_grid_bounds {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (m : ℕ) (b : ℝ) (hb : 0 < b) :
    M.P {ω | ∃ j ≤ m, b ≤ |partialSum (fun r => M.U i r ω) j - j|} ≤
      ENNReal.ofReal ((m : ℝ) * M.cU2 i / b ^ 2) := by
  let : IsProbabilityMeasure M.P := M.isProb
  let X : ℕ → Ω → ℝ := fun j ω => M.U i (j + 1) ω - 1
  have hmeas (j : ℕ) : Measurable (X j) := (M.U_meas i (j + 1)).sub_const _
  have hraw : iIndepFun (fun j => M.U i (j + 1)) M.P := by
    let g : ℕ → (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k) := fun j => Sum.inl (i, j)
    have hg : Function.Injective g := fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)
    exact (M.indep 0).precomp hg
  have hind : iIndepFun X M.P := hraw.comp (fun (_ : ℕ) (y : ℝ) => y - 1) (fun _ => measurable_id.sub_const _)
  have hL2 (j : ℕ) : MemLp (M.U i (j + 1)) 2 M.P :=
    (M.U_ident i (j + 1) (by omega)).memLp_iff.2 (M.U_memLp i)
  have hXi (j : ℕ) : MemLp (X j) 2 M.P := (hL2 j).sub (memLp_const _)
  have hmean (j : ℕ) : (∫ ω, X j ω ∂M.P) = 0 := by
    change (∫ ω, (M.U i (j + 1) ω - 1) ∂M.P) = 0
    rw [integral_sub ((hL2 j).integrable (by norm_num)) (integrable_const _),
      (M.U_ident i (j + 1) (by omega)).integral_eq, M.U_mean]
    simp
  have hvariance (j : ℕ) : variance (X j) M.P = M.cU2 i := by
    rw [show X j = fun ω => M.U i (j + 1) ω - 1 from rfl,
      variance_sub_const (M.U_meas i (j + 1)).aestronglyMeasurable]
    exact (M.U_ident i (j + 1) (by omega)).variance_eq
  have htotal : variance (DurrettProbability.partialSum X m) M.P = (m : ℝ) * M.cU2 i := by
    rw [show DurrettProbability.partialSum X m = ∑ j ∈ Finset.range m, X j from by
      funext ω; simp [DurrettProbability.partialSum, Finset.sum_apply]]
    rw [IndepFun.variance_sum (fun j _ => hXi j) (fun a _ b _ hab => hind.indepFun hab)]
    simp [hvariance]
  have hk := DurrettProbability.kolmogorov_maximal_inequality X hmeas hind hXi hmean m b hb
  rw [htotal] at hk
  have heq : {ω | ∃ j ≤ m, b ≤ |partialSum (fun r => M.U i r ω) j - j|} =
      {ω | ∃ j ∈ Finset.Icc 1 m, b ≤ |DurrettProbability.partialSum X j ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.mem_Icc, X, partialSum_shift]
    constructor
    · rintro ⟨j, hj, hjb⟩
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        simp [partialSum] at hjb
        linarith
      exact ⟨j, ⟨Nat.one_le_iff_ne_zero.mpr hj0, hj⟩, hjb⟩
    · rintro ⟨j, hj, hjb⟩
      exact ⟨j, hj.2, hjb⟩
  rw [heq, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hk

private theorem renewal_scaled_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (n : ℕ) (hn : 1 ≤ n)
    (A T R : ℝ) (hA : 0 ≤ A) (ha : M.lamN n i ≤ A * n) (hT : 0 ≤ T) (hR : 0 < R)
    (hRn : R ≤ Real.sqrt n) :
    M.P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, R + 1 < |M.Ahat n ω t i|} ≤
      ENNReal.ofReal ((A * T + 3) * M.cU2 i / R ^ 2) := by
  let m : ℕ := ⌊(n : ℝ) * (A * T + 2)⌋₊ + 1
  let b : ℝ := R * Real.sqrt n
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn₀
  have hs₁ : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn₁
  have hb : 0 < b := mul_pos hR hs
  have hbn : b ≤ n := by
    dsimp [b]
    exact (mul_le_mul_of_nonneg_right hRn hs.le).trans_eq (Real.mul_self_sqrt hn₀.le)
  let rate : ℝ := M.lamN n i
  have hrate : 0 < rate := M.lamN_pos n i
  let E (ω : Ω) (j : ℕ) := partialSum (fun r => M.U i r ω) j
  have hE (ω : Ω) (j : ℕ) : M.arrivalEpoch n i ω j = E ω j / rate := by
    simp [SystemSequence.arrivalEpoch, E, partialSum, Finset.sum_div, rate]
  have hbase : 0 ≤ (n : ℝ) * (A * T + 2) := by positivity
  calc
    _ ≤ M.P {ω | ∃ j ≤ m, b ≤ |E ω j - j|} := by
      apply measure_mono
      intro ω hω
      obtain ⟨t, ht, htbad⟩ := hω
      by_contra hg
      have gh (j : ℕ) (hj : j ≤ m) : |E ω j - j| ≤ b :=
        (lt_of_not_ge fun h => hg ⟨j, hj, h⟩).le
      have hm : t < M.arrivalEpoch n i ω m := by
        rw [hE, lt_div_iff₀ hrate]
        have hf : (n : ℝ) * (A * T + 2) < (m : ℝ) := by
          simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((n : ℝ) * (A * T + 2))
        have htRate : t * rate ≤ T * (A * n) :=
          mul_le_mul ht.2 ha hrate.le hT
        have hl := (abs_le.mp (gh m le_rfl)).1
        nlinarith
      have hmono : StrictMono (M.arrivalEpoch n i ω) := by
        apply strictMono_nat_of_lt_succ
        intro j
        have hpos : 0 < M.U i (j + 1) ω := M.U_pos i _ ω (by omega)
        rw [hE, hE]
        apply (div_lt_div_iff_of_pos_right hrate).2
        dsimp [E, partialSum]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
        linarith
      obtain ⟨j, hj, h1, h2, hcount⟩ := renewal_bracket hmono
        (by simpa [hE, E, partialSum] using ht.1) hm
      have hAeq : M.A n i ω t = j := by
        simp [SystemSequence.A, hcount]
      rw [hE, div_le_iff₀ hrate] at h1
      rw [hE, lt_div_iff₀ hrate] at h2
      have h20 := (abs_le.mp (gh j hj.le)).1
      have h21 := (abs_le.mp (gh (j + 1) (Nat.succ_le_of_lt hj))).2
      push_cast at h21 h2
      have habs : |(j : ℝ) - rate * t| ≤ b + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      apply not_le_of_gt htbad
      unfold SystemSequence.Ahat
      rw [hAeq, abs_div, abs_of_pos hs]
      apply (div_le_iff₀ hs).2
      change |(j : ℝ) - rate * t| ≤ _
      refine habs.trans ?_
      dsimp [b]
      rw [add_mul, one_mul]
      linarith
    _ ≤ ENNReal.ofReal ((m : ℝ) * M.cU2 i / b ^ 2) := renewal_grid_bounds M i m b hb
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hbound : (m : ℝ) ≤ (n : ℝ) * (A * T + 3) := by
        dsimp [m]
        push_cast
        have := Nat.floor_le hbase
        nlinarith
      have h1 := mul_le_mul_of_nonneg_right hbound (variance_nonneg (M.U i 1) M.P)
      have hb_sq : b ^ 2 = R ^ 2 * n := by
        dsimp [b]
        rw [mul_pow, Real.sq_sqrt hn₀.le]
      rw [hb_sq, div_mul_eq_div_div_swap]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [div_le_iff₀ hn₀]
      have h1' : (m : ℝ) * M.cU2 i ≤ (n : ℝ) * (A * T + 3) * M.cU2 i := h1
      linear_combination h1'

private noncomputable def inputRate {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) : ℝ :=
  (M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n

private theorem inputRate_tendsto {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) :
    Tendsto (fun n => inputRate M n i) atTop (𝓝 (M.ell i)) := by
  have hlim := (M.lamHat_lim i).sub (tendsto_const_nhds.mul (M.muHat_lim i) :
    Tendsto (fun n : ℕ => M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) atTop
      (𝓝 (M.rho i * M.muHat i)))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have hmul : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hρ : M.rho i * M.mu i = M.lam i := div_mul_cancel₀ _ (M.mu_pos i).ne'
  unfold inputRate
  symm
  apply (div_eq_iff hs.ne').2
  symm
  calc
    (Real.sqrt (n : ℝ) * (M.lamN n i / n - M.lam i) -
        M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) * Real.sqrt n =
      (Real.sqrt n * Real.sqrt n) *
        (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) := by ring
    _ = _ := by
      rw [hmul]
      calc
        (n : ℝ) * (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) =
            M.lamN n i - (n : ℝ) * M.lam i -
              (n : ℝ) * M.rho i * M.muN n i + (n : ℝ) * (M.rho i * M.mu i) := by
          rw [mul_sub, mul_sub, mul_div_cancel₀ _ hn'.ne']
          ring
        _ = _ := by rw [hρ]; ring

private theorem integral_gronwall (g : ℝ → ℝ) (T A C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hint : ∀ t ∈ Set.Icc 0 T, IntervalIntegrable g volume 0 t)
    (hbound : ∀ t ∈ Set.Icc 0 T, g t ≤ A + C * ∫ s in (0 : ℝ)..t, g s) :
    ∀ t ∈ Set.Icc 0 T, g t ≤ A * Real.exp (C * t) := by
  let G (t : ℝ) := A + C * ∫ s in (0 : ℝ)..t, g s
  have hgcont : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, g s) (Set.Icc 0 T) := by
    simpa only [Set.uIcc_of_le hT] using
      (intervalIntegral.continuousOn_primitive_interval' (hint T ⟨hT, le_rfl⟩)
        (Set.left_mem_uIcc (a := (0 : ℝ)) (b := T)))
  have hG : ContinuousOn G (Set.Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul hgcont)
  have hineq (t : ℝ) (ht : t ∈ Set.Icc 0 T) : G t ≤ A + ∫ s in (0 : ℝ)..t, C * G s := by
    rw [intervalIntegral.integral_const_mul]
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ hC
    have hGi : IntervalIntegrable G volume 0 t :=
      (hG.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    exact intervalIntegral.integral_mono_on ht.1 (hint t ht) hGi
      (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩)
  have happly := TeschlODE.IVP.gronwall_generalized G (fun _ => A) (fun _ => C) T hG
    continuousOn_const continuousOn_const (fun _ _ => hC) hineq
  intro t ht
  refine (hbound t ht).trans ?_
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm t C] using
    happly.2 (fun _ _ _ _ _ => le_rfl) t ht

private theorem abs_sub_le_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

private theorem pathwise_state_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hc : M.IsControlled n X0 X Ψ)
    (hq : ∀ ω t i, 0 ≤ t → X ω t i - Ψ ω t i ≤ max ((∑ j, X ω t j) - n) 0)
    (a B T : ℝ) (ha : 1 ≤ a) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ha_n : a ≤ Real.sqrt n) (hB_n : B ≤ Real.sqrt n)
    (hRates : ∀ i, M.lamN n i ≤ a * n ∧ M.muN n i ≤ a ∧ M.thetaN n i ≤ a ∧
      |inputRate M n i| ≤ a ∧ |M.Xhat0 n X0 i| ≤ a ∧ M.rho i ≤ a)
    (ω : Ω)
    (hNoise : ∀ t ∈ Set.Icc 0 ((a + 2 + a * T) * (T + 1)), ∀ i,
      |M.Ahat n ω t i| ≤ B ∧ |M.Shat n ω t i| ≤ B ∧ |M.Rhat n ω t i| ≤ B) :
    ∀ t ∈ Set.Icc 0 T,
      ‖M.Xhat n X ω t‖ ≤ ((k : ℝ) * (a + 3 * B + a * T) + 1) *
        Real.exp (3 * a * (k : ℝ) * T) := by
  let p : ℝ := Real.sqrt n
  let d : ℝ := a + 2 + a * T
  let H : ℝ := d * (T + 1)
  let A : ℝ := (k : ℝ) * (a + 3 * B + a * T) + 1
  let C : ℝ := 3 * a * (k : ℝ)
  have ha0 : 0 ≤ a := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < p := Real.sqrt_pos.2 hn'
  have hp2 : p * p = n := Real.mul_self_sqrt hn'.le
  have hd : 1 ≤ d := by dsimp [d]; nlinarith
  have hTH : T ≤ H := by
    have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ T + 1 by linarith)
    dsimp [H]
    linarith
  have hDH : d * T ≤ H := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hb_n : B * p ≤ n := (mul_le_mul_of_nonneg_right hB_n hp.le).trans_eq hp2
  have hx0le (i : Fin k) : (X0 i : ℝ) ≤ (a + 1) * n := by
    have hi := ((abs_le.mp (hRates i).2.2.2.2.1).2)
    change ((X0 i : ℝ) - M.rho i * n) / p ≤ a at hi
    have han : a * p ≤ n := (mul_le_mul_of_nonneg_right ha_n hp.le).trans_eq hp2
    have hρ := mul_le_mul_of_nonneg_right (hRates i).2.2.2.2.2 hn'.le
    have hi' := (div_le_iff₀ hp).1 hi
    linarith
  have hPsi (t : ℝ) (ht : 0 ≤ t) (i : Fin k) : Ψ ω t i ≤ n :=
    (Finset.single_le_sum (fun j _ => hc.psi_nonneg ω t j ht) (Finset.mem_univ i)).trans
      (hc.servers ω t ht)
  have hTimes0 (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      0 ≤ busyTime Ψ ω i t ∧ 0 ≤ queueTime X Ψ ω i t :=
    ⟨intervalIntegral.integral_nonneg ht (fun s hs => hc.psi_nonneg ω s i hs.1),
      intervalIntegral.integral_nonneg ht (fun s hs => hc.phi_nonneg ω s i hs.1)⟩
  have hXle (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i : Fin k) : X ω t i ≤ d * n := by
    have hR := (M.R_poisson n i).mono ω (show (0 : ℝ) ≤ 0 by rfl)
      (hTimes0 t ht.1 i).2 (hTimes0 t ht.1 i).2
    have hS := (M.S_poisson n i).mono ω (show (0 : ℝ) ≤ 0 by rfl)
      (hTimes0 t ht.1 i).1 (hTimes0 t ht.1 i).1
    rw [(M.R_poisson n i).zero ω] at hR
    rw [(M.S_poisson n i).zero ω] at hS
    have hArr := (abs_le.mp (hNoise t ⟨ht.1, ht.2.trans hTH⟩ i).1).2
    change (M.A n i ω t - M.lamN n i * t) / p ≤ B at hArr
    have hArr' := (div_le_iff₀ hp).1 hArr
    have hrate := mul_le_mul (hRates i).1 ht.2 ht.1 (by positivity)
    dsimp [d]
    linarith [hc.eq7 ω t i ht.1, hx0le i]
  have hTimes (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i : Fin k) :
      busyTime Ψ ω i t / n ∈ Set.Icc 0 H ∧ queueTime X Ψ ω i t / n ∈ Set.Icc 0 H := by
    have hv := hc.integrable ω i t ht.1
    refine ⟨⟨div_nonneg (hTimes0 t ht.1 i).1 hn'.le, ?_⟩,
      ⟨div_nonneg (hTimes0 t ht.1 i).2 hn'.le, ?_⟩⟩
    · have hb : busyTime Ψ ω i t ≤ (n : ℝ) * t := by
        unfold busyTime
        have hh := intervalIntegral.integral_mono_on ht.1 hv.1
          (intervalIntegrable_const (c := (n : ℝ))) (fun s hs => hPsi s hs.1 i)
        simpa [intervalIntegral.integral_const, mul_comm t (n : ℝ)] using hh
      exact ((div_le_iff₀ hn').2 (by linarith : busyTime Ψ ω i t ≤ t * n)).trans (ht.2.trans hTH)
    · have hq' : queueTime X Ψ ω i t ≤ d * (n : ℝ) * t := by
        unfold queueTime
        have hh := intervalIntegral.integral_mono_on ht.1 hv.2
          (intervalIntegrable_const (c := d * (n : ℝ))) (fun s hs => by
            have h := hXle s ⟨hs.1, hs.2.trans ht.2⟩ i
            linarith [hc.psi_nonneg ω s i hs.1])
        simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm t (d * (n : ℝ))] using hh
      have hi : queueTime X Ψ ω i t / n ≤ d * t := (div_le_iff₀ hn').2 (by
        calc
          _ ≤ d * (n : ℝ) * t := hq'
          _ = _ := by ring)
      exact hi.trans ((mul_le_mul_of_nonneg_left ht.2 (by linarith : 0 ≤ d)).trans hDH)
  let xx : ℝ → Fin k → ℝ := fun t => M.Xhat n X ω t
  let pp : ℝ → Fin k → ℝ := fun t => M.Psihat n Ψ ω t
  let qq : ℝ → Fin k → ℝ := fun t => Phihat n X Ψ ω t
  let g : ℝ → ℝ := fun t => l1norm (xx t)
  have hsum (t : ℝ) :
      ∑ j, xx t j = ((∑ j, X ω t j) - n) / p := by
    simp only [xx, SystemSequence.Xhat, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul,
      show (∑ j, M.rho j) = 1 from M.sum_rho, one_mul, p]
  have hgi (t : ℝ) (i : Fin k) : |xx t i| ≤ g t :=
    Finset.single_le_sum (fun j _ => abs_nonneg (xx t j)) (Finset.mem_univ i)
  have hg0 (t : ℝ) : 0 ≤ g t := Finset.sum_nonneg (fun i _ => abs_nonneg (xx t i))
  have hq_bound (t : ℝ) (ht : 0 ≤ t) (i : Fin k) : |qq t i| ≤ g t := by
    have hq0 : 0 ≤ qq t i := div_nonneg (hc.phi_nonneg ω t i ht) hp.le
    rw [abs_of_nonneg hq0]
    refine (div_le_div_of_nonneg_right (hq ω t i ht) hp.le).trans ?_
    rw [← max_div_div_right hp.le, zero_div, ← hsum]
    apply max_le _ (hg0 t)
    exact Finset.sum_le_sum (fun j _ => le_abs_self _)
  have hp_bound (t : ℝ) (ht : 0 ≤ t) (i : Fin k) : |pp t i| ≤ 2 * g t := by
    have heq : pp t i = xx t i - qq t i := by
      change (Ψ ω t i - M.rho i * n) / p =
        (X ω t i - M.rho i * n) / p - (X ω t i - Ψ ω t i) / p
      ring
    rw [heq]
    exact (abs_sub_le_add_abs _ _).trans (by linarith [hgi t i, hq_bound t ht i])
  have hint (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      IntervalIntegrable (fun s => pp s i) volume 0 t ∧
      IntervalIntegrable (fun s => qq s i) volume 0 t ∧
      IntervalIntegrable (fun s => xx s i) volume 0 t := by
    have h := hc.integrable ω i t ht
    have hpi : IntervalIntegrable (fun s => pp s i) volume 0 t :=
      (h.1.sub (intervalIntegrable_const (c := M.rho i * n))).div_const p
    have hqi : IntervalIntegrable (fun s => qq s i) volume 0 t := h.2.div_const p
    refine ⟨hpi, hqi, ?_⟩
    have hx : (fun s => xx s i) = (fun s => pp s i + qq s i) := by
      funext s
      change (X ω s i - M.rho i * n) / p =
        (Ψ ω s i - M.rho i * n) / p + (X ω s i - Ψ ω s i) / p
      ring
    rw [hx]
    exact hpi.add hqi
  have hgi_int (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable g volume 0 t :=
    by
      have heq : g = ∑ i, (fun s => |xx s i|) := by
        funext s
        simp [g, l1norm, Finset.sum_apply]
      rw [heq]
      exact IntervalIntegrable.sum Finset.univ (fun i _ => (hint t ht i).2.2.abs)
  have hbalance (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      xx t i = M.Xhat0 n X0 i + M.Ahat n ω t i -
        M.Rhat n ω (queueTime X Ψ ω i t / n) i - M.Shat n ω (busyTime Ψ ω i t / n) i +
        inputRate M n i * t -
        M.muN n i * (∫ s in (0 : ℝ)..t, pp s i) -
        M.thetaN n i * (∫ s in (0 : ℝ)..t, qq s i) := by
    have hIntP : (∫ s in (0 : ℝ)..t, pp s i) = (busyTime Ψ ω i t - t * (M.rho i * n)) / p := by
      change (∫ s in (0 : ℝ)..t, (Ψ ω s i - M.rho i * n) / p) = _
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub (hc.integrable ω i t ht).1 intervalIntegrable_const]
      simp only [busyTime, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hIntQ : (∫ s in (0 : ℝ)..t, qq s i) = queueTime X Ψ ω i t / p := by
      exact intervalIntegral.integral_div _ _
    rw [hIntP, hIntQ]
    simp only [xx, SystemSequence.Xhat, SystemSequence.Xhat0, SystemSequence.Ahat, SystemSequence.Rhat,
      SystemSequence.Shat, inputRate]
    rw [hc.eq7 ω t i ht]
    dsimp [p]
    have hnz := hn'.ne'
    have div_time (s : ℝ) : (n : ℝ) * (s / n) = s := mul_div_cancel₀ _ hnz
    have div_rate (r s : ℝ) : (n : ℝ) * r * (s / n) = r * s := by
      rw [mul_comm (n : ℝ) r, mul_assoc, div_time]
    rw [div_time, div_time, div_rate, div_rate]
    ring
  have h_g (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      g t ≤ A + C * ∫ s in (0 : ℝ)..t, g s := by
    let I : ℝ := ∫ s in (0 : ℝ)..t, g s
    have hI : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall ht.1 hg0
    have hcomp (i : Fin k) : |xx t i| ≤ a + 3 * B + a * T + (3 * a) * I := by
      have harr := (hNoise t ⟨ht.1, ht.2.trans hTH⟩ i).1
      have hrr := (hNoise _ (hTimes t ht i).2 i).2.2
      have hss := (hNoise _ (hTimes t ht i).1 i).2.1
      have hrP : |∫ s in (0 : ℝ)..t, pp s i| ≤ 2 * I := by
        refine (intervalIntegral.abs_integral_le_integral_abs ht.1).trans ?_
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on ht.1 (hint t ht.1 i).1.abs
          ((hgi_int t ht.1).const_mul _) (fun s hs => hp_bound s hs.1 i)
      have hrQ : |∫ s in (0 : ℝ)..t, qq s i| ≤ I :=
        (intervalIntegral.abs_integral_le_integral_abs ht.1).trans
          (intervalIntegral.integral_mono_on ht.1 (hint t ht.1 i).2.1.abs (hgi_int t ht.1)
            (fun s hs => hq_bound s hs.1 i))
      have hP : |M.muN n i * ∫ s in (0 : ℝ)..t, pp s i| ≤ a * (2 * I) := by
        rw [abs_mul, abs_of_pos (M.muN_pos n i)]
        exact mul_le_mul (hRates i).2.1 hrP (abs_nonneg _) ha0
      have hQ : |M.thetaN n i * ∫ s in (0 : ℝ)..t, qq s i| ≤ a * I := by
        rw [abs_mul, abs_of_nonneg (M.thetaN_nonneg n i)]
        exact mul_le_mul (hRates i).2.2.1 hrQ (abs_nonneg _) ha0
      have hin : |inputRate M n i * t| ≤ a * T := by
        rw [abs_mul, abs_of_nonneg ht.1]
        exact mul_le_mul (hRates i).2.2.2.1 ht.2 ht.1 ha0
      rw [hbalance t ht.1 i]
      calc
        _ ≤ |M.Xhat0 n X0 i + M.Ahat n ω t i -
            M.Rhat n ω (queueTime X Ψ ω i t / n) i - M.Shat n ω (busyTime Ψ ω i t / n) i +
            inputRate M n i * t - M.muN n i * (∫ s in (0 : ℝ)..t, pp s i)| +
            |M.thetaN n i * (∫ s in (0 : ℝ)..t, qq s i)| := abs_sub_le_add_abs _ _
        _ ≤ _ := by
          have h1 := abs_sub_le_add_abs
            (M.Xhat0 n X0 i + M.Ahat n ω t i -
              M.Rhat n ω (queueTime X Ψ ω i t / n) i - M.Shat n ω (busyTime Ψ ω i t / n) i +
                inputRate M n i * t) (M.muN n i * (∫ s in (0 : ℝ)..t, pp s i))
          have h2 := abs_add_le
            (M.Xhat0 n X0 i + M.Ahat n ω t i -
              M.Rhat n ω (queueTime X Ψ ω i t / n) i - M.Shat n ω (busyTime Ψ ω i t / n) i)
            (inputRate M n i * t)
          have h3 := abs_sub_le_add_abs
            (M.Xhat0 n X0 i + M.Ahat n ω t i - M.Rhat n ω (queueTime X Ψ ω i t / n) i)
            (M.Shat n ω (busyTime Ψ ω i t / n) i)
          have h4 := abs_sub_le_add_abs (M.Xhat0 n X0 i + M.Ahat n ω t i)
            (M.Rhat n ω (queueTime X Ψ ω i t / n) i)
          have h5 := abs_add_le (M.Xhat0 n X0 i) (M.Ahat n ω t i)
          linarith [h1, h2, h3, h4, h5, (hRates i).2.2.2.2.1]
    change g t ≤ A + C * I
    calc
      g t ≤ ∑ _i : Fin k, (a + 3 * B + a * T + (3 * a) * I) :=
        Finset.sum_le_sum (fun i _ => hcomp i)
      _ = (k : ℝ) * (a + 3 * B + a * T + (3 * a) * I) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ A + C * I := by dsimp [A, C]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  intro t ht
  have hnorm : ‖xx t‖ ≤ g t := (pi_norm_le_iff_of_nonneg (hg0 t)).2
    (fun i => by simpa only [Real.norm_eq_abs] using hgi t i)
  exact hnorm.trans ((integral_gronwall g T A C hT hC (fun s hs => hgi_int s hs.1) h_g t ht).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hC)) hA))

private theorem eventual_rate_bound {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x)) :
    ∃ a : ℝ, 1 ≤ a ∧ (∀ i, M.cU2 i ≤ a) ∧ ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      ∀ i, M.lamN n i ≤ a * n ∧ M.muN n i ≤ a ∧ M.thetaN n i ≤ a ∧
        |inputRate M n i| ≤ a ∧ |M.Xhat0 n (X0 n) i| ≤ a ∧ M.rho i ≤ a := by
  let b (i : Fin k) : ℝ := |M.lam i| + |M.mu i| + |M.theta i| +
    |M.ell i| + |x i| + |M.rho i| + M.cU2 i
  let a : ℝ := 1 + ∑ i, b i
  have hv (i : Fin k) : 0 ≤ M.cU2 i := variance_nonneg _ _
  have hb (i : Fin k) : 0 ≤ b i := by have := hv i; dsimp [b]; positivity
  have hsum0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hsum (i : Fin k) : b i < a := by
    have := Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
    dsimp [a]
    linarith
  have hsplit (i : Fin k) : M.lam i < a ∧ M.mu i < a ∧ M.theta i < a ∧
      |M.ell i| < a ∧ |x i| < a ∧ M.rho i < a ∧ M.cU2 i ≤ a := by
    have h := hsum i
    dsimp [b] at h
    have ha₁ := abs_nonneg (M.lam i)
    have ha₂ := abs_nonneg (M.mu i)
    have ha₃ := abs_nonneg (M.theta i)
    have ha₄ := abs_nonneg (M.ell i)
    have ha₅ := abs_nonneg (x i)
    have ha₆ := abs_nonneg (M.rho i)
    have ha₇ := hv i
    exact ⟨by linarith [le_abs_self (M.lam i)], by linarith [le_abs_self (M.mu i)],
      by linarith [le_abs_self (M.theta i)], by linarith, by linarith,
      by linarith [le_abs_self (M.rho i)], by linarith⟩
  refine ⟨a, ha, fun i => (hsplit i).2.2.2.2.2.2, ?_⟩
  have hN : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i,
      M.lamN n i ≤ a * n ∧ M.muN n i ≤ a ∧ M.thetaN n i ≤ a ∧
        |inputRate M n i| ≤ a ∧ |M.Xhat0 n (X0 n) i| ≤ a ∧ M.rho i ≤ a := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨hL, hM, hTh, hE, hX, hR, _⟩ := hsplit i
    have hE' := (inputRate_tendsto M i).abs
    have hX' : Tendsto (fun n => |M.Xhat0 n (X0 n) i|) atTop (𝓝 |x i|) :=
      (((continuous_apply i).tendsto x).comp hX0).abs
    filter_upwards [hN, (tendsto_order.1 (M.lam_lim i)).2 _ hL,
      (tendsto_order.1 (M.mu_lim i)).2 _ hM, (tendsto_order.1 (M.theta_lim i)).2 _ hTh,
      (tendsto_order.1 hE').2 _ hE, (tendsto_order.1 hX').2 _ hX] with n hn hL' hM' hTh' hE'' hX''
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact ⟨(div_le_iff₀ hn').1 hL'.le, hM'.le, hTh'.le, hE''.le, hX''.le, hR.le⟩
  exact hN.and hall

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hc : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hq : ∀ n, 1 ≤ n → ∀ ω t i, 0 ≤ t →
      X n ω t i - Ψ n ω t i ≤ max ((∑ j, X n ω t j) - n) 0)
    (T : ℝ) (hT : 0 ≤ T) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      M.P {ω | ∃ t ∈ Set.Icc 0 T, B < ‖M.Xhat n (X n) ω t‖} < η := by
  let : IsProbabilityMeasure M.P := M.isProb
  obtain ⟨a, ha, hva, harates⟩ := eventual_rate_bound M X0 x hX0
  have ha0 : 0 ≤ a := by linarith
  let H : ℝ := (a + 2 + a * T) * (T + 1)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let D : ℝ := (a * H + 3) * a + a * (H + 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpow : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have hsmall : Tendsto (fun r : ℝ => ENNReal.ofReal ((k : ℝ) * (3 * (D / r ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((hpow.const_div_atTop D).const_mul 3 |>.const_mul (k : ℝ))
  obtain ⟨R, hR, hRη⟩ : ∃ R : ℝ, 0 < R ∧
      ENNReal.ofReal ((k : ℝ) * (3 * (D / R ^ 2))) < η := by
    exact ((eventually_gt_atTop (0 : ℝ)).and ((tendsto_order.1 hsmall).2 _ hη)).exists
  let B : ℝ := R + a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  let L : ℝ := ((k : ℝ) * (a + 3 * B + a * T) + 1) * Real.exp (3 * a * (k : ℝ) * T)
  refine ⟨L, by dsimp [L]; positivity, ?_⟩
  filter_upwards [harates, (tendsto_atTop.1 hroot) B, (tendsto_atTop.1 hroot) a] with n hn hBn han
  let EA (i : Fin k) : Set Ω := {ω | ∃ t ∈ Set.Icc 0 H, B < |M.Ahat n ω t i|}
  let ES (i : Fin k) : Set Ω := {ω | ∃ t ∈ Set.Icc 0 H, B < |M.Shat n ω t i|}
  let ER (i : Fin k) : Set Ω := {ω | ∃ t ∈ Set.Icc 0 H, B < |M.Rhat n ω t i|}
  let F (i : Fin k) : Set Ω := EA i ∪ ES i ∪ ER i
  let q : ℝ := D / R ^ 2
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hA (i : Fin k) : M.P (EA i) ≤ ENNReal.ofReal q := by
    have hb : R + 1 ≤ B := add_le_add_right ha R
    have hRn : R ≤ Real.sqrt (n : ℝ) := (le_add_of_nonneg_right ha0).trans hBn
    calc
      M.P (EA i) ≤ M.P {ω | ∃ t ∈ Set.Icc 0 H, R + 1 < |M.Ahat n ω t i|} := by
        apply measure_mono
        rintro ω ⟨t, ht, h⟩
        exact ⟨t, ht, hb.trans_lt h⟩
      _ ≤ ENNReal.ofReal ((a * H + 3) * M.cU2 i / R ^ 2) :=
        renewal_scaled_bound M i n hn.1 a H R ha0 (hn.2 i).1 hH hR hRn
      _ ≤ ENNReal.ofReal q := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (sq_nonneg R)
        have h := mul_le_mul_of_nonneg_left (hva i) (by positivity : 0 ≤ a * H + 3)
        have h' : 0 ≤ a * (H + 2) := by positivity
        dsimp [D]
        linarith
  have hP : ENNReal.ofReal (a * (H + 2) / R ^ 2) ≤ ENNReal.ofReal q := by
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (sq_nonneg R)
    have h' : 0 ≤ (a * H + 3) * a := by positivity
    dsimp [D]
    linarith
  have hS (i : Fin k) : M.P (ES i) ≤ ENNReal.ofReal q :=
    (poisson_scaled_bound (M.S_poisson n i) n hn.1 a H R (hn.2 i).2.1 hH hR).trans hP
  have hR' (i : Fin k) : M.P (ER i) ≤ ENNReal.ofReal q :=
    (poisson_scaled_bound (M.R_poisson n i) n hn.1 a H R (hn.2 i).2.2.1 hH hR).trans hP
  have hF (i : Fin k) : M.P (F i) ≤ ENNReal.ofReal (3 * q) := by
    calc
      _ ≤ (M.P (EA i) + M.P (ES i)) + M.P (ER i) :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
      _ ≤ ENNReal.ofReal q + ENNReal.ofReal q + ENNReal.ofReal q :=
        add_le_add (add_le_add (hA i) (hS i)) (hR' i)
      _ = ENNReal.ofReal (3 * q) := by
        rw [← ENNReal.ofReal_add hq0 hq0, ← ENNReal.ofReal_add (add_nonneg hq0 hq0) hq0]
        congr 1
        ring
  calc
    _ ≤ M.P (⋃ i, F i) := by
      apply measure_mono
      intro ω hω
      by_contra hbad
      have hnoise (t : ℝ) (ht : t ∈ Set.Icc 0 H) (i : Fin k) :
          |M.Ahat n ω t i| ≤ B ∧ |M.Shat n ω t i| ≤ B ∧ |M.Rhat n ω t i| ≤ B := by
        have hi : ω ∉ F i := fun h => hbad (Set.mem_iUnion_of_mem i h)
        refine ⟨le_of_not_gt fun h => hi (Or.inl (Or.inl ⟨t, ht, h⟩)),
          le_of_not_gt fun h => hi (Or.inl (Or.inr ⟨t, ht, h⟩)),
          le_of_not_gt fun h => hi (Or.inr ⟨t, ht, h⟩)⟩
      obtain ⟨t, ht, h⟩ := hω
      exact (not_le_of_gt h) (pathwise_state_bound M n hn.1 (X0 n) (X n) (Ψ n)
        (hc n hn.1) (hq n hn.1) a B T ha hB hT han hBn hn.2 ω hnoise t ht)
    _ ≤ ∑ i, M.P (F i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin k, ENNReal.ofReal (3 * q) := Finset.sum_le_sum fun i _ => hF i
    _ = ENNReal.ofReal ((k : ℝ) * (3 * q)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
    _ < η := hRη
