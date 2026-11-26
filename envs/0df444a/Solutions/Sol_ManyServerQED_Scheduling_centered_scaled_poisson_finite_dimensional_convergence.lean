-- Prove2me | solution 1 for ManyServerQED.Scheduling.centered_scaled_poisson_finite_dimensional_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:12:11.029429+00:00
-- url     : https://prove2.me/submissions/bbe29e9d-7697-474e-93b6-b574e46fbdbe

import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_centered_count_variance_hasSum
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling DurrettProbability

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

private theorem iid_poisson_unit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N : Ω → ℝ → ℝ} (hN : IsPoissonProcess P N 1) :
    let Y (j : ℕ) (ω : Ω) := N ω ((j:ℝ)+1) - N ω j - 1
    iIndepFun Y P ∧ ∀ j, IdentDistrib (Y j) (Y 0) P P := by
  let Y (j : ℕ) (ω : Ω) := N ω ((j:ℝ)+1) - N ω j - 1
  have hy (j : ℕ) : Measurable (Y j) := ((hN.meas _).sub (hN.meas _)).sub_const _
  constructor
  · apply iIndepFun_iff_finset.mpr
    intro s
    let m := s.sup id + 1
    let τ (j : Fin (m+1)) : ℝ := (j:ℕ)
    have he : Monotone τ := fun j l hjl => by
      unfold τ
      exact_mod_cast (show j.val ≤ l.val from hjl)
    have hin := hN.indep_incr m τ (by dsimp [τ]; positivity) he
    let g (j : s) : Fin m := ⟨j, Nat.lt_succ_of_le (Finset.le_sup (f := id) j.2)⟩
    have hg : Function.Injective g := fun j l h => Subtype.ext (congrArg Fin.val h)
    have h' := (hin.precomp hg).comp (fun _ (z : ℝ) => z-1)
      (fun _ => measurable_id.sub_const _)
    convert h' using 1
    funext j ω
    simp [Y, g, τ, Finset.restrict]
  · have hmap (j : ℕ) :
        Measure.map (Y j) P = (poissonMeasure 1).map (fun z : ℕ => (z:ℝ)-1) := by
      let F (ω : Ω) : ℕ := ⌊N ω ((j:ℝ)+1) - N ω j⌋₊
      have hF : Measurable F := ((hN.meas _).sub (hN.meas _)).nat_floor
      have hcast (ω : Ω) : (F ω : ℝ) = N ω ((j:ℝ)+1) - N ω j := by
        obtain ⟨p,hp⟩ := hN.nat_valued ω j (by positivity)
        obtain ⟨q,hq⟩ := hN.nat_valued ω ((j:ℝ)+1) (by positivity)
        have hpq : p ≤ q := by
          have hh := hN.mono ω (Set.mem_Ici.2 (by positivity : (0:ℝ) ≤ (j:ℝ)))
            (Set.mem_Ici.2 (by positivity : (0:ℝ) ≤ (j:ℝ)+1)) (by linarith)
          rw [hp,hq] at hh
          exact_mod_cast hh
        have hh : N ω ((j:ℝ)+1) - N ω j = (q-p:ℕ) := by
          rw [hp,hq,Nat.cast_sub hpq]
        simp [F, hh]
      have hFmap : Measure.map F P = poissonMeasure 1 := by
        apply Measure.ext_of_singleton
        intro l
        rw [Measure.map_apply hF (measurableSet_singleton l)]
        have hh := hN.law (j:ℝ) ((j:ℝ)+1) (by positivity) (by linarith) l
        simp only [add_sub_cancel_left, mul_one, Real.toNNReal_one] at hh
        convert hh using 2
        ext ω
        change F ω = l ↔ N ω ((j:ℝ)+1) - N ω j = (l:ℝ)
        rw [← hcast]
        exact Nat.cast_inj.symm
      rw [← hFmap, Measure.map_map (Measurable.of_discrete) hF]
      congr 1
      funext ω
      simp [Y,hcast]
    exact fun j => ⟨(hy j).aemeasurable, (hy 0).aemeasurable, (hmap j).trans (hmap 0).symm⟩

private theorem poisson_integer_grid_donsker {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℝ → ℝ) (hN : IsPoissonProcess P N 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution
      (fun n : ℕ => walkPath (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n)
      atTop (brownianPath B) (fun _ => P) P' := by
  let Y (j : ℕ) (ω : Ω) := N ω ((j:ℝ)+1) - N ω j - 1
  have hY (j : ℕ) : Measurable (Y j) := ((hN.meas _).sub (hN.meas _)).sub_const _
  obtain ⟨hi,hid⟩ := iid_poisson_unit P hN
  obtain ⟨hLp, hm, hv⟩ := poisson_inc_moments hN 0 1 (by norm_num) (by norm_num)
  have hq : (fun ω => N ω 1 - N ω 0 - 1 * (1-0)) = Y 0 := by funext ω; norm_num [Y]
  dsimp only at hLp hm hv
  rw [hq] at hLp hm hv
  have hSq : Integrable (fun ω => Y 0 ω ^ 2) P :=
    (memLp_two_iff_integrable_sq (hY 0).aestronglyMeasurable).mp hLp
  have hVar : (∫ ω, Y 0 ω ^ 2 ∂P) = 1 := by
    rw [variance_eq_integral (hY 0).aemeasurable, hm] at hv
    simpa using hv
  exact donsker hY hi hid hSq hm hVar hB hBc

open Set Finset
private theorem interp_segment (N : ℝ → ℝ) {n j : ℕ} (hj : j < n) {u : ℝ}
    (hu : u ∈ Icc (j:ℝ) ((j:ℝ)+1)) :
    walkInterp (Ω := Unit) (fun l _ => N ((l:ℝ)+1) - N l - 1) n () u =
      (N j - N 0 - j) + (N ((j:ℝ)+1) - N j - 1) * (u-j) := by
  let a (l : ℕ) := N ((l:ℝ)+1) - N l - 1
  let c (l : ℕ) := max 0 (min 1 (u - (l:ℝ)))
  have hC (l : ℕ) (hl : l < j) : c l = 1 := by
    have hl' : (l:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hl
    have hh : 1 ≤ u - (l:ℝ) := by linarith [hu.1]
    simp [c, min_eq_left hh]
  have hJ : c j = u-j := by
    have h0 : 0 ≤ u-(j:ℝ) := sub_nonneg.mpr hu.1
    have h1 : u-(j:ℝ) ≤ 1 := by linarith [hu.2]
    simp [c, min_eq_right h1, max_eq_right h0]
  have hZ (l : ℕ) (hl : j+1 ≤ l) : c l = 0 := by
    have hl' : (j:ℝ)+1 ≤ l := by exact_mod_cast hl
    have hh : u-(l:ℝ) ≤ 0 := by linarith [hu.2]
    have hh' : u-(l:ℝ) ≤ 1 := by linarith
    simp [c, min_eq_right hh', max_eq_left hh]
  have ht (m : ℕ) : ∑ l ∈ range m, a l = N m - N 0 - m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      unfold a
      ring
  change (∑ l ∈ range n, a l * c l) = _
  have hp := sum_range_add_sum_Ico (fun l => a l * c l) (Nat.succ_le_of_lt hj)
  rw [← hp]
  have hz : (∑ l ∈ Finset.Ico (j+1) n, a l * c l) = 0 :=
    Finset.sum_eq_zero (fun l hl => by rw [hZ l (mem_Ico.1 hl).1,mul_zero])
  rw [hz, add_zero, sum_range_succ,hJ]
  have he : ∑ l ∈ range j, a l * c l = ∑ l ∈ range j, a l :=
    Finset.sum_congr rfl (fun l hl => by rw [hC l (mem_range.1 hl),mul_one])
  rw [he, ht]

private theorem interpolation_bound (N : ℝ → ℝ) (hmono : MonotoneOn N (Ici 0)) (h0 : N 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : u ∈ Icc (0:ℝ) (n:ℝ)) :
    ∃ j < n, |(N u - u) -
      walkInterp (Ω := Unit) (fun l _ => N ((l:ℝ)+1) - N l - 1) n () u| ≤
        N ((j:ℝ)+1) - N j := by
  have hbr : ∃ j < n, u ∈ Icc (j:ℝ) ((j:ℝ)+1) := by
    rcases (mem_Icc.1 hu).2.lt_or_eq with hlt | heq
    · let j := ⌊u⌋₊
      have hj : j < n := Nat.floor_lt (by exact hu.1) |>.2 hlt
      exact ⟨j,hj,Nat.floor_le hu.1,(Nat.lt_floor_add_one u).le⟩
    · have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hEq : ((n-1:ℕ):ℝ)+1 = n := by rw [Nat.cast_sub hn]; simp
      refine ⟨n-1,by omega,?_⟩
      rw [heq,hEq]
      exact ⟨by linarith,rfl.le⟩
  obtain ⟨j,hj,hu'⟩ := hbr
  refine ⟨j,hj,?_⟩
  rw [interp_segment N hj hu']
  have hleft : N j ≤ N u := hmono (mem_Ici.2 (by positivity)) (mem_Ici.2 hu.1) hu'.1
  have hright : N u ≤ N ((j:ℝ)+1) := hmono (mem_Ici.2 hu.1) (mem_Ici.2 (by positivity)) hu'.2
  have hm : 0 ≤ N ((j:ℝ)+1)-N j := sub_nonneg.mpr (hleft.trans hright)
  have hp : 0 ≤ u-j := sub_nonneg.mpr hu'.1
  have hp' : u-j ≤ (1:ℝ) := by linarith [hu'.2]
  have hl : N j ≤ N j + (N ((j:ℝ)+1)-N j)*(u-j) := le_add_of_nonneg_right (mul_nonneg hm hp)
  have hr : N j + (N ((j:ℝ)+1)-N j)*(u-j) ≤ N ((j:ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_left hp' hm
    linarith
  rw [h0]
  apply abs_le.mpr
  constructor <;> nlinarith

open scoped ENNReal

private theorem square_tail_small {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hXm : Measurable X) (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n:ℝ≥0∞) * P {ω | ε * Real.sqrt n ≤ X ω}) atTop (𝓝 0) := by
  let S (n : ℕ) : Set Ω := {ω | ε*Real.sqrt n ≤ X ω}
  let f (n : ℕ) (ω : Ω) := Set.indicator (S n) (fun ω => ENNReal.ofReal (X ω^2)) ω
  let e : ℝ≥0∞ := ENNReal.ofReal (ε^2)
  have hm (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hXm
  have hXsq : Measurable (fun ω => ENNReal.ofReal (X ω^2)) := (hXm.pow_const _).ennreal_ofReal
  have hXle : (∫⁻ ω, ENNReal.ofReal (X ω^2) ∂P) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hX2.hasFiniteIntegral).ne
  have hfs : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    apply ae_of_all
    intro ω
    have h := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_atTop.1 h) (X ω/ε + 1)] with n hn
    have h' : X ω < ε*Real.sqrt n := by
      change X ω/ε+1 ≤ Real.sqrt (n:ℝ) at hn
      have hh := mul_le_mul_of_nonneg_left hn hε.le
      rw [mul_add, mul_one, mul_div_cancel₀ _ hε.ne'] at hh
      linarith
    have hnot : ω ∉ S n := not_le_of_gt h'
    exact (Set.indicator_of_notMem hnot _).symm
  have ht := tendsto_lintegral_of_dominated_convergence (fun ω => ENNReal.ofReal (X ω^2))
    (fun n => hXsq.indicator (hm n)) (fun n => ae_of_all _ (fun ω => by
      by_cases hw : ω ∈ S n <;> simp [f,hw]))
    hXle hfs
  simp only [lintegral_zero] at ht
  have he0 : e ≠ 0 := by dsimp [e]; exact (ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)).ne'
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB (n : ℕ) : e * ((n:ℝ≥0∞) * P (S n)) ≤ ∫⁻ ω, f n ω ∂P := by
    rw [← mul_assoc, ← lintegral_indicator_const (hm n)]
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ S n
    · simp only [f, Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hh : ε * Real.sqrt n ≤ X ω := hω
      calc
        _ = (ε * Real.sqrt n)^2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        _ ≤ _ := by gcongr <;> positivity
    · simp [f,hω]
  have hBn (n : ℕ) : (n:ℝ≥0∞) * P (S n) ≤ e⁻¹ * ∫⁻ ω, f n ω ∂P := by
    have h := mul_le_mul_right (hB n) e⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel he0 heT, one_mul] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hBn
  have hei : e⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 he0
  simpa only [mul_zero] using (ENNReal.Tendsto.const_mul (a := e⁻¹) ht (Or.inr hei))

private theorem interpolation_uniform_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → ℝ → ℝ) (hN : ∀ ω, MonotoneOn (N ω) (Ici 0)) (h0 : ∀ ω, N ω 0 = 0)
    (hM : ∀ t, Measurable (fun ω => N ω t))
    (hid : ∀ j : ℕ, IdentDistrib (fun ω => N ω ((j:ℝ)+1) - N ω j) (fun ω => N ω 1) P P)
    (h2 : Integrable (fun ω => (N ω 1)^2) P) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω |
      ∃ t ∈ Icc (0:ℝ) 1,
        ε ≤ |(N ω ((n:ℝ)*t) - (n:ℝ)*t)/Real.sqrt n -
          walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t)/Real.sqrt n|})
      atTop (𝓝 0) := by
  intro ε hε
  let b (n : ℕ) := (n:ℝ≥0∞) * P {ω | ε*Real.sqrt n ≤ N ω 1}
  have hb := square_tail_small P (fun ω => N ω 1) (hM 1) h2 ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  let E (j : Fin n) := {ω | ε*Real.sqrt n ≤ N ω ((j:ℝ)+1) - N ω j}
  have hsub : {ω | ∃ t ∈ Icc (0:ℝ) 1,
        ε ≤ |(N ω ((n:ℝ)*t) - (n:ℝ)*t)/Real.sqrt n -
          walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t)/Real.sqrt n|}
        ⊆ ⋃ j, E j := by
    rintro ω ⟨t,ht,hω⟩
    have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hu : (n:ℝ)*t ∈ Icc (0:ℝ) n := by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) ht.1, ?_⟩
      simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n)
    obtain ⟨j,hj,hjB⟩ := interpolation_bound (N ω) (hN ω) (h0 ω) n hn _ hu
    have hX : walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t) =
      walkInterp (Ω := Unit) (fun j _ => N ω ((j:ℝ)+1)-N ω j-1) n () ((n:ℝ)*t) := rfl
    rw [← sub_div, abs_div, abs_of_pos hs, hX, le_div_iff₀ hs] at hω
    exact mem_iUnion.2 ⟨⟨j,hj⟩,hω.trans hjB⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le E).trans_eq ?_)
  have hEq (j : Fin n) : P (E j) = P {ω | ε*Real.sqrt n ≤ N ω 1} := by
    exact (hid j).measure_mem_eq (measurableSet_Ici (a := ε*Real.sqrt n))
  simp [hEq,b,nsmul_eq_mul]

open ManyServerQED.Scheduling

set_option maxHeartbeats 1200000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (N : Ω → ℝ → ℝ) (hN : IsPoissonProcess P N 1)
    (hId : ∀ j : ℕ, IdentDistrib (fun ω => N ω ((j:ℝ)+1) - N ω j) (fun ω => N ω 1) P P)
    (hSq : Integrable (fun ω => (N ω 1)^2) P)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (a : ℝ) (ha : 0 ≤ a)
    (haL : Tendsto aN atTop (𝓝 a))
    (T : ℝ) (hT : 0 ≤ T) (J : ℕ) (hJ : (a+1)*(T+1) < J)
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ i, τ i ∈ Icc (0:ℝ) T)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω i => (N ω ((n:ℝ)*aN n*τ i) - (n:ℝ)*aN n*τ i)/Real.sqrt n)
      atTop (fun ω i => Real.sqrt (J:ℝ) * B ((a*τ i/(J:ℝ)).toNNReal) ω) (fun _ => P) P' := by
  let y (j : ℕ) (ω : Ω) := N ω ((j:ℝ)+1) - N ω j - 1
  let d (n : ℕ) (i : Fin m) := aN n * τ i / (J:ℝ)
  let e (i : Fin m) := a * τ i / (J:ℝ)
  have hJ0 : (0:ℝ) < J := lt_trans (by positivity) hJ
  have hJNat : 0 < J := by exact_mod_cast hJ0
  let r (n : ℕ) := J*n
  have hr : Tendsto r atTop atTop := by
    have hr1 (n : ℕ) : 1*n ≤ r n := Nat.mul_le_mul_right n hJNat
    simp only [one_mul] at hr1
    exact tendsto_atTop_mono hr1 tendsto_id
  have hd : Tendsto d atTop (𝓝 e) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (haL.mul tendsto_const_nhds).div_const _
  have H : ∀ᶠ n in atTop, ∀ i, d n i ∈ Icc (0:ℝ) 1 := by
    filter_upwards [(tendsto_order.1 haL).2 (a+1) (by linarith)] with n hn
    intro i
    refine ⟨div_nonneg (mul_nonneg (haN n) (hτ i).1) hJ0.le, (div_le_one hJ0).2 ?_⟩
    exact ((mul_le_mul hn.le (hτ i).2 (hτ i).1 (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity : 0 ≤ a+1))).trans hJ.le
  have hE (i : Fin m) : e i ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg (mul_nonneg ha (hτ i).1) hJ0.le, (div_le_one hJ0).2 ?_⟩
    exact ((mul_le_mul (show a ≤ a+1 by linarith) (hτ i).2 (hτ i).1 (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity : 0 ≤ a+1))).trans hJ.le
  have hdIn : TendstoInMeasure P (fun n (_ : Ω) => d n) atTop (fun _ => e) := by
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ (fun _ => hd))
  have hDon := poisson_integer_grid_donsker N hN hB hBc
  have hWalk : TendstoInDistribution (fun n => walkPath y (r n)) atTop (brownianPath B) (fun _ => P) P' :=
    ⟨fun n => hDon.forall_aemeasurable (r n),hDon.aemeasurable_limit,hDon.tendsto.comp hr⟩
  let f (z : PathSpace × (Fin m → ℝ)) (i : Fin m) :=
    Real.sqrt (J:ℝ) * z.1 (Set.projIcc 0 1 zero_le_one (z.2 i))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    apply Continuous.const_mul
    have hg : Continuous (fun z : PathSpace × (Fin m → ℝ) =>
        Set.projIcc (0:ℝ) 1 zero_le_one (z.2 i)) :=
      continuous_projIcc.comp ((continuous_apply i).comp continuous_snd)
    exact continuous_eval.comp (continuous_fst.prodMk hg)
  let I (n : ℕ) (ω : Ω) := f (walkPath y (r n) ω,d n)
  let Q (n : ℕ) (ω : Ω) (i : Fin m) :=
    (N ω ((n:ℝ)*aN n*τ i) - (n:ℝ)*aN n*τ i)/Real.sqrt n
  let Z (ω : Ω') (i : Fin m) := Real.sqrt (J:ℝ) * B ((e i).toNNReal) ω
  have hproj (v : ℝ) (hv : v ∈ Icc (0:ℝ) 1) :
      ((Set.projIcc 0 1 zero_le_one v : Icc (0:ℝ) 1) : ℝ) = v := by
    simp [Set.projIcc, max_eq_right hv.1, min_eq_right hv.2]
  have hIZ : TendstoInDistribution I atTop Z (fun _ => P) P' := by
    have hp := hWalk.continuous_comp_prodMk_of_tendstoInMeasure_const hf hdIn
      (fun _ => measurable_const.aemeasurable)
    refine hp.congr (fun _ => EventuallyEq.rfl) (Eventually.of_forall (fun ω => ?_))
    funext i
    change Real.sqrt (J:ℝ) * brownianPath B ω (Set.projIcc 0 1 zero_le_one (e i)) = _
    have hp0 : (((Set.projIcc 0 1 zero_le_one (e i) : Icc (0:ℝ) 1) : ℝ).toNNReal) =
        (e i).toNNReal := congrArg Real.toNNReal (hproj (e i) (hE i))
    unfold brownianPath toPath
    simp only [hBc ω, dite_true, ContinuousMap.coe_mk]
    apply congrArg (fun t : ℝ≥0 => Real.sqrt (J:ℝ) * B t ω)
    apply Subtype.ext
    exact (hproj (e i) (hE i)).trans (Real.coe_toNNReal _ (hE i).1).symm
  have hQ (n : ℕ) : AEMeasurable (Q n) P := by
    apply aemeasurable_pi_lambda
    intro i
    exact (((hN.meas _).sub_const _).div_const _).aemeasurable
  have hInterpolation := interpolation_uniform_error P N hN.mono hN.zero hN.meas hId hSq
  refine tendstoInDistribution_of_tendstoInMeasure_sub Q Z hIZ ?_ hQ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let c := Real.sqrt (J:ℝ)
  have hc : 0 < c := Real.sqrt_pos.2 hJ0
  have hProb := (hInterpolation (ε/c) (div_pos hε hc)).comp hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hProb
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [H,eventually_ge_atTop (1:ℕ)] with n hdN hn
  apply measure_mono
  intro ω hω
  have hnot : ¬∀ i, ‖Q n ω i - I n ω i‖ < ε := by
    intro hh
    have he : ‖(Q - I) n ω - (0 : Ω → Fin m → ℝ) ω‖ < ε := by
      apply (pi_norm_lt_iff hε).2
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero] using hh
    exact (not_le_of_gt he) hω
  push Not at hnot
  obtain ⟨i,hi⟩ := hnot
  refine ⟨d n i, hdN i, ?_⟩
  have hScale : ((r n:ℕ):ℝ)*d n i = (n:ℝ)*aN n*τ i := by
    dsimp [r,d]
    push_cast
    field_simp
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hS : Real.sqrt ((r n:ℕ):ℝ) = c*Real.sqrt n := by simp [r,c,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg J)]
  have hIeq : I n ω i = c * (walkInterp y (r n) ω ((r n:ℕ)*d n i) / Real.sqrt ((r n:ℕ):ℝ)) := by
    change c * (walkInterp y (r n) ω ((r n:ℕ) *
      ((Set.projIcc 0 1 zero_le_one (d n i) : Icc (0:ℝ) 1) : ℝ)) / Real.sqrt ((r n:ℕ):ℝ)) = _
    rw [hproj _ (hdN i)]
  have hQeq : Q n ω i = c * ((N ω ((r n:ℕ)*d n i) - (r n:ℕ)*d n i) / Real.sqrt ((r n:ℕ):ℝ)) := by
    rw [hScale,hS]
    unfold Q
    field_simp [(Real.sqrt_pos.2 hnR).ne',hc.ne']
  change ε / c ≤ |(N ω ((r n:ℕ)*d n i) - (r n:ℕ)*d n i)/Real.sqrt ((r n:ℕ):ℝ) -
    walkInterp y (r n) ω ((r n:ℕ)*d n i)/Real.sqrt ((r n:ℕ):ℝ)|
  rw [hQeq,hIeq,← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_pos hc] at hi
  exact (div_le_iff₀ hc).2 (by rwa [mul_comm])
