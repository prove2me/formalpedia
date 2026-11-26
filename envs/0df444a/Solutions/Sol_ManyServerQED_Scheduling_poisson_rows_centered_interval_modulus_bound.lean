-- Prove2me | solution 1 for ManyServerQED.Scheduling.poisson_rows_centered_interval_modulus_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:49:41.469641+00:00
-- url     : https://prove2.me/submissions/2c5e5164-5efe-4329-bdbc-31e10aefd3a4

import Theorems.Thm_ManyServerQED_Scheduling_weak_continuous_path_laws_control_norm_and_modulus
import Theorems.Thm_ManyServerQED_Scheduling_poisson_polygonal_interpolation_uniform_error
import Theorems.Thm_ManyServerQED_Scheduling_centered_scaled_poisson_finite_dimensional_convergence
import Theorems.Thm_ManyServerQED_Scheduling_poisson_path_laws_with_matched_time_scales
import Theorems.Thm_ManyServerQED_Scheduling_brownian_weighted_finite_observation_law
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



open Set Finset
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


private theorem unit_poisson_increment_setup {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    (N₀ : Ω₀ → ℝ → ℝ) (hN₀ : IsPoissonProcess P₀ N₀ 1) :
    (∀ j : ℕ, IdentDistrib (fun ω => N₀ ω ((j:ℝ)+1) - N₀ ω j) (fun ω => N₀ ω 1) P₀ P₀) ∧
      Integrable (fun ω => (N₀ ω 1)^2) P₀ := by
  obtain ⟨_,hInc⟩ := iid_poisson_unit P₀ hN₀
  have hId (j : ℕ) : IdentDistrib (fun ω => N₀ ω ((j:ℝ)+1)-N₀ ω j)
      (fun ω => N₀ ω 1) P₀ P₀ := by
    have h := (hInc j).comp (measurable_id.add_const (1:ℝ))
    simpa only [Function.comp_def, id_eq,sub_add_cancel,Nat.cast_zero,zero_add,hN₀.zero,sub_zero] using h
  have hSq : Integrable (fun ω => (N₀ ω 1)^2) P₀ := by
    have h := (poisson_inc_moments hN₀ 0 1 (by norm_num) (by norm_num)).1
    simp only [hN₀.zero, sub_zero, one_mul] at h
    have hlp : MemLp (fun ω => N₀ ω 1) 2 P₀ := by
      convert h.add (memLp_const (1:ℝ)) using 1
      funext ω
      exact (sub_add_cancel (N₀ ω 1) 1).symm
    exact (memLp_two_iff_integrable_sq ((hN₀.meas 1).aestronglyMeasurable)).1 hlp
  exact ⟨hId,hSq⟩

private theorem approximate_path_modulus {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Q : ℕ → Ω → ℝ → ℝ) (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (hY : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (T c L : ℝ) (hL : 0 < L) (d : ℕ → ℝ → Set.Icc (0:ℝ) 1)
    (hD : ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, ∀ t ∈ Icc (0:ℝ) T,
      dist (d n s) (d n t) ≤ L* |s-t|)
    (hApprox : ∀ ε > (0:ℝ), Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
      ε ≤ |Q n ω t - c*Y n ω (d n t)|}) atTop (𝓝 0)) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | (∃ t ∈ Icc (0:ℝ) T, A ≤ |Q n ω t|) ∨
        ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
          ε ≤ |Q n ω s-Q n ω t|} ≤ ENNReal.ofReal η := by
  intro ε η hε hη
  let β := ε/3
  let ξ := β/(1+|c|)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  obtain ⟨A,hA,δ,hδ,hYevent⟩ := weak_continuous_path_laws_control_norm_and_modulus
    Y Z hY ξ (η/2) hξ (by positivity)
  let S (n : ℕ) := {ω | ∃ t ∈ Icc (0:ℝ) T, β ≤ |Q n ω t - c*Y n ω (d n t)|}
  let F (n : ℕ) := {ω | A ≤ ‖Y n ω‖ ∨ ∃ s t : Set.Icc (0:ℝ) 1,
    dist s t ≤ δ ∧ ξ ≤ |Y n ω s-Y n ω t|}
  have hSm : ∀ᶠ n in atTop, P (S n) ≤ ENNReal.ofReal (η/2) :=
    ((tendsto_order.1 (hApprox β hβ)).2 _ (ENNReal.ofReal_pos.2 (by positivity))).mono
      (fun _ h => h.le)
  refine ⟨ |c| *A+β,add_pos_of_nonneg_of_pos (mul_nonneg (abs_nonneg _) hA.le) hβ,
    δ/L,div_pos hδ hL,?_⟩
  filter_upwards [hD,hYevent,hSm] with n hd hf hs
  calc
    _ ≤ P (S n ∪ F n) := by
      apply measure_mono
      intro ω hω
      by_contra hBad
      have hS : ω ∉ S n := fun h => hBad (Or.inl h)
      have hF : ω ∉ F n := fun h => hBad (Or.inr h)
      have hSup : ‖Y n ω‖ < A := lt_of_not_ge (fun h => hF (Or.inl h))
      have herr (t : ℝ) (ht : t ∈ Icc 0 T) : |Q n ω t - c*Y n ω (d n t)| < β :=
        lt_of_not_ge (fun h => hS ⟨t,ht,h⟩)
      rcases hω with ⟨t,ht,htb⟩ | ⟨s,hs',t,ht,hst,hb⟩
      · have hval : |Y n ω (d n t)| ≤ A := by
          rw [← Real.norm_eq_abs]
          exact (ContinuousMap.norm_coe_le_norm _ _).trans hSup.le
        have hQ : |Q n ω t| ≤ |Q n ω t - c*Y n ω (d n t)| + |c*Y n ω (d n t)| := by
          simpa only [sub_add_cancel] using abs_add_le (Q n ω t - c*Y n ω (d n t)) (c*Y n ω (d n t))
        rw [abs_mul] at hQ
        linarith [herr t ht,mul_le_mul_of_nonneg_left hval (abs_nonneg c)]
      · have hu : dist (d n s) (d n t) ≤ δ :=
          (hd s hs' t ht).trans (by
            rw [mul_comm]
            exact (le_div_iff₀ hL).1 hst)
        have hwithin : |Y n ω (d n s)-Y n ω (d n t)| < ξ :=
          lt_of_not_ge (fun h => hF (Or.inr ⟨_,_,hu,h⟩))
        have hscaled : |c| * |Y n ω (d n s)-Y n ω (d n t)| ≤ β := by
          refine (mul_le_mul_of_nonneg_left hwithin.le (abs_nonneg c)).trans ?_
          have hEq : (1+|c|)*ξ = β := by dsimp [ξ]; field_simp
          nlinarith [hξ.le]
        have hQ : |Q n ω s-Q n ω t| ≤ |Q n ω s-c*Y n ω (d n s)| +
            |c| * |Y n ω (d n s)-Y n ω (d n t)| + |Q n ω t-c*Y n ω (d n t)| := by
          let u := Q n ω s-c*Y n ω (d n s)
          let v := c*(Y n ω (d n s)-Y n ω (d n t))
          let w := Q n ω t-c*Y n ω (d n t)
          have eq : Q n ω s-Q n ω t = u+v-w := by dsimp [u,v,w]; ring
          rw [eq]
          calc
            |u+v-w| ≤ |w|+|u+v| := by simpa only [add_comm] using abs_sub (u+v) w
            _ ≤ |w|+(|u|+|v|) := add_le_add_right (abs_add_le _ _) _
            _ = _ := by dsimp [u,v,w]; rw [abs_mul]; ring
        dsimp [β] at hscaled
        have h1 := herr s hs'
        have h2 := herr t ht
        dsimp [β] at h1 h2
        linarith only [h1,h2,hscaled,hQ,hb]
    _ ≤ P (S n) + P (F n) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) := add_le_add hs hf
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

private theorem rational_right_approximation {E : Type*} [PseudoMetricSpace E]
    {x : ℝ → E} {T : ℕ}
    (h : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt x (Ici s) s)
    {s e : ℝ} (hs : s ∈ Icc (0:ℝ) (T:ℝ)) (he : 0 < e) :
    ∃ q : ℚ, (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ dist (q:ℝ) s < e ∧ dist (x q) (x s) < e := by
  rcases hs.2.lt_or_eq with hst | hst
  · obtain ⟨d,hd,hD⟩ := Metric.continuousWithinAt_iff.1 (h s hs.1) e he
    have hm : s < min (T:ℝ) (s+min d e) := lt_min hst
      (lt_add_of_pos_right _ (lt_min hd he))
    obtain ⟨q,hq,hQ⟩ := exists_rat_btwn hm
    have hdQ : dist (q:ℝ) s < min d e := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.2 hq)]
      linarith [(lt_min_iff.1 hQ).2]
    exact ⟨q,⟨hs.1.trans hq.le,(lt_min_iff.1 hQ).1.le⟩,(lt_min_iff.1 hdQ).2,
      hD hq.le (lt_min_iff.1 hdQ).1⟩
  · have hu : ((T:ℚ):ℝ) = s := by simpa using hst.symm
    exact ⟨T,by rw [hu]; exact hs,by rw [hu,dist_self]; exact he,
      by rw [hu,dist_self]; exact he⟩

private theorem path_law_modulus_transfer {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {P' : Measure Ω'}
    (X : Ω → ℝ → E) (Y : Ω' → ℝ → E)
    (hLaw : IdentDistrib (fun ω (t : ℝ≥0) => X ω t) (fun ω (t : ℝ≥0) => Y ω t) P P')
    (hX : ∀ ω s, 0 ≤ s → ContinuousWithinAt (X ω) (Ici s) s)
    (T : ℕ) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ δ ∧ ε ≤ dist (X ω s) (X ω t)} ≤
    P' {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ 2*δ ∧ ε/2 ≤ dist (Y ω s) (Y ω t)} := by
  let B : Set (ℝ≥0 → E) := {f | ∃ (q r : ℚ), (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
    (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
    ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)}
  have hB : MeasurableSet B := by
    have he : B = ⋃ q : ℚ, ⋃ r : ℚ, {f | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
        (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
        ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)} := by ext; simp [B]
    rw [he]
    refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun r => ?_
    by_cases c : (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
        |(q:ℝ)-(r:ℝ)| < 2*δ
    · simpa only [c.1,c.2.1,c.2.2,true_and] using
        (measurableSet_lt (measurable_const (a := ε/2))
          ((measurable_pi_apply (q:ℝ).toNNReal).dist (measurable_pi_apply (r:ℝ).toNNReal)) :
          MeasurableSet {f : ℝ≥0 → E | ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)})
    · have hf : {f : ℝ≥0 → E | (q:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧
          (r:ℝ) ∈ Icc (0:ℝ) (T:ℝ) ∧ |(q:ℝ)-(r:ℝ)| < 2*δ ∧
          ε/2 < dist (f (q:ℝ).toNNReal) (f (r:ℝ).toNNReal)} = ∅ := by
        ext f
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => c ⟨h.1,h.2.1,h.2.2.1⟩
      rw [hf]
      exact MeasurableSet.empty
  let F (ω : Ω) (t : ℝ≥0) := X ω t
  let G (ω : Ω') (t : ℝ≥0) := Y ω t
  have hMeasure : P (F ⁻¹' B) = P' (G ⁻¹' B) := by
    rw [← Measure.map_apply_of_aemeasurable hLaw.aemeasurable_fst hB,
      ← Measure.map_apply_of_aemeasurable hLaw.aemeasurable_snd hB]
    exact congrArg (fun m : Measure (ℝ≥0 → E) => m B) hLaw.map_eq
  calc
    _ ≤ P (F ⁻¹' B) := by
      apply measure_mono
      rintro ω ⟨s,hs,t,ht,hst,hval⟩
      let e := min (δ/4) (ε/8)
      have he : 0 < e := lt_min (by positivity) (by positivity)
      obtain ⟨q,hq,hqs,hQ⟩ := rational_right_approximation (hX ω) hs he
      obtain ⟨r,hr,hrt,hR⟩ := rational_right_approximation (hX ω) ht he
      have hT : |(q:ℝ)-(r:ℝ)| < 2*δ := by
        have h1 := dist_triangle (q:ℝ) s (r:ℝ)
        have h2 := dist_triangle s t (r:ℝ)
        rw [dist_comm t (r:ℝ)] at h2
        rw [← Real.dist_eq] at hst ⊢
        have he' : e ≤ δ/4 := min_le_left _ _
        linarith only [h1,h2,hst,hqs,hrt,he',hδ]
      have hv : ε/2 < dist (X ω q) (X ω r) := by
        have h1 := dist_triangle (X ω s) (X ω q) (X ω t)
        have h2 := dist_triangle (X ω q) (X ω r) (X ω t)
        rw [dist_comm (X ω s) (X ω q)] at h1
        have he' : e ≤ ε/8 := min_le_right _ _
        linarith only [h1,h2,hval,hQ,hR,he',hε]
      refine ⟨q,r,hq,hr,hT,?_⟩
      simpa only [F,Real.coe_toNNReal _ hq.1,Real.coe_toNNReal _ hr.1] using hv
    _ = P' (G ⁻¹' B) := hMeasure
    _ ≤ _ := by
      apply measure_mono
      rintro ω ⟨q,r,hq,hr,hd,hv⟩
      refine ⟨q,hq,r,hr,hd.le,?_⟩
      simpa only [G,Real.coe_toNNReal _ hq.1,Real.coe_toNNReal _ hr.1] using hv.le

open BellWilliams2001.ThresholdPolicy
private theorem cadlag_rescale {x : ℝ → ℝ} (h : IsCadlag x) {c : ℝ} (hc : 0 < c) :
    IsCadlag (fun t => x (c*t)) := by
  have hmap : Continuous (fun t : ℝ => c*t) := continuous_const.mul continuous_id
  constructor
  · intro t ht
    refine (h.1 (c*t) (mul_nonneg hc.le ht)).comp hmap.continuousWithinAt ?_
    intro u hu
    exact mul_le_mul_of_nonneg_left hu hc.le
  · intro t ht
    obtain ⟨l,hl⟩ := h.2 (c*t) (mul_pos hc ht)
    refine ⟨l,hl.comp ?_⟩
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hmap.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (s := Iio t)] with u hu
      exact mul_lt_mul_of_pos_left hu hc


set_option maxHeartbeats 1600000 in
theorem solution {Ω Ω₀ Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Ω']
    {P : Measure Ω} {P₀ : Measure Ω₀} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P₀] [IsProbabilityMeasure P']
    (N : ℕ → Ω → ℝ → ℝ) (aN : ℕ → ℝ) (hN : ∀ n, IsPoissonProcess P (N n) (aN n))
    (a : ℝ) (ha : 0 ≤ a) (hconv : Tendsto aN atTop (𝓝 a))
    (N₀ : Ω₀ → ℝ → ℝ) (hN₀ : IsPoissonProcess P₀ N₀ 1)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let Q (n : ℕ) (ω : Ω) (t : ℝ) :=
      (N n ω ((n:ℝ)*t) - (n:ℝ)*aN n*t)/Real.sqrt n
    ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          ε ≤ |Q n ω s - Q n ω t|} ≤ ENNReal.ofReal η := by
  intro Q
  have haN (n : ℕ) : 0 ≤ aN n := (hN n).rate_nonneg
  obtain ⟨J,hJ⟩ := exists_nat_gt ((a+1)*((T:ℝ)+1))
  have hJ0 : 0 < (J:ℝ) := (by positivity : 0 < (a+1)*((T:ℝ)+1)).trans hJ
  have hJn : 1 ≤ J := by exact_mod_cast hJ0
  obtain ⟨hId,hSq⟩ := unit_poisson_increment_setup N₀ hN₀
  let r (n : ℕ) := J*n
  have hr : Tendsto r atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ J*n
    simpa only [one_mul] using Nat.mul_le_mul_right n hJn
  let y (j : ℕ) (ω : Ω₀) := N₀ ω ((j:ℝ)+1) - N₀ ω j - 1
  let Y n := walkPath y (r n)
  let d (n : ℕ) (t : ℝ) := aN n*t/(J:ℝ)
  let cl (n : ℕ) (t : ℝ) := projIcc 0 1 zero_le_one (d n t)
  let L := (a+1)/(J:ℝ)
  let c := Real.sqrt (J:ℝ)
  let Z (n : ℕ) (ω : Ω₀) (t : ℝ) :=
    (N₀ ω ((n:ℝ)*aN n*t) - (n:ℝ)*aN n*t)/Real.sqrt n
  have hc : 0 < c := Real.sqrt_pos.2 hJ0
  have hL : 0 < L := div_pos (by linarith) hJ0
  have hDon := poisson_integer_grid_donsker N₀ hN₀ hB hBc
  have hY : TendstoInDistribution Y atTop (brownianPath B) (fun _ => P₀) P' :=
    ⟨fun n => hDon.forall_aemeasurable (r n),hDon.aemeasurable_limit,hDon.tendsto.comp hr⟩
  have hA' : ∀ᶠ n in atTop, aN n ≤ a+1 :=
    ((tendsto_order.1 hconv).2 _ (show a < a+1 by linarith)).mono (fun _ h => h.le)
  have hC (n : ℕ) (hn : aN n ≤ a+1) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T:ℝ)) :
      d n t ∈ Icc (0:ℝ) 1 := by
    have hB := mul_le_mul hn ht.2 ht.1 (by linarith : 0 ≤ a+1)
    exact ⟨div_nonneg (mul_nonneg (haN n) ht.1) hJ0.le,(div_le_one hJ0).2 (by linarith)⟩
  have hProj (n : ℕ) (hn : aN n ≤ a+1) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T:ℝ)) :
      (cl n t : ℝ) = d n t := by
    have h := hC n hn t ht
    simp [cl,projIcc,max_eq_right h.1,min_eq_right h.2]
  have hCl : ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) (T:ℝ), ∀ t ∈ Icc (0:ℝ) (T:ℝ),
      dist (cl n s) (cl n t) ≤ L*|s-t| := by
    filter_upwards [hA'] with n hn
    intro s hs t ht
    rw [Subtype.dist_eq,Real.dist_eq,hProj n hn s hs,hProj n hn t ht,
      show d n s - d n t = (aN n/(J:ℝ))*(s-t) by dsimp [d]; ring,
      abs_mul, abs_of_nonneg (div_nonneg (haN n) hJ0.le)]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn hJ0.le) (abs_nonneg _)
  have hApprox (e : ℝ) (he : 0 < e) : Tendsto (fun n => P₀ {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      e ≤ |Z n ω t-c*Y n ω (cl n t)|}) atTop (𝓝 0) := by
    have h := poisson_polygonal_interpolation_uniform_error P₀ N₀
      hN₀.mono hN₀.zero hN₀.meas hId hSq (e/c) (div_pos he hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h.comp hr)
      (Eventually.of_forall (fun _ => zero_le)) ?_
    filter_upwards [hA',eventually_ge_atTop (1:ℕ)] with n hn hn0
    apply measure_mono
    rintro ω ⟨t,ht,hbad⟩
    refine ⟨d n t,hC n hn t ht,?_⟩
    have hTime : ((r n:ℕ):ℝ)*d n t = (n:ℝ)*aN n*t := by dsimp [r,d]; push_cast; field_simp
    have hSn : Real.sqrt ((r n:ℕ):ℝ) = c*Real.sqrt n := by
      simp [r,c,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg J)]
    have hi : c*Y n ω (cl n t) = c*(walkInterp y (r n) ω ((r n:ℕ)*d n t) / Real.sqrt ((r n:ℕ):ℝ)) := by
      change c*(walkInterp y (r n) ω ((r n:ℕ)*(cl n t:ℝ))/Real.sqrt ((r n:ℕ):ℝ)) = _
      rw [hProj n hn t ht]
    have hz : Z n ω t = c*((N₀ ω ((r n:ℕ)*d n t)-(r n:ℕ)*d n t)/Real.sqrt ((r n:ℕ):ℝ)) := by
      rw [hTime,hSn]
      unfold Z
      field_simp [hc.ne',(Real.sqrt_pos.2 (by exact_mod_cast hn0 : (0:ℝ) < n)).ne']
    rw [hi,hz,← mul_sub,abs_mul,abs_of_pos hc] at hbad
    exact (div_le_iff₀ hc).2 (by rwa [mul_comm])
  obtain ⟨A,hA,δ,hδ,hMod⟩ := approximate_path_modulus Z Y (brownianPath B)
    hY T c L hL cl hCl hApprox (ε/2) η (by positivity) hη
  refine ⟨δ/2,by positivity,?_⟩
  filter_upwards [hMod,eventually_ge_atTop (1:ℕ)] with n hn hn0
  have hPath : IdentDistrib (fun ω (t : ℝ≥0) => Q n ω t)
      (fun ω (t : ℝ≥0) => Z n ω t) P P₀ := by
    let F (x : ℝ≥0 → ℝ) (t : ℝ≥0) := (x t-(n:ℝ)*aN n*t)/Real.sqrt n
    have hmF : Measurable F := measurable_pi_lambda _ (fun t =>
      ((measurable_pi_apply t).sub_const _).div_const _)
    have he : aN n*(n:ℝ) = 1*((n:ℝ)*aN n) := by ring
    have h := (poisson_path_laws_with_matched_time_scales (N n) N₀ (aN n) 1 (n:ℝ)
      ((n:ℝ)*aN n) (hN n) hN₀ (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (haN n)) he).comp hmF
    simpa only [Function.comp_def,F,Q,Z] using h
  have hQ (ω : Ω) (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (Q n ω) (Ici t) t := by
    have hnR : (0:ℝ) < n := by exact_mod_cast hn0
    have hh : ContinuousWithinAt (fun s => N n ω ((n:ℝ)*s)) (Ici t) t :=
      (cadlag_rescale ((hN n).cadlag ω) hnR).1 t ht
    exact (hh.sub (((continuous_const.mul continuous_id).continuousWithinAt :
      ContinuousWithinAt (fun s : ℝ => ((n:ℝ)*aN n)*s) (Ici t) t))).div_const _
  have h := path_law_modulus_transfer (Q n) (Z n) hPath hQ T (δ/2) ε (by positivity) hε
  simp only [Real.dist_eq,show 2*(δ/2) = δ by ring] at h
  exact h.trans ((measure_mono (fun _ hs => Or.inr hs)).trans hn)
