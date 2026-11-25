-- Prove2me | solution 1 for ManyServerQED.Scheduling.poisson_integer_grid_donsker
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T21:10:13.538247+00:00
-- url     : https://prove2.me/submissions/eb4d06f7-ea48-43a1-b7f7-f06b24c8fc2b

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

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
