-- Prove2me | solution 1 for ManyServerQED.Scheduling.poisson_rows_centered_finite_observation_limit
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:40:34.200746+00:00
-- url     : https://prove2.me/submissions/60d5d0c5-817e-4b69-9dd2-2489491d212f

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

set_option maxHeartbeats 1600000 in
theorem solution {Ω Ω₀ Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace Ω']
    {P : Measure Ω} {P₀ : Measure Ω₀} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P₀] [IsProbabilityMeasure P']
    (N : ℕ → Ω → ℝ → ℝ) (aN : ℕ → ℝ) (hN : ∀ n, IsPoissonProcess P (N n) (aN n))
    (a : ℝ) (ha : 0 ≤ a) (hconv : Tendsto aN atTop (𝓝 a))
    (N₀ : Ω₀ → ℝ → ℝ) (hN₀ : IsPoissonProcess P₀ N₀ 1)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
    TendstoInDistribution
      (fun (n : ℕ) ω j => (N n ω ((n:ℝ)*τ j) - (n:ℝ)*aN n*τ j)/Real.sqrt n)
      atTop (fun ω j => Real.sqrt a*B (τ j).toNNReal ω) (fun _ => P) P' := by
  have haN (n : ℕ) : 0 ≤ aN n := (hN n).rate_nonneg
  obtain ⟨T,hT,hτT⟩ : ∃ T : ℝ, 0 ≤ T ∧ ∀ j, τ j ≤ T := by
    let T := ∑ j, max (τ j) 0
    exact ⟨T,Finset.sum_nonneg (fun _ _ => le_max_right _ _),fun j =>
      (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (τ j) 0)
        (fun _ _ => le_max_right _ _) (Finset.mem_univ _))⟩
  obtain ⟨J,hJ⟩ := exists_nat_gt ((a+1)*(T+1))
  have hJ0 : 0 < (J:ℝ) := (by positivity : 0 < (a+1)*(T+1)).trans hJ
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
  let Z (n : ℕ) (ω : Ω₀) (i : Fin m) :=
    (N₀ ω ((n:ℝ)*aN n*τ i) - (n:ℝ)*aN n*τ i)/Real.sqrt n
  let Q (n : ℕ) (ω : Ω) (i : Fin m) :=
    (N n ω ((n:ℝ)*τ i) - (n:ℝ)*aN n*τ i)/Real.sqrt n
  let V (ω : Ω') (i : Fin m) := Real.sqrt (J:ℝ)*B ((a*τ i/(J:ℝ)).toNNReal) ω
  let U (ω : Ω') (i : Fin m) := Real.sqrt a*B (τ i).toNNReal ω
  have hZ : TendstoInDistribution Z atTop V (fun _ => P₀) P' :=
    centered_scaled_poisson_finite_dimensional_convergence N₀ hN₀ hId hSq
      aN haN a ha hconv T hT J hJ τ (fun j => ⟨hτ j,hτT j⟩) hB hBc
  have hPath (n : ℕ) : IdentDistrib (Q n) (Z n) P P₀ := by
    let F (p : ℝ≥0 → ℝ) (i : Fin m) := (p (τ i).toNNReal-(n:ℝ)*aN n*τ i)/Real.sqrt n
    have hmF : Measurable F := measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply (τ i).toNNReal).sub_const _).div_const _)
    have hScale : aN n*(n:ℝ) = 1*((n:ℝ)*aN n) := by ring
    have h := (poisson_path_laws_with_matched_time_scales (N n) N₀ (aN n) 1 (n:ℝ)
      ((n:ℝ)*aN n) (hN n) hN₀ (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (haN n)) hScale).comp hmF
    simpa only [F,Q,Z,Function.comp_def,Real.coe_toNNReal _ (hτ _)] using h
  have hOut : IdentDistrib V U P' P' := by
    rcases ha.eq_or_lt with h0 | h0
    · have hv : V =ᵐ[P'] U := by
        filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
        funext i
        simp [V,U,h0.symm,hω]
      exact IdentDistrib.of_ae_eq hZ.aemeasurable_limit hv
    · let c : ℝ≥0 := (a/(J:ℝ)).toNNReal
      have hcR : (c:ℝ) = a/(J:ℝ) := Real.coe_toNNReal _ (div_nonneg ha hJ0.le)
      have hcpos : 0 < (c:ℝ) := hcR ▸ div_pos h0 hJ0
      have hc : c ≠ 0 := by intro hh; exact hcpos.ne' (by rw [hh]; rfl)
      let C (t : ℝ≥0) (ω : Ω') := (Real.sqrt (c:ℝ))⁻¹ * B (c*t) ω
      have hC : IsBrownianReal C P' := hB.smul hc
      have heq : V = fun ω i => Real.sqrt a*C (τ i).toNNReal ω := by
        funext ω i
        have ht : (a*τ i/(J:ℝ)).toNNReal = c*(τ i).toNNReal := by
          apply Subtype.ext
          change ((a*τ i/(J:ℝ)).toNNReal:ℝ) = (c:ℝ)*((τ i).toNNReal:ℝ)
          rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg ha (hτ i)) hJ0.le),
            Real.coe_toNNReal _ (hτ i),hcR]
          ring
        have hcoef : Real.sqrt a = Real.sqrt (J:ℝ) * Real.sqrt (c:ℝ) := by
          rw [← Real.sqrt_mul (Nat.cast_nonneg J), hcR,
            show (J:ℝ)*(a/(J:ℝ)) = a by field_simp]
        dsimp only [V,C]
        rw [ht,hcoef]
        field_simp [(Real.sqrt_pos.2 hcpos).ne']
      rw [heq]
      exact brownian_weighted_finite_observation_law hC.toIsPreBrownianReal hB.toIsPreBrownianReal
        (fun j => (τ j).toNNReal) (fun _ => Real.sqrt a)
  refine ⟨fun n => (hPath n).aemeasurable_fst,hOut.aemeasurable_snd,?_⟩
  have hIn (n : ℕ) : (⟨P.map (Q n),Measure.isProbabilityMeasure_map (hPath n).aemeasurable_fst⟩ :
      ProbabilityMeasure (Fin m → ℝ)) =
      ⟨P₀.map (Z n),Measure.isProbabilityMeasure_map (hZ.forall_aemeasurable n)⟩ :=
    Subtype.ext (hPath n).map_eq
  have hTarget : (⟨P'.map V,Measure.isProbabilityMeasure_map hZ.aemeasurable_limit⟩ :
      ProbabilityMeasure (Fin m → ℝ)) =
      ⟨P'.map U,Measure.isProbabilityMeasure_map hOut.aemeasurable_snd⟩ :=
    Subtype.ext hOut.map_eq
  exact ((hTarget ▸ hZ.tendsto).congr fun n => (hIn n).symm)
