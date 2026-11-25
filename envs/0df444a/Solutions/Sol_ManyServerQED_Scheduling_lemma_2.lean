-- Prove2me | solution 1 for ManyServerQED.Scheduling.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:17:25.596117+00:00
-- url     : https://prove2.me/submissions/dfbfadb2-35d0-4a88-97a4-e197fc42c4a0

import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_StochApproxDyn_MartingaleNoise_burkholder_eq13

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal
open StochApproxDyn.MartingaleNoise

private noncomputable def harmonicSteps (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem harmonicSteps_pos (n : ℕ) : 0 < harmonicSteps n := by
  unfold harmonicSteps
  positivity

private theorem harmonicSteps_valid : IsStepSequence harmonicSteps := by
  refine ⟨fun n => (harmonicSteps_pos _).le, ?_, ?_⟩
  · apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => (harmonicSteps_pos (n+1)).le)).mp
    intro hs
    apply Real.not_summable_natCast_inv
    apply (summable_nat_add_iff 2).mp
    norm_num [harmonicSteps, Nat.cast_add, add_assoc] at hs ⊢
    exact hs
  · have h := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))
    apply h.comp
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

private theorem harmonicSteps_index (m : ℕ) :
    stepIndex harmonicSteps (StochApproxDyn.Interpolation.tau harmonicSteps m) = m := by
  have hs : StrictMono (StochApproxDyn.Interpolation.tau harmonicSteps) :=
    strictMono_nat_of_lt_succ (fun n => by
      unfold StochApproxDyn.Interpolation.tau
      rw [Finset.sum_range_succ]
      exact lt_add_of_pos_right _ (harmonicSteps_pos _))
  unfold stepIndex
  have hset : {k : ℕ | StochApproxDyn.Interpolation.tau harmonicSteps k ≤
       StochApproxDyn.Interpolation.tau harmonicSteps m} = Set.Iic m := by
    ext k
    exact hs.le_iff_le
  rw [hset, csSup_Iic]

private theorem sum_rpow_average (m : ℕ) (hm : 0 < m) (z : ℕ → ℝ) (hz : ∀ i, 0 ≤ z i)
    (q : ℝ) (hq : 1 ≤ q) :
    (∑ i ∈ range m, z i) ^ q ≤ (m : ℝ) ^ (q - 1) * ∑ i ∈ range m, (z i) ^ q := by
  have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
  have hj := (convexOn_rpow hq).map_sum_le (t := range m) (w := fun _ => (m : ℝ)⁻¹)
    (p := z) (fun _ _ => inv_nonneg.mpr hmr.le)
    (by simp [nsmul_eq_mul, hmr.ne']) (fun i _ => hz i)
  simp only [smul_eq_mul, ← Finset.mul_sum, Real.mul_rpow (inv_nonneg.mpr hmr.le)
    (Finset.sum_nonneg (fun i _ => hz i)), Real.inv_rpow hmr.le] at hj
  have hh := mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hmr.le q)
  rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hmr q).ne', one_mul] at hh
  rw [← mul_assoc, ← Real.rpow_neg_one (m:ℝ), ← Real.rpow_add hmr, show q + -1 = q - 1 by ring] at hh
  exact hh

private theorem discrete_centered_sum_max_moment (p : ℝ) (hp : 2 ≤ p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ → Ω → ℝ)
      (hY : ∀ j, Measurable (Y j)), iIndepFun Y P →
      (∀ j, Integrable (Y j) P) → (∀ j, ∫ ω, Y j ω ∂P = 0) →
      (∀ j, IdentDistrib (Y j) (Y 0) P P) →
      ∀ m : ℕ, 0 < m →
        ∫⁻ ω, ((Ioc 0 m).sup fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω|)^p ∂P
        ≤ ENNReal.ofReal (C * (m : ℝ)^(p/2)) *
          ∫⁻ ω, ENNReal.ofReal (|Y 0 ω|^p) ∂P := by
  obtain ⟨C, hC, hBurk⟩ := burkholder_eq13 1 p hp
  refine ⟨C, hC, fun Y hY hInd hInt hMean hid m hm => ?_⟩
  let E := EuclideanSpace ℝ (Fin 1)
  let e : ℝ ≃ₗᵢ[ℝ] E := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let a (j : ℕ) := MeasurableSpace.comap (Y j) inferInstance
  have ha (j : ℕ) : a j ≤ (inferInstance : MeasurableSpace Ω) := (hY j).comap_le
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    ⟨fun j => ⨆ i < j, a i,
      fun j l hjl => iSup_le fun i => iSup_le fun hi => le_iSup₂_of_le i (hi.trans_le hjl) le_rfl,
      fun j => iSup₂_le fun i _ => ha i⟩
  let U (j : ℕ) (ω : Ω) : E := (harmonicSteps j)⁻¹ • e (Y (j-1) ω)
  let x (j : ℕ) (ω : Ω) : E := ∑ i ∈ range j, e (Y i ω)
  have hstep (j : ℕ) (ω : Ω) : harmonicSteps (j+1) • U (j+1) ω = e (Y j ω) := by
    simp [U, smul_smul, (harmonicSteps_pos (j+1)).ne']
  have hU (j : ℕ) : StronglyMeasurable[a j] (U (j+1)) := by
    have hmeas : @Measurable Ω ℝ (MeasurableSpace.comap (Y j) inferInstance) inferInstance (Y j) :=
      Measurable.of_comap_le le_rfl
    change StronglyMeasurable[a j]
      (((harmonicSteps (j+1))⁻¹) • (fun ω => e (Y j ω)))
    exact (e.continuous.measurable.comp hmeas).stronglyMeasurable.const_smul ((harmonicSteps (j+1))⁻¹)
  have hUmean (j : ℕ) : (∫ ω, U (j+1) ω ∂P) = 0 := by
    change (∫ ω, (harmonicSteps (j+1))⁻¹ • e (Y j ω) ∂P) = 0
    rw [integral_smul]
    have h := e.toLinearIsometry.integral_comp_comm (μ := P) (Y j)
    change (∫ ω, e (Y j ω) ∂P) = e (∫ ω, Y j ω ∂P) at h
    rw [h, hMean, map_zero, smul_zero]
  have hRM : IsRobbinsMonro P ℱ (fun _ : E => 0) harmonicSteps x U := by
    refine ⟨continuous_const, harmonicSteps_valid, ?_, ?_, ?_, ?_⟩
    · intro n ω
      simp only [x, zero_add, Finset.sum_range_succ, hstep, add_sub_cancel_left]
    · intro n
      exact (hU n).mono (le_iSup₂ (f := fun i (_ : i < n+1) => a i) n (Nat.lt_succ_self _))
    · intro n
      change Integrable (((harmonicSteps (n+1))⁻¹) • (fun ω => e (Y n ω))) P
      exact (e.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hInt n)).smul _
    · intro n
      have hd : Disjoint ({n} : Set ℕ) (Set.Iio n) := by simp
      have hh : Indep (a n) (ℱ n) P := by
        have hh := indep_iSup_of_disjoint (m := a) ha hInd hd
        simpa [ℱ] using hh
      haveI : IsFiniteMeasure (P.trim (ℱ.le n)) := by infer_instance
      change _ =ᵐ[P] (fun _ => (0:E))
      simpa [hUmean] using condExp_indep_eq (ha n) (ℱ.le n) (hU n) hh
  let T := StochApproxDyn.Interpolation.tau harmonicSteps m
  have hT : 0 < T := by
    apply Finset.sum_pos (fun i _ => harmonicSteps_pos (i+1))
    exact Finset.nonempty_range_iff.mpr hm.ne'
  have hi : stepIndex harmonicSteps (StochApproxDyn.Interpolation.tau harmonicSteps 0 + T) = m := by
    simpa [T, StochApproxDyn.Interpolation.tau] using harmonicSteps_index m
  have hb := hBurk P ℱ (fun _ : E => 0) harmonicSteps x U hRM 0 T hT
  rw [hi] at hb
  have hnorm (j : ℕ) (ω : Ω) :
      ‖∑ i ∈ range j, harmonicSteps (i+1) • U (i+1) ω‖ₑ =
        ENNReal.ofReal |∑ i ∈ range j, Y i ω| := by
    simp [hstep, ← map_sum, ← ofReal_norm, Real.norm_eq_abs]
  have hsq (j : ℕ) (ω : Ω) :
      ENNReal.ofReal (harmonicSteps (j+1)^2) * ‖U (j+1) ω‖ₑ^(2:ℝ) =
        ENNReal.ofReal (|Y j ω|^2) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) from rfl, ENNReal.rpow_natCast, ← ofReal_norm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _), ← mul_pow]
    congr 2
    have hh := congrArg norm (hstep j ω)
    simpa [norm_smul, e.norm_map, Real.norm_eq_abs, abs_of_pos (harmonicSteps_pos _)] using hh
  simp only [Nat.Ico_zero_eq_range, hnorm, hsq] at hb
  have hpow_sup (ω : Ω) : ((Ioc 0 m).sup fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω|)^p =
      (Ioc 0 m).sup fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω| ^ p := by
    have hne : (Ioc 0 m).Nonempty := ⟨m, mem_Ioc.mpr ⟨hm, le_rfl⟩⟩
    obtain ⟨j, hj, he⟩ := (Ioc 0 m).exists_mem_eq_sup hne
      (fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω|)
    apply le_antisymm
    · rw [he]
      exact Finset.le_sup (f := fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω| ^ p) hj
    · exact Finset.sup_le fun i hi => ENNReal.rpow_le_rpow (Finset.le_sup (f := fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω|) hi) (by linarith)
  simp_rw [hpow_sup]
  refine hb.trans ?_
  let q := p / 2
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
  have hpoint (ω : Ω) :
      (∑ i ∈ range m, ENNReal.ofReal (|Y i ω|^2))^q ≤
        ENNReal.ofReal ((m:ℝ)^(q-1)) * ∑ i ∈ range m, ENNReal.ofReal (|Y i ω|^p) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg |Y i ω|),
      ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg |Y i ω|))
        (by linarith)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hmr.le _)]
    apply ENNReal.ofReal_le_ofReal
    have h := sum_rpow_average m hm (fun i => |Y i ω|^2) (fun i => sq_nonneg _) q hq
    simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), Nat.cast_ofNat] at h
    have he : ((2:ℕ):ℝ)*q = p := by dsimp [q]; norm_num; ring
    simpa only [he, show (2:ℝ) = ((2:ℕ):ℝ) from rfl, Real.rpow_natCast] using h
  let g (i : ℕ) (ω : Ω) := ENNReal.ofReal (|Y i ω|^p)
  have hmom (i : ℕ) : (∫⁻ ω, g i ω ∂P) = ∫⁻ ω, ENNReal.ofReal (|Y 0 ω|^p) ∂P := by
    exact ((hid i).comp (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (|x|^p)))).lintegral_eq
  calc
    _ ≤ ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal ((m:ℝ)^(q-1)) *
          ∑ i ∈ range m, g i ω ∂P := by
      exact mul_le_mul_right (lintegral_mono hpoint) _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum (f := g) (range m) (fun i _ => by dsimp [g]; fun_prop)]
      simp only [hmom, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast]
      have he : (m:ℝ)^(q-1) * m = (m:ℝ)^q := by
        calc
          _ = (m:ℝ)^(q-1) * (m:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hmr, sub_add_cancel]
      rw [← mul_assoc, ← mul_assoc, mul_assoc (ENNReal.ofReal C),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hmr.le _), he,
        ← ENNReal.ofReal_mul hC.le]

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
private theorem renewal_lower_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hp : ∀ i ω, 0 < U i ω) (hI : iIndepFun U P)
    (hid : ∀ i, IdentDistrib (U i) (U 0) P P) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (j : ℕ) (r : ℝ), r ≤ δ * j →
      P {ω | ∑ i ∈ range j, U i ω ≤ r} ≤ ENNReal.ofReal (ρ^j) := by
  let f : ℝ → ℝ := fun r => Real.exp (-r)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hI0 : Integrable (f ∘ U 0) P := by
    apply (integrable_const (1:ℝ)).mono' (hf.comp (hU 0)).aestronglyMeasurable
    filter_upwards with ω
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.mpr (hp 0 ω).le)
  let b := ∫ ω, f (U 0 ω) ∂P
  have hb : 0 < b := integral_exp_pos hI0
  have hb1 : b < 1 := by
    have ht : Integrable (fun ω => 1 - f (U 0 ω)) P := (integrable_const _).sub hI0
    have hp0 (ω : Ω) : 0 < 1 - f (U 0 ω) := sub_pos.mpr (Real.exp_lt_one_iff.2 (neg_neg_of_pos (hp 0 ω)))
    have hh := (integral_pos_iff_support_of_nonneg (fun ω => (hp0 ω).le) ht).2
    have hsu : Function.support (fun ω => 1 - f (U 0 ω)) = Set.univ :=
      Set.eq_univ_iff_forall.mpr (fun ω => (hp0 ω).ne')
    simp only [hsu, measure_univ, one_ne_zero] at hh
    have hlt := hh zero_lt_one
    have hI0' : Integrable (fun ω => f (U 0 ω)) P := hI0
    rw [integral_sub (integrable_const (1:ℝ)) hI0'] at hlt
    simpa only [integral_const, probReal_univ, one_smul, sub_pos, b] using hlt
  let δ := -(Real.log b) / 2
  let ρ := Real.exp (-δ)
  have hδ : 0 < δ := by dsimp [δ]; linarith [Real.log_neg hb hb1]
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos hδ)
  have hbρ : Real.exp δ * b = ρ := by
    calc
      _ = Real.exp (δ + Real.log b) := by rw [Real.exp_add, Real.exp_log hb]
      _ = _ := by congr 1; dsimp [δ]; ring
  refine ⟨δ, ρ, hδ, hρ, hρ1, fun j r hr => ?_⟩
  let e (ω : Ω) : ℝ := ∑ i ∈ range j, U i ω
  have hem : Measurable e := Finset.measurable_sum _ (fun i _ => hU i)
  have hE : (∫ ω, Real.exp (-e ω) ∂P) = b^j := by
    let idx (i : Fin j) : ℕ := i
    have hind := hI.precomp (show Function.Injective idx from Fin.val_injective)
    have he (ω : Ω) : Real.exp (-e ω) = ∏ i : Fin j, f (U i ω) := by
      unfold e f
      rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun i => -U i ω) j).symm
    simp_rw [he]
    rw [hind.integral_fun_prod_comp
      (fun i => (hU i).aemeasurable) (fun _ => hf.aestronglyMeasurable)]
    have hterm (i : Fin j) : (∫ ω, f (U i ω) ∂P) = b :=
      ((hid i).comp hf).integral_eq
    change (∏ i : Fin j, ∫ ω, f (U i ω) ∂P) = _
    simp [hterm]
  have hExpInt : Integrable (fun ω => Real.exp (r - e ω)) P := by
    apply (integrable_const (Real.exp r)).mono' (by fun_prop)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    gcongr
    exact sub_le_self _ (Finset.sum_nonneg fun i _ => (hp i ω).le)
  have hme : MeasurableSet {ω | e ω ≤ r} := measurableSet_le hem measurable_const
  have hP : (P {ω | e ω ≤ r}).toReal ≤ Real.exp r * b^j := by
    calc
      _ = ∫ ω, Set.indicator {ω | e ω ≤ r} (fun _ => (1:ℝ)) ω ∂P := by
        rw [integral_indicator hme, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
      _ ≤ ∫ ω, Real.exp (r - e ω) ∂P := by
        apply integral_mono ((integrable_const _).indicator hme) hExpInt
        intro ω
        by_cases h : ω ∈ {ω | e ω ≤ r}
        · rw [Set.indicator_of_mem h]
          exact Real.one_le_exp_iff.2 (sub_nonneg.mpr h)
        · exact (Set.indicator_of_notMem h _).trans_le (Real.exp_pos _).le
      _ = _ := by simp_rw [sub_eq_add_neg, Real.exp_add, integral_const_mul, hE]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  apply ENNReal.ofReal_le_ofReal
  refine hP.trans ?_
  calc
    _ ≤ Real.exp (δ * j) * b^j := by gcongr
    _ = ρ^j := by rw [mul_comm δ, Real.exp_nat_mul, ← mul_pow, hbρ]

private theorem polynomial_times_geometric_finite (p ρ : ℝ) (hp : 0 ≤ p) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑' j : ℕ, ENNReal.ofReal ((2*j : ℝ)^p * ρ^j)) < ⊤ := by
  let k : ℕ := ⌈p⌉₊
  have hk : p ≤ k := Nat.le_ceil p
  have hs : Summable (fun j : ℕ => (2:ℝ)^p * (1 + (j:ℝ)^k) * ρ^j) := by
    have h₁ := summable_geometric_of_lt_one hρ hρ1
    have h₂ := summable_pow_mul_geometric_of_norm_lt_one k (r := ρ) (by rwa [Real.norm_eq_abs, abs_of_nonneg hρ])
    simpa only [add_mul, one_mul, mul_assoc] using (h₁.add h₂).mul_left ((2:ℝ)^p)
  have hs' : Summable (fun j : ℕ => (2*j : ℝ)^p * ρ^j) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
    gcongr
    by_cases hj : j = 0
    · subst j
      simpa only [Nat.cast_zero] using (Real.zero_rpow_le_one (x := p)).trans
        (le_add_of_nonneg_right (pow_nonneg (by norm_num : 0 ≤ (0:ℝ)) k))
    · have hj1 : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      exact ((Real.rpow_le_rpow_of_exponent_le hj1 hk).trans_eq (Real.rpow_natCast _ _)).trans
        (le_add_of_nonneg_left zero_le_one)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs']
  exact ENNReal.ofReal_lt_top

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

private theorem renewal_inverse_pointwise {Ω : Type*} (U : ℕ → Ω → ℝ)
    (hpos : ∀ j ω, 0 < U j ω)
    (hfin : ∀ ω, Tendsto (fun j => ∑ i ∈ range j, U i ω) atTop atTop)
    (r : ℝ) (hr : 0 ≤ r) (p : ℝ) (hp : 0 < p) (m : ℕ)
    (hm : r ≤ (m:ℝ)) (ω : Ω) :
    (⨆ s ∈ Set.Icc 0 r, ENNReal.ofReal
      |(((renewalCount (fun j => ∑ i ∈ range j, U i ω) s).toNat : ℕ) : ℝ) - s|^p)
      ≤ (2:ℝ≥0∞)^p * (1 + ((Ioc 0 m).sup (fun j =>
          ENNReal.ofReal |∑ i ∈ range j, (U i ω - 1)|))^p) +
        ∑' j : ℕ, Set.indicator
          {ω | m ≤ j ∧ ∑ i ∈ range j, U i ω ≤ r}
          (fun _ => ENNReal.ofReal ((2*j:ℝ)^p)) ω := by
  let E (j : ℕ) : ℝ := ∑ i ∈ range j, U i ω
  let K (j : ℕ) := ENNReal.ofReal |E j - j|
  let B := (Ioc 0 m).sup K
  have hE0 : E 0 = 0 := by simp [E]
  have hEm : StrictMono E := strictMono_nat_of_lt_succ fun j => by
    unfold E
    rw [Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (hpos j ω)
  have hK (j : ℕ) : K j = ENNReal.ofReal |∑ i ∈ range j, (U i ω - 1)| := by
    simp [K, E, Finset.sum_sub_distrib]
  simp_rw [← hK]
  apply iSup₂_le
  intro s hs
  change ENNReal.ofReal |((renewalCount E s).toNat : ℝ) - s|^p ≤ _
  by_cases hgood : r < E m
  · obtain ⟨j, hj, h1, h2, hc⟩ := renewal_bracket hEm (hE0.symm ▸ hs.1) (hs.2.trans_lt hgood)
    have hj1 : j + 1 ≤ m := Nat.succ_le_of_lt hj
    have hB (i : ℕ) (hi : i ≤ m) : K i ≤ B := by
      by_cases h0 : i = 0
      · subst i
        simp [K, hE0]
      · exact Finset.le_sup (f := K) (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, hi⟩)
    have hdev : ENNReal.ofReal |(j:ℝ) - s| ≤ 1 + B := by
      have hreal : |(j:ℝ) - s| ≤ 1 + max |E j - j| |E (j+1) - (j+1:ℕ)| := by
        have hk1 := le_max_left |E j - j| |E (j+1) - (j+1:ℕ)|
        have hk2 := le_max_right |E j - j| |E (j+1) - (j+1:ℕ)|
        have hl := (neg_le_abs (E j - j)).trans hk1
        have hu := (le_abs_self (E (j+1) - (j+1:ℕ))).trans hk2
        push_cast at hl hu ⊢
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [ENNReal.ofReal_add zero_le_one (le_max_left _ _ |>.trans' (abs_nonneg _)),
        ENNReal.ofReal_one, ENNReal.ofReal_max]
      exact add_le_add_right (max_le (hB j hj.le) (hB (j+1) hj1)) _
    have hcost : (1 + B)^p ≤ (2:ℝ≥0∞)^p * (1 + B^p) := by
      have hh : 1 + B ≤ 2 * max 1 B := by
        simpa [two_mul] using add_le_add (le_max_left (1:ℝ≥0∞) B) (le_max_right 1 B)
      calc
        _ ≤ (2 * max 1 B)^p := ENNReal.rpow_le_rpow hh hp.le
        _ ≤ _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          apply mul_le_mul_right
          rcases le_total (1:ℝ≥0∞) B with h | h
          · rw [max_eq_right h]
            exact le_add_left (le_refl _)
          · rw [max_eq_left h, ENNReal.one_rpow]
            exact le_self_add
    rw [hc]
    exact ((ENNReal.rpow_le_rpow (by simpa only [ENat.toNat_natCast] using hdev) hp.le).trans hcost).trans le_self_add
  · obtain ⟨j0, hj0⟩ := eventually_atTop.mp ((tendsto_atTop.1 (hfin ω)) (r+1))
    have he0 : r < E j0 := lt_of_lt_of_le (by linarith) (hj0 j0 le_rfl)
    obtain ⟨j, hj, h1, h2, hc⟩ := renewal_bracket hEm (hE0.symm ▸ hr) he0
    have hmj : m ≤ j := by
      by_contra! hmj
      exact hgood (h2.trans_le (hEm.monotone hmj))
    have his : renewalCount E s ≤ j := by
      rw [← hc]
      exact iSup₂_le fun l hl => le_iSup₂_of_le l (hl.trans hs.2) le_rfl
    have hcs : ((renewalCount E s).toNat : ℝ) ≤ j := by
      exact_mod_cast ENat.toNat_le_of_le_natCast his
    have hlim : r ≤ (j:ℝ) := hm.trans (by exact_mod_cast hmj)
    have hpn : ENNReal.ofReal |((renewalCount E s).toNat : ℝ) - s|^p ≤
        ENNReal.ofReal ((2*j:ℝ)^p) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le]
      apply ENNReal.ofReal_le_ofReal
      have hjr : 0 ≤ (j:ℝ) := by positivity
      have hcs0 : (0:ℝ) ≤ ((renewalCount E s).toNat : ℝ) := by positivity
      apply Real.rpow_le_rpow (abs_nonneg _) (abs_le.mpr ⟨?_, ?_⟩) hp.le <;> linarith [hs.1, hs.2]
    let F (i : ℕ) : ℝ≥0∞ :=
      Set.indicator {ω | m ≤ i ∧ ∑ a ∈ range i, U a ω ≤ r} (fun _ => ENNReal.ofReal ((2*i:ℝ)^p)) ω
    have hmem : ω ∈ {ω | m ≤ j ∧ ∑ a ∈ range j, U a ω ≤ r} := ⟨hmj, h1⟩
    have he : F j = ENNReal.ofReal ((2*j:ℝ)^p) := Set.indicator_of_mem hmem _
    have hsingle : F j ≤ ∑' i, F i := ENNReal.le_tsum j
    rw [he] at hsingle
    exact (hpn.trans hsingle).trans (le_add_left (le_refl _))


private theorem renewal_inverse_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
    (hpos : ∀ i ω, 0 < U i ω) (hI : iIndepFun U P)
    (hid : ∀ i, IdentDistrib (U i) (U 0) P P)
    (hfin : ∀ ω, Tendsto (fun j => ∑ i ∈ range j, U i ω) atTop atTop)
    (hint : ∀ i, Integrable (U i) P) (hmean : ∀ i, ∫ ω, U i ω ∂P = 1)
    (p : ℝ) (hp : 2 ≤ p) (hpfin : (∫⁻ ω, ENNReal.ofReal |U 0 ω - 1|^p ∂P) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∃ J : Ω → ℝ≥0∞, Measurable J ∧
        (∀ ω, (⨆ s ∈ Set.Icc 0 r, ENNReal.ofReal
          |(((renewalCount (fun j => ∑ i ∈ range j, U i ω) s).toNat : ℕ) : ℝ) - s|^p) ≤ J ω) ∧
        (∫⁻ ω, J ω ∂P) ≤ ENNReal.ofReal (C * (1+r)^(p/2)) := by
  obtain ⟨δ, ρ, hδ, hρ, hρ1, htail⟩ := renewal_lower_tail P U hU hpos hI hid
  obtain ⟨B, hB, hmax⟩ := discrete_centered_sum_max_moment p hp P
  let Y (i : ℕ) (ω : Ω) := U i ω - 1
  let I := ∫⁻ ω, ENNReal.ofReal (|Y 0 ω|^p) ∂P
  let F := ∑' j : ℕ, ENNReal.ofReal ((2*j:ℝ)^p * ρ^j)
  let L := 2 + δ⁻¹
  let q := p/2
  have hIf : I < ⊤ := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (show 0 ≤ p by linarith)] at hpfin
    exact hpfin
  have hFf : F < ⊤ := polynomial_times_geometric_finite p ρ (by linarith) hρ.le hρ1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hYn (i : ℕ) : Measurable (Y i) := (hU i).sub_const 1
  have hYi : iIndepFun Y P := hI.comp (fun _ (u : ℝ) => u-1) (fun _ => measurable_id.sub_const _)
  have hYint (i : ℕ) : Integrable (Y i) P := (hint i).sub (integrable_const 1)
  have hYmean (i : ℕ) : (∫ ω, Y i ω ∂P) = 0 := by
    unfold Y
    rw [integral_sub (hint i) (integrable_const _), hmean]
    simp
  have hYid (i : ℕ) : IdentDistrib (Y i) (Y 0) P P := (hid i).comp (measurable_id.sub_const _)
  let D := B * L^q * I.toReal
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2^p * (1+D) + F.toReal, by positivity, fun r hr => ?_⟩
  let m : ℕ := ⌊r + (1+r)*δ⁻¹⌋₊ + 1
  have hmr : r + (1+r)*δ⁻¹ < (m:ℝ) := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (r + (1+r)*δ⁻¹)
  have hrm : r ≤ (m:ℝ) := by
    linarith [mul_nonneg (by linarith : 0 ≤ 1+r) (inv_nonneg.mpr hδ.le)]
  have hmpos : 0 < m := by simp [m]
  have hmδ {j : ℕ} (hj : m ≤ j) : r ≤ δ * j := by
    have hh : (1+r)*δ⁻¹ ≤ (j:ℝ) := by
      have hj' : (m:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    rw [← div_eq_mul_inv, div_le_iff₀ hδ] at hh
    linarith
  have hmL : (m:ℝ) ≤ L*(1+r) := by
    have hfloor := Nat.floor_le (show 0 ≤ r + (1+r)*δ⁻¹ by positivity)
    dsimp [m, L]
    push_cast
    nlinarith
  let G (ω : Ω) := ((Ioc 0 m).sup (fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω|))^p
  let S (j : ℕ) := {ω | m ≤ j ∧ ∑ i ∈ range j, U i ω ≤ r}
  let H (j : ℕ) (ω : Ω) := Set.indicator (S j) (fun _ => ENNReal.ofReal ((2*j:ℝ)^p)) ω
  have hSm (j : ℕ) : MeasurableSet (S j) := by
    change MeasurableSet ({ω | m ≤ j} ∩ {ω | ∑ i ∈ range j, U i ω ≤ r})
    have hconst : MeasurableSet {ω : Ω | m ≤ j} := by
      by_cases h : m ≤ j <;> simp [h]
    exact hconst.inter
      (measurableSet_le (Finset.measurable_sum _ (fun i _ => hU i)) measurable_const)
  have hHm (j : ℕ) : Measurable (H j) := measurable_const.indicator (hSm j)
  have hG : (∫⁻ ω, G ω ∂P) ≤ ENNReal.ofReal (D * (1+r)^q) := by
    refine (hmax Y hYn hYi hYint hYmean hYid m hmpos).trans ?_
    change ENNReal.ofReal (B * (m:ℝ)^q) * I ≤ _
    rw [← ENNReal.ofReal_toReal hIf.ne, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hmp := Real.rpow_le_rpow (Nat.cast_nonneg m) hmL hq
    rw [Real.mul_rpow hL (by positivity)] at hmp
    calc
      _ ≤ B * (L^q * (1+r)^q) * I.toReal := by gcongr
      _ = _ := by unfold D; ring
  have hHF : (∫⁻ ω, ∑' j, H j ω ∂P) ≤ F := by
    rw [lintegral_tsum (fun j => (hHm j).aemeasurable)]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [lintegral_indicator_const (hSm j)]
    by_cases hj : m ≤ j
    · have he : S j = {ω | ∑ i ∈ range j, U i ω ≤ r} := by ext ω; simp [S, hj]
      rw [he, ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact htail j r (hmδ hj)
    · simp [S, hj]
  have hTm : Measurable (fun ω : Ω => ∑' j : ℕ, H j ω) := Measurable.tsum hHm
  refine ⟨fun ω => (2:ℝ≥0∞)^p * (1 + G ω) + ∑' j, H j ω, ?_,
    fun ω => renewal_inverse_pointwise U hpos hfin r hr p (by linarith) m hrm ω, ?_⟩
  · have hmne : (Ioc 0 m).Nonempty := ⟨m, mem_Ioc.mpr ⟨hmpos, le_rfl⟩⟩
    have hf (j : ℕ) : Measurable (fun ω => ENNReal.ofReal |∑ i ∈ range j, Y i ω|) :=
      (Finset.measurable_sum _ (fun i _ => hYn i)).abs.ennreal_ofReal
    have hsup : Measurable (fun ω => (Ioc 0 m).sup (fun j => ENNReal.ofReal |∑ i ∈ range j, Y i ω|)) := by
      let f (j : ℕ) (ω : Ω) := ENNReal.ofReal |∑ i ∈ range j, Y i ω|
      have hh := Finset.measurable_sup' (f := f) hmne (fun j _ => hf j)
      have he : (Ioc 0 m).sup' hmne f = fun ω => (Ioc 0 m).sup (fun j => f j ω) := by
        funext ω
        rw [Finset.sup'_apply, Finset.sup'_eq_sup]
      rw [he] at hh
      exact hh
    have hGm : Measurable G := (ENNReal.continuous_rpow_const.measurable.comp hsup)
    exact (measurable_const.mul (measurable_const.add hGm)).add hTm
  change (∫⁻ ω, (2:ℝ≥0∞)^p * (1 + G ω) + ∑' j, H j ω ∂P) ≤ _
  have htwo : (2:ℝ≥0∞)^p = ENNReal.ofReal ((2:ℝ)^p) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
    norm_num
  rw [lintegral_add_right _ hTm, htwo, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  have hq1 : 1 ≤ (1+r)^q := Real.one_le_rpow (by linarith) hq
  refine (add_le_add (mul_le_mul_right (add_le_add_right hG _) _) hHF).trans ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hFf.ne,
    ← ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  change (2:ℝ)^p * (1 + D * (1+r)^q) + F.toReal ≤
    ((2:ℝ)^p * (1 + D) + F.toReal) * (1+r)^q
  nlinarith [mul_nonneg (sub_nonneg.mpr hq1)
    (add_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (2:ℝ)) p) (ENNReal.toReal_nonneg (a := F)))]

private theorem epoch_sum_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (ω : Ω) (m : ℕ) :
    ∑ j ∈ range m, M.U i (j+1) ω = partialSum (fun j => M.U i j ω) m := by
  unfold partialSum
  rw [show Finset.Icc 1 m = Finset.Ico 1 (m+1) from by ext; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm]

private theorem renewal_on_rate_clock {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (s : ℝ) :
    M.A n i ω s =
      ((renewalCount (fun j => ∑ l ∈ range j, M.U i (l+1) ω) (M.lamN n i * s)).toNat : ℝ) := by
  have heq (j : ℕ) : M.arrivalEpoch n i ω j = (∑ l ∈ range j, M.U i (l+1) ω) / M.lamN n i := by
    rw [epoch_sum_eq]
    simp [SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  unfold SystemSequence.A renewalCount
  simp only [heq, div_le_iff₀ (M.lamN_pos n i), mul_comm s]

private theorem fin_vector_rpow_le {k : ℕ} (z : Fin k → ℝ≥0∞) (p : ℝ) (hp : 0 < p) :
    (∑ i, z i)^p ≤ (k:ℝ≥0∞)^p * ∑ i, (z i)^p := by
  let s : Finset (Fin k) := Finset.univ
  change (∑ i ∈ s, z i)^p ≤ _ 
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs, ENNReal.zero_rpow_of_pos hp]
  · obtain ⟨j, hj, he⟩ := s.exists_mem_eq_sup hs z
    have hsum : ∑ i ∈ s, z i ≤ (k:ℝ≥0∞) * z j := by
      calc
        _ ≤ ∑ i ∈ s, z j :=
          Finset.sum_le_sum fun i hi => he ▸ Finset.le_sup (f := z) hi
        _ = _ := by simp [s, nsmul_eq_mul]
    refine (ENNReal.rpow_le_rpow hsum hp.le).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    exact mul_le_mul_right
      (Finset.single_le_sum (f := fun i => (z i)^p) (fun _ _ => zero_le) hj) _

set_option maxHeartbeats 1400000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (mL mU : ℝ)
    (hA3 : M.Assumption3 mL mU) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, supDist (M.Ahat n ω) (fun _ => 0) t ^ mU ∂M.P ≤
        ENNReal.ofReal (c * (1 + t ^ (mU / 2))) := by
  classical
  letI : IsProbabilityMeasure M.P := M.isProb
  let p := mU
  let q := p/2
  have hp2 : 2 ≤ p := hA3.1
  have hp : 0 < p := by linarith
  have hq : 0 ≤ q := by dsimp [q]; linarith
  let U (i : Fin k) (j : ℕ) (ω : Ω) := M.U i (j+1) ω
  have hU (i : Fin k) (j : ℕ) : Measurable (U i j) := M.U_meas i (j+1)
  have hpU (i : Fin k) (j : ℕ) (ω : Ω) : 0 < U i j ω := M.U_pos i (j+1) ω (by omega)
  have hiU (i : Fin k) : iIndepFun (U i) M.P := by
    let g : ℕ → (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k) := fun j => Sum.inl (i, j)
    have hg : Function.Injective g := fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)
    exact (M.indep 0).precomp hg
  have hid (i : Fin k) (j : ℕ) : IdentDistrib (U i j) (U i 0) M.P M.P :=
    M.U_ident i (j+1) (by omega)
  have hfin (i : Fin k) (ω : Ω) : Tendsto (fun j => ∑ l ∈ range j, U i l ω) atTop atTop := by
    simpa only [U, epoch_sum_eq] using M.U_finite i ω
  have hint (i : Fin k) (j : ℕ) : Integrable (U i j) M.P :=
    ((hid i j).memLp_iff.2 (M.U_memLp i)).integrable (by norm_num)
  have hm (i : Fin k) (j : ℕ) : (∫ ω, U i j ω ∂M.P) = 1 :=
    (hid i j).integral_eq.trans (M.U_mean i)
  have hpow (i : Fin k) : (∫⁻ ω, ENNReal.ofReal |U i 0 ω - 1|^p ∂M.P) < ⊤ := by
    have hg (ω : Ω) : ENNReal.ofReal |U i 0 ω - 1| ≤ ENNReal.ofReal (U i 0 ω) + 1 := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (hpU i 0 ω).le zero_le_one]
      exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith [hpU i 0 ω], by linarith⟩)
    have hg' (ω : Ω) : (ENNReal.ofReal |U i 0 ω - 1|)^p ≤
        (2:ℝ≥0∞)^p * ((ENNReal.ofReal (U i 0 ω))^p + 1) := by
      refine (ENNReal.rpow_le_rpow (hg ω) hp.le).trans ?_
      simpa using ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
        (ENNReal.ofReal (U i 0 ω)) 1 hp.le
    refine lt_of_le_of_lt (lintegral_mono hg') ?_
    have hm' : Measurable (fun _ : Ω => (1:ℝ≥0∞)) := measurable_const
    have h2 : (2:ℝ≥0∞)^p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le (by norm_num)
    rw [lintegral_const_mul' _ _ h2, lintegral_add_right _ hm', lintegral_const, measure_univ, mul_one]
    exact ENNReal.mul_lt_top h2.lt_top (ENNReal.add_lt_top.mpr ⟨hA3.2.2 i, ENNReal.one_lt_top⟩)
  choose C hC hRen using fun i => renewal_inverse_moment M.P (U i) (hU i) (hpU i) (hiU i)
    (hid i) (hfin i) (hint i) (hm i) p hp2 (hpow i)
  have hRate (i : Fin k) : ∃ a : ℝ, 1 ≤ a ∧ ∀ n : ℕ, 1 ≤ n → M.lamN n i ≤ a*n := by
    obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ (M.lam_lim i)).bddAbove
    refine ⟨max B 1, le_max_right _ _, fun n hn => ?_⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
    exact (div_le_iff₀ hn').1 ((hB ⟨n,rfl⟩).trans (le_max_left _ _))
  choose a ha hRa using hRate
  let D : Fin k → ℝ := fun i => C i * (a i)^q * (2:ℝ)^q
  have ha0 (i : Fin k) : 0 ≤ a i := le_trans zero_le_one (ha i)
  have hD (i : Fin k) : 0 ≤ D i := by
    unfold D
    exact mul_nonneg (mul_nonneg (hC i) (Real.rpow_nonneg (ha0 i) _))
      (Real.rpow_nonneg (by norm_num) _)
  refine ⟨(k:ℝ)^p * ∑ i, D i, fun n hn t ht => ?_⟩
  let r (i : Fin k) := M.lamN n i * t
  have hr (i : Fin k) : 0 ≤ r i := mul_nonneg (M.lamN_pos n i).le ht
  choose J hJm hJp hJi using fun i => hRen i (r i) (hr i)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  let α : ℝ := ((n:ℝ)^q)⁻¹
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαs : (Real.sqrt (n:ℝ))⁻¹ ^ p = α := by
    rw [Real.inv_rpow hs.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
    congr 2
    dsimp [q]
    ring
  have htime : (1+t)^q ≤ (2:ℝ)^q * (1+t^q) := by
    rcases le_total t 1 with h | h
    · have h1 : (1+t)^q ≤ (2:ℝ)^q := Real.rpow_le_rpow (by positivity) (by linarith) hq
      exact h1.trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (Real.rpow_nonneg ht _)))
    · have hh : (1+t)^q ≤ (2*t)^q := Real.rpow_le_rpow (by positivity) (by linarith) hq
      rw [Real.mul_rpow (by norm_num) ht] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
  have hsJ (i : Fin k) : ENNReal.ofReal α * (∫⁻ ω, J i ω ∂M.P) ≤
      ENNReal.ofReal (D i * (1+t^q)) := by
    refine (mul_le_mul_right (hJi i) _).trans ?_
    rw [← ENNReal.ofReal_mul hα]
    apply ENNReal.ofReal_le_ofReal
    have haux : 1 + r i ≤ (n:ℝ) * (a i * (1+t)) := by
      have hl := mul_le_mul_of_nonneg_right (hRa i n hn) ht
      have hh : 1 ≤ (n:ℝ) * a i := one_le_mul_of_one_le_of_one_le hn1 (ha i)
      dsimp [r]
      nlinarith
    have hA0 : 0 ≤ a i := (by linarith [ha i])
    have hpowr := Real.rpow_le_rpow (show 0 ≤ 1+r i from add_nonneg zero_le_one (hr i)) haux hq
    rw [Real.mul_rpow hn0.le (by positivity), Real.mul_rpow hA0 (by positivity)] at hpowr
    have hcn : 0 < (n:ℝ)^q := Real.rpow_pos_of_pos hn0 _
    calc
      α * (C i * (1+r i)^q) ≤ α * (C i * ((n:ℝ)^q * ((a i)^q * (1+t)^q)))  :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowr (hC i)) hα
      _ = C i * (a i)^q * (1+t)^q := by dsimp [α]; field_simp
      _ ≤ _ := by
        unfold D
        rw [mul_assoc (C i * a i ^ q)]
        exact mul_le_mul_of_nonneg_left htime (mul_nonneg (hC i) (Real.rpow_nonneg hA0 _))
  let K (ω : Ω) : ℝ≥0∞ := ((k:ℝ≥0∞)^p * ENNReal.ofReal α) * ∑ i, J i ω
  have hsK (ω : Ω) : (supDist (M.Ahat n ω) (fun _ => 0) t)^p ≤ K ω := by
    apply (ENNReal.le_rpow_inv_iff hp).1
    unfold supDist
    apply iSup₂_le
    intro s hs0
    apply (ENNReal.le_rpow_inv_iff hp).2
    simp only [Pi.zero_apply, sub_zero]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    refine (fin_vector_rpow_le _ _ hp).trans ?_
    unfold K
    rw [mul_assoc]
    apply mul_le_mul_right
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hsi : M.lamN n i * s ∈ Set.Icc 0 (r i) :=
      ⟨mul_nonneg (M.lamN_pos n i).le hs0.1, mul_le_mul_of_nonneg_left hs0.2 (M.lamN_pos n i).le⟩
    have hbound : (ENNReal.ofReal |M.A n i ω s - M.lamN n i*s|)^p ≤ J i ω := by
      rw [renewal_on_rate_clock]
      exact (le_iSup₂_of_le (M.lamN n i * s) hsi le_rfl).trans (hJp i ω)
    unfold SystemSequence.Ahat
    rw [abs_div, abs_of_pos hs, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hs.le),
      ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hs.le) hp.le, hαs]
    exact mul_le_mul_right hbound _
  refine (lintegral_mono hsK).trans ?_
  unfold K
  have hkn : (k:ℝ≥0∞)^p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le (ENNReal.natCast_ne_top k)
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hkn ENNReal.ofReal_ne_top),
    lintegral_finsetSum (f := J) Finset.univ (fun i _ => hJm i), mul_assoc]
  rw [Finset.mul_sum (a := ENNReal.ofReal α)]
  calc
    _ ≤ (k:ℝ≥0∞)^p * ∑ i, ENNReal.ofReal (D i*(1+t^q)) := by
      exact mul_le_mul_right (Finset.sum_le_sum fun i _ => hsJ i) _
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hD i) (add_nonneg zero_le_one (Real.rpow_nonneg ht _))), ← ENNReal.ofReal_natCast,
        ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) hp.le,
        ← ENNReal.ofReal_mul (by positivity), ← Finset.sum_mul, mul_assoc]
