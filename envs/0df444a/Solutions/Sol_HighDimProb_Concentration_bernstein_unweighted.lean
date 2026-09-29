-- Prove2me | solution 1 for HighDimProb.Concentration.bernstein_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T22:27:35.357923+00:00
-- url     : https://prove2.me/submissions/997bda66-5ba4-4af2-8457-558693e93561

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Filter Topology

lemma hdpc_exp_le_quad (y : ℝ) : exp y ≤ 1 + y + y ^ 2 * exp |y| := by
  rcases le_or_gt |y| 1 with hy | hy
  · have h1 := Real.abs_exp_sub_one_sub_id_le hy
    have h3 := (abs_le.1 h1).2
    have h4 : 1 ≤ exp |y| := Real.one_le_exp (abs_nonneg y)
    have h5 : y ^ 2 ≤ y ^ 2 * exp |y| := le_mul_of_one_le_right (sq_nonneg y) h4
    linarith
  · have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have he : exp y ≤ exp |y| := exp_le_exp.2 (le_abs_self y)
    have h6 : exp |y| ≤ y ^ 2 * exp |y| := le_mul_of_one_le_left (exp_pos _).le hy2
    have h7 : |y| + 1 ≤ exp |y| := add_one_le_exp |y|
    rcases le_or_gt 0 y with h0 | h0
    · linarith
    · have h8 : exp y ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h9 : |y| = -y := abs_of_neg h0
      linarith

lemma hdpc_sq_le_exp (u : ℝ) (hu : 0 ≤ u) : u ^ 2 ≤ 16 * exp (u / 2) := by
  have h1 : u / 4 ≤ exp (u / 4) := by linarith [add_one_le_exp (u / 4)]
  have h2 : exp (u / 2) = exp (u / 4) * exp (u / 4) := by rw [← exp_add]; ring_nf
  have h3 : 0 ≤ u / 4 := by positivity
  have h4 := mul_le_mul h1 h1 h3 (exp_pos _).le
  nlinarith

lemma hdpc_subE_mgf {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0) (s : ℝ) (hs : 0 < s)
    (hint : Integrable (fun ω => exp (|Y ω| / s)) P)
    (hle : ∫ ω, exp (|Y ω| / s) ∂P ≤ 2) (l : ℝ) (hl : |l| * s ≤ 1 / 2) :
    Integrable (fun ω => exp (l * Y ω)) P ∧ mgf Y P l ≤ exp (32 * l ^ 2 * s ^ 2) := by
  have hpt : ∀ ω, exp (l * Y ω) ≤ 1 + l * Y ω + 16 * l ^ 2 * s ^ 2 * exp (|Y ω| / s) ∧
      exp (l * Y ω) ≤ exp (|Y ω| / s) ∧ |Y ω| ≤ s * exp (|Y ω| / s) := by
    intro ω
    set u := |Y ω| / s with hu
    have hu0 : 0 ≤ u := div_nonneg (abs_nonneg _) hs.le
    have hYu : |Y ω| = s * u := by rw [hu]; field_simp
    have hsq : Y ω ^ 2 = s ^ 2 * u ^ 2 := by rw [← sq_abs, hYu]; ring
    have hlu : |l * Y ω| ≤ u / 2 := by
      rw [abs_mul, hYu]
      nlinarith [abs_nonneg l, mul_le_mul_of_nonneg_right hl hu0]
    have h1 := hdpc_exp_le_quad (l * Y ω)
    have h2 : exp |l * Y ω| ≤ exp (u / 2) := exp_le_exp.2 hlu
    have h3 := hdpc_sq_le_exp u hu0
    have h4 : exp u = exp (u / 2) * exp (u / 2) := by rw [← exp_add]; ring_nf
    have h5 : (l * Y ω) ^ 2 * exp |l * Y ω| ≤ 16 * l ^ 2 * s ^ 2 * exp u := by
      rw [mul_pow, hsq, h4]
      have hA : 0 ≤ l ^ 2 * s ^ 2 := by positivity
      calc l ^ 2 * (s ^ 2 * u ^ 2) * exp |l * Y ω|
          = (l ^ 2 * s ^ 2) * (u ^ 2 * exp |l * Y ω|) := by ring
        _ ≤ (l ^ 2 * s ^ 2) * ((16 * exp (u / 2)) * exp (u / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact mul_le_mul h3 h2 (exp_pos _).le (by positivity)
        _ = 16 * l ^ 2 * s ^ 2 * (exp (u / 2) * exp (u / 2)) := by ring
    refine ⟨by linarith, ?_, ?_⟩
    · apply exp_le_exp.2
      have := le_abs_self (l * Y ω)
      linarith
    · rw [hYu]
      have := add_one_le_exp u
      nlinarith
  have hintE : Integrable (fun ω => exp (l * Y ω)) P := by
    refine Integrable.mono' hint ((hY.const_mul l).exp.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact (hpt ω).2.1
  have hYint : Integrable Y P := by
    refine Integrable.mono' (hint.const_mul s) hY.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact (hpt ω).2.2
  refine ⟨hintE, ?_⟩
  have hI1 : Integrable (fun ω => 1 + l * Y ω) P := (integrable_const _).add (hYint.const_mul l)
  have hI2 : Integrable (fun ω => 16 * l ^ 2 * s ^ 2 * exp (|Y ω| / s)) P := hint.const_mul _
  rw [mgf]
  calc ∫ ω, exp (l * Y ω) ∂P
      ≤ ∫ ω, (1 + l * Y ω + 16 * l ^ 2 * s ^ 2 * exp (|Y ω| / s)) ∂P :=
        integral_mono hintE (hI1.add hI2) (fun ω => (hpt ω).1)
    _ = 1 + l * ∫ ω, Y ω ∂P + 16 * l ^ 2 * s ^ 2 * ∫ ω, exp (|Y ω| / s) ∂P := by
        rw [integral_add hI1 hI2, integral_add (integrable_const _) (hYint.const_mul l),
          integral_const_mul, integral_const_mul, integral_const]
        simp
    _ ≤ 1 + 32 * l ^ 2 * s ^ 2 := by
        rw [hmean]
        have hq0 : 0 ≤ 16 * l ^ 2 * s ^ 2 := by positivity
        nlinarith
    _ ≤ exp (32 * l ^ 2 * s ^ 2) := by linarith [add_one_le_exp (32 * l ^ 2 * s ^ 2)]

open HighDimProb.Concentration in
lemma hdpc_subE_norm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0)
    (hsg : ∃ s > 0, Integrable (fun ω => Real.exp (|Y ω| / s)) P ∧
      ∫ ω, Real.exp (|Y ω| / s) ∂P ≤ 2)
    (l : ℝ) (hl : |l| * (4 * subexponentialNorm P Y) ≤ 1) :
    Integrable (fun ω => exp (l * Y ω)) P ∧
      mgf Y P l ≤ exp (128 * l ^ 2 * subexponentialNorm P Y ^ 2) := by
  obtain ⟨s0, hs0, hint0, hle0⟩ := hsg
  have hne : ({s : ℝ | 0 < s ∧ Integrable (fun ω => Real.exp (|Y ω| / s)) P ∧
      ∫ ω, Real.exp (|Y ω| / s) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hint0, hle0⟩
  have hprop : ∀ s, subexponentialNorm P Y < s →
      Integrable (fun ω => exp (|Y ω| / s)) P ∧ ∫ ω, exp (|Y ω| / s) ∂P ≤ 2 := by
    intro s hs
    unfold subexponentialNorm at hs
    obtain ⟨s1, ⟨hs1, hint1, hle1⟩, hs1s⟩ := exists_lt_of_csInf_lt hne hs
    have hmono : ∀ ω, exp (|Y ω| / s) ≤ exp (|Y ω| / s1) := fun ω =>
      exp_le_exp.2 (div_le_div_of_nonneg_left (abs_nonneg _) hs1 hs1s.le)
    have hint2 : Integrable (fun ω => exp (|Y ω| / s)) P :=
      hint1.mono' ((hY.abs.div_const _).exp.aestronglyMeasurable)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
    exact ⟨hint2, (integral_mono hint2 hint1 hmono).trans hle1⟩
  have hν0 : 0 ≤ subexponentialNorm P Y := Real.sInf_nonneg (fun x hx => hx.1.le)
  rcases hν0.lt_or_eq with hpos | hzero
  · obtain ⟨h1, h2⟩ := hprop (2 * subexponentialNorm P Y) (by linarith)
    have h := hdpc_subE_mgf P Y hY hmean (2 * subexponentialNorm P Y) (by linarith) h1 h2 l
      (by linarith)
    refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
    congr 1
    ring
  · have hs1 : (0 : ℝ) < 1 / (2 * |l| + 1) := by positivity
    have hsmall : ∀ s, 0 < s → s < 1 / (2 * |l| + 1) → |l| * s ≤ 1 / 2 := by
      intro s hs hs'
      rw [lt_div_iff₀ (by positivity)] at hs'
      nlinarith [abs_nonneg l]
    obtain ⟨hA1, hA2⟩ := hprop (1 / (2 * (2 * |l| + 1))) (by rw [← hzero]; positivity)
    have hI := (hdpc_subE_mgf P Y hY hmean (1 / (2 * (2 * |l| + 1))) (by positivity) hA1 hA2 l
      (hsmall _ (by positivity) (by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [abs_nonneg l]))).1
    refine ⟨hI, ?_⟩
    have hlim : Tendsto (fun s : ℝ => exp (32 * l ^ 2 * s ^ 2)) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun s : ℝ => exp (32 * l ^ 2 * s ^ 2)) := by fun_prop
      exact (hc.tendsto' 0 1 (by simp)).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), mgf Y P l ≤ exp (32 * l ^ 2 * s ^ 2) := by
      filter_upwards [Ioo_mem_nhdsGT hs1] with s hs
      obtain ⟨h1, h2⟩ := hprop s (by rw [← hzero]; exact hs.1)
      exact (hdpc_subE_mgf P Y hY hmean s hs.1 h1 h2 l (hsmall s hs.1 hs.2)).2
    have h := ge_of_tendsto hlim hev
    rw [← hzero]
    simpa using h

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration in
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N : ℕ} (X : Fin N → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp (|X i ω| / s)) P ∧
                       ∫ ω, Real.exp (|X i ω| / s) ∂P ≤ 2) →
        ∀ {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, X i ω|} ≤
          2 * Real.exp (-(c * min
            (t ^ 2 / ∑ i, (subexponentialNorm P (X i)) ^ 2)
            (t / ⨆ i, subexponentialNorm P (X i)))) := by
  refine ⟨1 / 512, by norm_num, ?_⟩
  intro Ω _ P _ N X hX_meas hX_indep hmean hsg t ht
  set M := ⨆ i, subexponentialNorm P (X i) with hM
  set V := ∑ i, (subexponentialNorm P (X i)) ^ 2 with hV
  have hP1 : P.real {ω | t ≤ |∑ i, X i ω|} ≤ 1 := measureReal_le_one
  have hnn : ∀ i, 0 ≤ subexponentialNorm P (X i) := fun i =>
    Real.sInf_nonneg (fun x hx => hx.1.le)
  have hbdd : BddAbove (Set.range fun i => subexponentialNorm P (X i)) :=
    (Set.finite_range _).bddAbove
  have hleM : ∀ i, subexponentialNorm P (X i) ≤ M := fun i => le_ciSup hbdd i
  have hM0 : 0 ≤ M := Real.iSup_nonneg hnn
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hdeg : V = 0 ∨ M = 0
  · have hmin : min (t ^ 2 / V) (t / M) = 0 := by
      rcases hdeg with h | h
      · rw [h, div_zero]; exact min_eq_left (div_nonneg ht hM0)
      · rw [h, div_zero]; exact min_eq_right (div_nonneg (sq_nonneg t) hV0)
    rw [hmin, mul_zero, neg_zero, exp_zero]; linarith
  rw [not_or] at hdeg
  have hVpos : 0 < V := lt_of_le_of_ne hV0 (Ne.symm hdeg.1)
  have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hdeg.2)
  set l := min (t / (256 * V)) (1 / (4 * M)) with hl
  have hl0 : 0 ≤ l := le_min (by positivity) (by positivity)
  have hl1 : l ≤ t / (256 * V) := min_le_left _ _
  have hl2 : l ≤ 1 / (4 * M) := min_le_right _ _
  have hlM : l * (4 * M) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hl2; linarith
  have hmgf : ∀ i (r : ℝ), |r| = l → Integrable (fun ω => exp (r * X i ω)) P ∧
      mgf (X i) P r ≤ exp (128 * l ^ 2 * subexponentialNorm P (X i) ^ 2) := by
    intro i r hr
    have h := hdpc_subE_norm P (X i) (hX_meas i) (hmean i) (hsg i) r (by
      rw [hr]; nlinarith [mul_le_mul_of_nonneg_left (hleM i) hl0])
    rw [← sq_abs r, hr] at h
    exact h
  have hsumV : ∑ i, 128 * l ^ 2 * subexponentialNorm P (X i) ^ 2 = 128 * l ^ 2 * V := by
    rw [hV, Finset.mul_sum]
  have hup : P.real {ω | t ≤ ∑ i, X i ω} ≤ exp (-l * t + 128 * l ^ 2 * V) := by
    have hint : Integrable (fun ω => exp (l * (∑ i, X i) ω)) P :=
      hX_indep.integrable_exp_mul_sum hX_meas (fun i _ => (hmgf i l (abs_of_nonneg hl0)).1)
    have h1 := measure_ge_le_exp_mul_mgf (X := ∑ i, X i) t hl0 hint
    have hset : {ω | t ≤ ∑ i, X i ω} = {ω | t ≤ (∑ i, X i) ω} := by
      ext ω; simp [Finset.sum_apply]
    rw [hset]
    refine h1.trans ?_
    rw [hX_indep.mgf_sum hX_meas, exp_add]
    gcongr
    rw [← hsumV, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => mgf_nonneg)
      (fun i _ => (hmgf i l (abs_of_nonneg hl0)).2)
  have hdown : P.real {ω | ∑ i, X i ω ≤ -t} ≤ exp (-l * t + 128 * l ^ 2 * V) := by
    have hr : |-l| = l := by rw [abs_neg, abs_of_nonneg hl0]
    have hint : Integrable (fun ω => exp ((-l) * (∑ i, X i) ω)) P :=
      hX_indep.integrable_exp_mul_sum hX_meas (fun i _ => (hmgf i (-l) hr).1)
    have h1 := measure_le_le_exp_mul_mgf (X := ∑ i, X i) (-t) (by linarith : -l ≤ 0) hint
    have hset : {ω | ∑ i, X i ω ≤ -t} = {ω | (∑ i, X i) ω ≤ -t} := by
      ext ω; simp [Finset.sum_apply]
    rw [hset]
    refine h1.trans ?_
    rw [hX_indep.mgf_sum hX_meas, show -(-l) * -t = -l * t by ring, exp_add]
    gcongr
    rw [← hsumV, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hmgf i (-l) hr).2)
  have hexpo : -l * t + 128 * l ^ 2 * V ≤ -(1 / 512 * min (t ^ 2 / V) (t / M)) := by
    have h1 : l * (256 * V) ≤ t := (le_div_iff₀ (by positivity)).1 hl1
    have h2 : 128 * l ^ 2 * V ≤ l * t / 2 := by nlinarith [mul_le_mul_of_nonneg_left h1 hl0]
    have h3 : min (t ^ 2 / V) (t / M) / 512 ≤ l * t / 2 := by
      rcases min_choice (t / (256 * V)) (1 / (4 * M)) with h | h
      · rw [← hl] at h
        rw [h]
        have h5 : min (t ^ 2 / V) (t / M) ≤ t ^ 2 / V := min_le_left _ _
        have e : t / (256 * V) * t / 2 = t ^ 2 / V / 512 := by ring
        rw [e]; linarith
      · rw [← hl] at h
        rw [h]
        have h5 : min (t ^ 2 / V) (t / M) ≤ t / M := min_le_right _ _
        have e : 1 / (4 * M) * t / 2 = t / M / 8 := by ring
        rw [e]
        have h6 : 0 ≤ t / M := div_nonneg ht hMpos.le
        linarith
    linarith
  have hsplit : {ω | t ≤ |∑ i, X i ω|} ⊆ {ω | t ≤ ∑ i, X i ω} ∪ {ω | ∑ i, X i ω ≤ -t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_abs.1 hω with h | h
    · exact Or.inl h
    · right; linarith
  calc P.real {ω | t ≤ |∑ i, X i ω|}
      ≤ P.real ({ω | t ≤ ∑ i, X i ω} ∪ {ω | ∑ i, X i ω ≤ -t}) := measureReal_mono hsplit
    _ ≤ P.real {ω | t ≤ ∑ i, X i ω} + P.real {ω | ∑ i, X i ω ≤ -t} := measureReal_union_le _ _
    _ ≤ exp (-l * t + 128 * l ^ 2 * V) + exp (-l * t + 128 * l ^ 2 * V) := add_le_add hup hdown
    _ ≤ 2 * exp (-(1 / 512 * min (t ^ 2 / V) (t / M))) := by
        have := exp_le_exp.2 hexpo
        linarith
