-- Prove2me | solution 1 for KellyStochasticNetworks.EffectiveBandwidth.cramer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:56:27.915976+00:00
-- url     : https://prove2.me/submissions/a85feefb-7d42-47b5-b118-9bcc3f5b2f8b

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false




namespace X5CR

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

lemma mgf_eq (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (i : ℕ) (t : ℝ) :
    mgf (X i) P t = mgf (X 0) P t :=
  ((hident i).comp (u := fun x => Real.exp (t * x)) (by fun_prop)).integral_eq

lemma int_iff (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (i : ℕ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X i ω)) P ↔ Integrable (fun ω => Real.exp (t * X 0 ω)) P :=
  ((hident i).comp (u := fun x => Real.exp (t * x)) (by fun_prop)).integrable_iff

lemma cgf_sum (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) :
    cgf (∑ i ∈ Finset.range n, X i) P = fun t => (n : ℝ) * cgf (X 0) P t := by
  funext t
  simp only [cgf]
  rw [hindep.mgf_sum hmeas, Finset.prod_congr rfl (fun i _ => mgf_eq hident i t),
    Finset.prod_const, Finset.card_range, Real.log_pow]

lemma sub_int (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) :
    integrableExpSet (X 0) P ⊆ integrableExpSet (∑ i ∈ Finset.range n, X i) P := by
  intro t ht
  exact hindep.integrable_exp_mul_sum hmeas (fun i _ => (int_iff hident i t).2 ht)

lemma iter2 (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

variable {Y : Ω → ℝ}

lemma var_pos {c : ℝ} (hmean : ∫ ω, Y ω ∂P < c) (htail : 0 < P {ω | c < Y ω}) {s : ℝ}
    (hs : s ∈ interior (integrableExpSet Y P)) : 0 < iteratedDeriv 2 (cgf Y P) s := by
  rw [← variance_tilted_mul hs]
  have hL := memLp_tilted_mul hs 2
  rcases (variance_nonneg Y (P.tilted (s * Y ·))).lt_or_eq with h | h
  · exact h
  exfalso
  have hev : evariance Y (P.tilted (s * Y ·)) = 0 := by
    rw [← hL.ofReal_variance_eq, ← h, ENNReal.ofReal_zero]
  rw [evariance_eq_zero_iff hL.aestronglyMeasurable.aemeasurable] at hev
  set k := (P.tilted (s * Y ·))[Y]
  have hP : Y =ᵐ[P] fun _ => k :=
    (absolutelyContinuous_tilted (interior_subset (s := integrableExpSet Y P) hs)).ae_le hev
  have hmk : ∫ ω, Y ω ∂P = k := by
    rw [integral_congr_ae hP]; simp
  by_cases hck : c < k
  · linarith
  · have : P {ω | c < Y ω} = 0 := by
      apply measure_mono_null _ (ae_iff.1 hP)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      intro he; rw [he] at hω; exact hck hω
    rw [this] at htail; exact lt_irrefl _ htail

lemma strictMono_deriv {c : ℝ} (hmean : ∫ ω, Y ω ∂P < c) (htail : 0 < P {ω | c < Y ω}) :
    StrictMonoOn (deriv (cgf Y P)) (interior (integrableExpSet Y P)) := by
  apply strictMonoOn_of_deriv_pos convex_integrableExpSet.interior
  · intro x hx
    exact (analyticAt_cgf hx).deriv.continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_interior] at hx
    rw [← iter2]
    exact var_pos hmean htail hx

lemma M_eq {s : ℝ} (hs : Integrable (fun ω => Real.exp (s * Y ω)) P) :
    ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (s * Y ω)) ∂P) = ((cgf Y P s : ℝ) : EReal) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hs (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.log_ofReal_of_pos (mgf_pos hs)

end X5CR




namespace X5CR

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

lemma upper (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {s0 : ℝ} (hs0 : 0 ≤ s0)
    (hint : Integrable (fun ω => Real.exp (s0 * X 0 ω)) P) (c : ℝ) (n : ℕ) :
    P.real {ω | (n : ℝ) * c < ∑ i ∈ Finset.range n, X i ω} ≤
      Real.exp (n * (cgf (X 0) P s0 - c * s0)) := by
  set S := ∑ i ∈ Finset.range n, X i with hSdef
  have hS : ∀ ω, S ω = ∑ i ∈ Finset.range n, X i ω := fun ω => Finset.sum_apply _ _ _
  have hintS : Integrable (fun ω => Real.exp (s0 * S ω)) P := sub_int hmeas hindep hident n hint
  calc P.real {ω | (n : ℝ) * c < ∑ i ∈ Finset.range n, X i ω}
      ≤ P.real {ω | (n : ℝ) * c ≤ S ω} := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro ω hω
        simp only [Set.mem_setOf_eq, hS] at hω ⊢
        exact hω.le
    _ ≤ Real.exp (-s0 * (n * c)) * mgf S P s0 := measure_ge_le_exp_mul_mgf _ hs0 hintS
    _ = Real.exp (n * (cgf (X 0) P s0 - c * s0)) := by
        rw [← exp_cgf hintS, hSdef, cgf_sum hmeas hindep hident, ← Real.exp_add]
        congr 1; ring

lemma lower (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) {c s m θ : ℝ}
    (hs : s ∈ interior (integrableExpSet (X 0) P)) (hspos : 0 < s)
    (hm : deriv (cgf (X 0) P) s = m) (hcm : c < m) (hθ : 0 < θ) (n : ℕ) (hn : 0 < n) :
    (1 - iteratedDeriv 2 (cgf (X 0) P) s / (n * (min (m - c) θ) ^ 2)) *
        Real.exp (n * (cgf (X 0) P s - s * (m + θ))) ≤
      P.real {ω | (n : ℝ) * c < ∑ i ∈ Finset.range n, X i ω} := by
  set S := ∑ i ∈ Finset.range n, X i with hSdef
  have hS : ∀ ω, S ω = ∑ i ∈ Finset.range n, X i ω := fun ω => Finset.sum_apply _ _ _
  have hSm : Measurable S := by
    have := Finset.measurable_sum (Finset.range n) (fun i _ => hmeas i)
    simpa only [← Finset.sum_apply] using this
  have hsS : s ∈ interior (integrableExpSet S P) :=
    interior_mono (sub_int hmeas hindep hident n) hs
  have hintS : Integrable (fun ω => Real.exp (s * S ω)) P :=
    interior_subset (s := integrableExpSet S P) hsS
  set Q := P.tilted (s * S ·) with hQ
  have : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hintS
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set v := iteratedDeriv 2 (cgf (X 0) P) s
  have hmean : Q[S] = n * m := by
    rw [hQ, integral_tilted_mul_self hsS, hSdef, cgf_sum hmeas hindep hident,
      deriv_const_mul_field']
    beta_reduce; rw [hm]
  have hvar : Var[S; Q] = n * v := by
    rw [hQ, variance_tilted_mul hsS, hSdef, cgf_sum hmeas hindep hident,
      iteratedDeriv_const_mul_field]
  set η := min (m - c) θ with hη
  have hηpos : 0 < η := lt_min (by linarith) hθ
  have hη1 : η ≤ m - c := min_le_left _ _
  have hη2 : η ≤ θ := min_le_right _ _
  have hnη : 0 < n * η := mul_pos hnpos hηpos
  set B := {ω | (n : ℝ) * c < S ω ∧ S ω < n * (m + θ)} with hB
  set Bad := {ω | n * η ≤ |S ω - Q[S]|} with hBad
  have hBm : MeasurableSet B :=
    (measurableSet_lt measurable_const hSm).inter (measurableSet_lt hSm measurable_const)
  -- Chebyshev under the tilt
  have hcheb : Q.real Bad ≤ v / (n * η ^ 2) := by
    have h1 := meas_ge_le_variance_div_sq (memLp_tilted_mul hsS 2) hnη
    have h2 : Var[S; Q] / (n * η) ^ 2 = v / (n * η ^ 2) := by
      rw [hvar]; field_simp
    rw [h2] at h1
    have hv : 0 ≤ v := by
      rw [show v = _ from (variance_tilted_mul hs).symm]; exact variance_nonneg _ _
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hv (by positivity)) h1
  have hcover : (Set.univ : Set Ω) ⊆ B ∪ Bad := by
    intro ω _
    by_cases h : ω ∈ Bad
    · exact Or.inr h
    · left
      simp only [hBad, Set.mem_setOf_eq, not_le, hmean] at h
      rw [abs_lt] at h
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hη1 hnpos.le]
      · nlinarith [mul_le_mul_of_nonneg_left hη2 hnpos.le]
  have hQB : 1 - v / (n * η ^ 2) ≤ Q.real B := by
    have := (measureReal_mono hcover (by finiteness)).trans (measureReal_union_le (μ := Q) B Bad)
    rw [probReal_univ] at this
    linarith
  -- change of measure
  set E := Real.exp (s * (n * (m + θ)) - n * cgf (X 0) P s)
  have hQle : Q B ≤ ENNReal.ofReal E * P B := by
    rw [hQ, tilted_mul_apply_cgf B hintS, ← setLIntegral_const]
    apply setLIntegral_mono' hBm
    intro ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    rw [hSdef, cgf_sum hmeas hindep hident]
    have : s * S ω ≤ s * (n * (m + θ)) := mul_le_mul_of_nonneg_left hω.2.le hspos.le
    simp only [hSdef] at this
    linarith
  have hQle' : Q.real B ≤ E * P.real B := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hQle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hEinv : Real.exp (n * (cgf (X 0) P s - s * (m + θ))) * E = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2; ring
  have hBA : P.real B ≤ P.real {ω | (n : ℝ) * c < ∑ i ∈ Finset.range n, X i ω} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq, ← hS]
    exact hω.1
  have hexp := Real.exp_pos (n * (cgf (X 0) P s - s * (m + θ)))
  calc (1 - v / (n * η ^ 2)) * Real.exp (n * (cgf (X 0) P s - s * (m + θ)))
      ≤ Q.real B * Real.exp (n * (cgf (X 0) P s - s * (m + θ))) :=
        mul_le_mul_of_nonneg_right hQB hexp.le
    _ ≤ (E * P.real B) * Real.exp (n * (cgf (X 0) P s - s * (m + θ))) :=
        mul_le_mul_of_nonneg_right hQle' hexp.le
    _ = P.real B := by rw [mul_comm E, mul_assoc, mul_comm E, hEinv, mul_one]
    _ ≤ _ := hBA

end X5CR




namespace X5CR

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}

lemma hasDeriv_cgf {Y : Ω → ℝ} {s : ℝ} (hs : s ∈ interior (integrableExpSet Y P)) :
    HasDerivAt (cgf Y P) (deriv (cgf Y P) s) s :=
  (analyticAt_cgf hs).differentiableAt.hasDerivAt

/-- Real-valued core: positivity of the probabilities and the limit of the normalized logs. -/
lemma core (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (c : ℝ) (hmean : ∫ ω, X 0 ω ∂P < c)
    (htail : 0 < P {ω | c < X 0 ω}) {s0 : ℝ} (hs0 : 0 ≤ s0)
    (hI0 : (0 : ℝ) ∈ interior (integrableExpSet (X 0) P))
    (hIs : s0 ∈ interior (integrableExpSet (X 0) P))
    (hmin : ∀ s ∈ integrableExpSet (X 0) P, 0 ≤ s →
      cgf (X 0) P s0 - c * s0 ≤ cgf (X 0) P s - c * s) :
    (∀ᶠ N : ℕ in atTop, 0 < P.real {ω | ((N + 1 : ℕ) : ℝ) * c < ∑ i ∈ Finset.range (N + 1), X i ω}) ∧
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹ *
        Real.log (P.real {ω | ((N + 1 : ℕ) : ℝ) * c < ∑ i ∈ Finset.range (N + 1), X i ω}))
      atTop (𝓝 (cgf (X 0) P s0 - c * s0)) := by
  set I := interior (integrableExpSet (X 0) P) with hI
  set L := cgf (X 0) P s0 - c * s0 with hL
  set h : ℝ → ℝ := fun s => cgf (X 0) P s - c * s with hh
  have hIopen : IsOpen I := isOpen_interior
  have hD : ∀ s ∈ I, HasDerivAt h (deriv (cgf (X 0) P) s - c) s := by
    intro s hs
    have := (hasDeriv_cgf hs).sub ((hasDerivAt_id s).const_mul c)
    rw [mul_one] at this; exact this
  -- s0 > 0
  have hd0 : deriv (cgf (X 0) P) 0 = ∫ ω, X 0 ω ∂P := by
    rw [deriv_cgf_zero hI0]; simp
  have hs0pos : 0 < s0 := by
    rcases hs0.lt_or_eq with h' | h'
    · exact h'
    exfalso
    have ht := (hD 0 hI0).tendsto_slope_zero_right
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ t⁻¹ • (h (0 + t) - h 0) := by
      have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ I :=
        nhdsWithin_le_nhds (hIopen.mem_nhds hI0)
      filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht2
      rw [zero_add, smul_eq_mul]
      apply mul_nonneg (inv_nonneg.2 (le_of_lt ht2))
      have := hmin t (interior_subset ht1) (le_of_lt ht2)
      have hL0 : L = cgf (X 0) P 0 - c * 0 := by rw [hL, ← h']
      simp only [hh]; linarith
    have := ge_of_tendsto ht hev
    rw [hd0] at this; linarith
  -- first-order condition
  have hdc : deriv (cgf (X 0) P) s0 = c := by
    have hloc : IsLocalMin h s0 := by
      have : I ∩ Set.Ioi 0 ∈ 𝓝 s0 :=
        Filter.inter_mem (hIopen.mem_nhds hIs) (Ioi_mem_nhds hs0pos)
      filter_upwards [this] with t ht
      exact hmin t (interior_subset ht.1) (le_of_lt ht.2)
    have := hloc.hasDerivAt_eq_zero (hD s0 hIs)
    linarith
  -- strict monotonicity of the tilted mean
  have hsm := strictMono_deriv hmean htail
  -- lower-bound family
  have hlow : ∀ η > 0, ∀ᶠ N : ℕ in atTop,
      0 < P.real {ω | ((N + 1 : ℕ) : ℝ) * c < ∑ i ∈ Finset.range (N + 1), X i ω} ∧
      L - η < ((N + 1 : ℕ) : ℝ)⁻¹ *
        Real.log (P.real {ω | ((N + 1 : ℕ) : ℝ) * c < ∑ i ∈ Finset.range (N + 1), X i ω}) := by
    intro η hη
    set g : ℝ → ℝ := fun s => cgf (X 0) P s - s * deriv (cgf (X 0) P) s with hg
    have hgc : ContinuousAt g s0 := by
      apply ContinuousAt.sub (analyticAt_cgf hIs).continuousAt
      exact continuousAt_id.mul (analyticAt_cgf hIs).deriv.continuousAt
    have hgs0 : g s0 = L := by simp only [hg, hL, hdc]; ring
    have hnb : {s | s ∈ I ∧ L - η / 3 < g s} ∈ 𝓝 s0 := by
      apply Filter.inter_mem (hIopen.mem_nhds hIs)
      have := hgc.eventually (lt_mem_nhds (show L - η / 3 < g s0 by rw [hgs0]; linarith))
      exact this
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnb
    set s := s0 + ε / 2 with hsdef
    have hsb : s ∈ Metric.ball s0 ε := by
      rw [Metric.mem_ball, Real.dist_eq, hsdef]; rw [abs_of_pos (by linarith)]; linarith
    obtain ⟨hsI, hgs⟩ := hball hsb
    have hspos : 0 < s := by linarith
    set m := deriv (cgf (X 0) P) s with hmdef
    have hcm : c < m := by rw [← hdc]; exact hsm hIs hsI (by linarith)
    set θ := η / (3 * s) with hθdef
    have hθ : 0 < θ := by positivity
    have hsθ : s * θ = η / 3 := by rw [hθdef]; field_simp
    set v := iteratedDeriv 2 (cgf (X 0) P) s
    set η0 := min (m - c) θ
    have hη0 : 0 < η0 := lt_min (by linarith) hθ
    -- eventually the Chebyshev factor is ≥ 1/2 and log 2 / n < η/3
    have hA : ∀ᶠ N : ℕ in atTop, v / (((N + 1 : ℕ) : ℝ) * η0 ^ 2) ≤ 1 / 2 ∧
        Real.log 2 / ((N + 1 : ℕ) : ℝ) < η / 3 := by
      have t1 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      have t2 : Tendsto (fun N : ℕ => v / (((N + 1 : ℕ) : ℝ) * η0 ^ 2)) atTop (𝓝 0) := by
        have := (t1.atTop_mul_const (pow_pos hη0 2)).const_div_atTop v
        exact this
      have t3 : Tendsto (fun N : ℕ => Real.log 2 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
        t1.const_div_atTop _
      exact (t2.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1 / 2))).and
        (t3.eventually (gt_mem_nhds (by linarith : (0:ℝ) < η / 3)))
    filter_upwards [hA] with N hN
    set n : ℝ := ((N + 1 : ℕ) : ℝ) with hn
    have hnpos : 0 < n := by rw [hn]; positivity
    have hlb := lower hmeas hindep hident hsI hspos hmdef.symm hcm hθ (N + 1) (Nat.succ_pos N)
    set p := P.real {ω | n * c < ∑ i ∈ Finset.range (N + 1), X i ω}
    have hE := Real.exp_pos (n * (cgf (X 0) P s - s * (m + θ)))
    have hp : (1 / 2) * Real.exp (n * (cgf (X 0) P s - s * (m + θ))) ≤ p :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith [hN.1]) hE.le) hlb
    have hppos : 0 < p := lt_of_lt_of_le (by positivity) hp
    refine ⟨hppos, ?_⟩
    have hlog := Real.log_le_log (by positivity) hp
    rw [Real.log_mul (by norm_num) hE.ne', Real.log_exp, one_div, Real.log_inv] at hlog
    have hgs' : g s = cgf (X 0) P s - s * m := rfl
    have h2 : Real.log 2 < n * (η / 3) := by
      have := hN.2; rw [div_lt_iff₀ hnpos] at this; linarith
    rw [lt_inv_mul_iff₀ hnpos]
    nlinarith
  refine ⟨(hlow 1 one_pos).mono (fun N hN => hN.1), ?_⟩
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hlow (L - a) (by linarith)] with N hN
    linarith [hN.2]
  · filter_upwards [hlow 1 one_pos] with N hN
    have hu := upper hmeas hindep hident hs0 (interior_subset (s := integrableExpSet (X 0) P) hIs)
      c (N + 1)
    have hnpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have := Real.log_le_log hN.1 hu
    rw [Real.log_exp] at this
    have : ((N + 1 : ℕ) : ℝ)⁻¹ *
        Real.log (P.real {ω | ((N + 1 : ℕ) : ℝ) * c < ∑ i ∈ Finset.range (N + 1), X i ω}) ≤ L := by
      rw [inv_mul_le_iff₀ hnpos]; exact this
    linarith

end X5CR



open X5CR in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (c : ℝ) (hmean : ∫ ω, X 0 ω ∂P < c)
    (htail : 0 < P {ω | c < X 0 ω})
    (hlocal : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      Integrable (fun ω => Real.exp (s * X 0 ω)) P) :
    let M : ℝ → EReal := fun s =>
      ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (s * X 0 ω)) ∂P)
    (∃ sStar : ℝ, 0 ≤ sStar ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - sStar| < δ →
        Integrable (fun ω => Real.exp (s * X 0 ω)) P) ∧
      (∀ s : ℝ, 0 ≤ s → M sStar - ((c * sStar : ℝ) : EReal) ≤
        M s - ((c * s : ℝ) : EReal))) →
    Tendsto
      (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : EReal) *
        ENNReal.log (P {ω | ((N + 1 : ℕ) : ℝ) * c <
          ∑ i ∈ Finset.range (N + 1), X i ω})))
      atTop (𝓝 (⨅ s : {s : ℝ // 0 ≤ s}, M s.val - ((c * s.val : ℝ) : EReal))) := by
  intro M hstar
  obtain ⟨s0, hs0, ⟨δ, hδ, hint⟩, hmin⟩ := hstar
  obtain ⟨δ0, hδ0, hloc⟩ := hlocal
  have hIs : s0 ∈ interior (integrableExpSet (X 0) P) := by
    apply mem_interior_iff_mem_nhds.2
    apply Filter.mem_of_superset (Metric.ball_mem_nhds s0 hδ)
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact hint s hs
  have hI0 : (0 : ℝ) ∈ interior (integrableExpSet (X 0) P) := by
    apply mem_interior_iff_mem_nhds.2
    apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 hδ0)
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
    exact hloc s hs
  have hM : ∀ s ∈ integrableExpSet (X 0) P, M s = ((cgf (X 0) P s : ℝ) : EReal) :=
    fun s hs => M_eq hs
  have hs0I : s0 ∈ integrableExpSet (X 0) P := interior_subset hIs
  have hminR : ∀ s ∈ integrableExpSet (X 0) P, 0 ≤ s →
      cgf (X 0) P s0 - c * s0 ≤ cgf (X 0) P s - c * s := by
    intro s hs hs'
    have := hmin s hs'
    rw [hM s hs, hM s0 hs0I, ← EReal.coe_sub, ← EReal.coe_sub] at this
    exact EReal.coe_le_coe_iff.1 this
  have hinf : (⨅ s : {s : ℝ // 0 ≤ s}, M s.val - ((c * s.val : ℝ) : EReal)) =
      ((cgf (X 0) P s0 - c * s0 : ℝ) : EReal) := by
    apply le_antisymm
    · apply iInf_le_of_le ⟨s0, hs0⟩
      rw [hM s0 hs0I, ← EReal.coe_sub]
    · exact le_iInf fun s => by
        have := hmin s.1 s.2
        rwa [hM s0 hs0I, ← EReal.coe_sub] at this
  obtain ⟨hpos, hlim⟩ := core hmeas hindep hident c hmean htail hs0 hI0 hIs hminR
  rw [hinf]
  refine ((continuous_coe_real_ereal.tendsto _).comp hlim).congr' ?_
  filter_upwards [hpos] with N hN
  simp only [Function.comp]
  rw [← ofReal_measureReal (measure_ne_top _ _), ENNReal.log_ofReal_of_pos hN, ← EReal.coe_inv, ← EReal.coe_mul]

