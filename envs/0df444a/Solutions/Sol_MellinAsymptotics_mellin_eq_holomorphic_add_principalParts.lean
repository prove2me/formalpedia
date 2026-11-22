-- Prove2me | solution 1 for MellinAsymptotics.mellin_eq_holomorphic_add_principalParts
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:48:29.388967+00:00
-- url     : https://prove2.me/submissions/88913b95-7f83-41c4-a9e3-1fc28a96bf87

import Mathlib

open MeasureTheory Filter Topology Asymptotics

set_option autoImplicit false

namespace Sol_MellinAsymptotics_mellin_eq_holomorphic_add_principalParts

open Set Complex

/-! ### Power-logarithm functions cut off at `1` -/

noncomputable def cpowLog (a : ℂ) (n : ℕ) : ℝ → ℂ :=
  fun t => (t : ℂ) ^ a * (Real.log t : ℂ) ^ n

noncomputable def cpowLogInd (a : ℂ) (n : ℕ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (cpowLog a n)

theorem continuousOn_cpowLog (a : ℂ) (n : ℕ) :
    ContinuousOn (cpowLog a n) (Ioi 0) := by
  refine ContinuousOn.mul ?_ ?_
  · intro t ht
    exact (continuousAt_ofReal_cpow_const t a (Or.inr (ne_of_gt ht))).continuousWithinAt
  · refine ContinuousOn.pow ?_ _
    exact continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)

theorem isBigO_cpowLog_nhdsGT (a : ℂ) (n : ℕ) {b : ℝ} (hb : -a.re < b) :
    cpowLog a n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  have hlim : Tendsto (fun t : ℝ => |Real.log t| ^ (n : ℝ) * t ^ (a.re + b)) (𝓝[>] 0)
      (𝓝 0) := by
    have hs : -(a.re + b) < 0 := by linarith
    refine (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n : ℝ) hs).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [div_eq_mul_inv, Real.rpow_neg ht.le, inv_inv]
  have hratio : (fun t : ℝ => ‖cpowLog a n t‖ / t ^ (-b)) =ᶠ[𝓝[>] 0]
      fun t => |Real.log t| ^ (n : ℝ) * t ^ (a.re + b) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [cpowLog, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_pow, norm_real,
      Real.norm_eq_abs]
    rw [div_eq_mul_inv, ← Real.rpow_natCast |Real.log t| n, Real.rpow_neg ht.le, inv_inv,
      mul_right_comm, ← Real.rpow_add ht]
    ac_rfl
  have hlim' := hlim.congr' hratio.symm
  filter_upwards [hlim'.eventually (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with t ht (hpos : 0 < t)
  have hden : 0 < t ^ (-b) := Real.rpow_pos_of_pos hpos _
  have hlt : ‖cpowLog a n t‖ / t ^ (-b) < 1 := ht
  rw [div_lt_one hden] at hlt
  have hnorm : ‖(t : ℝ) ^ (-b)‖ = t ^ (-b) :=
    Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)
  simpa [hnorm, one_mul] using hlt.le

theorem isBigO_cpowLogInd_nhdsGT (a : ℂ) (n : ℕ) {b : ℝ} (hb : -a.re < b) :
    cpowLogInd a n =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  have hEq : cpowLogInd a n =ᶠ[𝓝[>] (0 : ℝ)] cpowLog a n := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    simp [cpowLogInd, indicator_of_mem ht']
  exact (isBigO_cpowLog_nhdsGT a n hb).congr' hEq.symm .rfl

theorem isBigO_cpowLogInd_atTop (a : ℂ) (n : ℕ) (c : ℝ) :
    cpowLogInd a n =O[atTop] (fun t : ℝ => t ^ c) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  have hnot : t ∉ Ioc (0 : ℝ) 1 := fun h => lt_irrefl (1 : ℝ) (ht.trans_le h.2)
  simp [cpowLogInd, indicator_of_notMem hnot]

theorem locallyIntegrableOn_indicator {g : ℝ → ℂ} (hg : LocallyIntegrableOn g (Ioi 0))
    {T : Set ℝ} (hT : MeasurableSet T) :
    LocallyIntegrableOn (T.indicator g) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed] at hg ⊢
  intro k hk hkc
  exact (hg k hk hkc).indicator hT

theorem locallyIntegrableOn_cpowLogInd (a : ℂ) (n : ℕ) :
    LocallyIntegrableOn (cpowLogInd a n) (Ioi 0) :=
  locallyIntegrableOn_indicator
    ((continuousOn_cpowLog a n).locallyIntegrableOn measurableSet_Ioi) measurableSet_Ioc

theorem log_mul_cpowLogInd (a : ℂ) (n : ℕ) :
    (fun t : ℝ => (Real.log t : ℂ) * cpowLogInd a n t) = cpowLogInd a (n + 1) := by
  funext t
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [cpowLogInd, indicator_of_mem ht, cpowLog]
    ring
  · simp [cpowLogInd, indicator_of_notMem ht]

/-- `∫₀¹ t^{s+a-1} (log t)^n dt = (-1)^n n! (s+a)^{-n-1}` for `Re (s + a) > 0`. -/
theorem hasMellin_cpowLogInd (a : ℂ) (n : ℕ) {s : ℂ} (hs : 0 < s.re + a.re) :
    HasMellin (cpowLogInd a n) s
      ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (s + a) ^ (-(n : ℤ) - 1)) := by
  have hhalf : IsOpen {z : ℂ | 0 < z.re + a.re} := by
    have hEq : {z : ℂ | 0 < z.re + a.re} = (fun z : ℂ => z.re + a.re) ⁻¹' Ioi 0 := by
      ext z; rfl
    rw [hEq]
    exact isOpen_Ioi.preimage (continuous_re.add continuous_const)
  have key : ∀ n : ℕ, ∀ s : ℂ, 0 < s.re + a.re →
      HasMellin (cpowLogInd a n) s (iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h0 := hasMellin_cpow_Ioc a hs
      have hfun : cpowLogInd a 0 = (Ioc (0 : ℝ) 1).indicator (fun t : ℝ => (t : ℂ) ^ a) := by
        funext t
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · rw [cpowLogInd, indicator_of_mem ht, indicator_of_mem ht, cpowLog, pow_zero, mul_one]
        · rw [cpowLogInd, indicator_of_notMem ht, indicator_of_notMem ht]
      refine ⟨?_, ?_⟩
      · rw [hfun]; exact h0.1
      · rw [hfun, iteratedDeriv_zero, inv_eq_one_div]; exact h0.2
    | succ n ih =>
      intro s hs
      have hloc := locallyIntegrableOn_cpowLogInd a n
      have htop := isBigO_cpowLogInd_atTop a n (-(s.re + 1))
      set b0 : ℝ := (-a.re + s.re) / 2
      have hb0_lt : b0 < s.re := by dsimp [b0]; linarith
      have hb0_gt : -a.re < b0 := by dsimp [b0]; linarith
      have hbot := isBigO_cpowLogInd_nhdsGT a n hb0_gt
      have hder := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := b0)
        hloc htop (by linarith) hbot hb0_lt
      have hsmul := log_mul_cpowLogInd a n
      have hHas : HasDerivAt (mellin (cpowLogInd a n)) (mellin (cpowLogInd a (n + 1)) s) s := by
        simpa [hsmul, real_smul] using hder.2
      have hconv : MellinConvergent (cpowLogInd a (n + 1)) s := by
        simpa [hsmul, real_smul] using hder.1
      have hagree : mellin (cpowLogInd a n) =ᶠ[𝓝 s]
          iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) := by
        filter_upwards [hhalf.mem_nhds hs] with z hz
        exact (ih z hz).2
      refine ⟨hconv, ?_⟩
      rw [← hHas.deriv, hagree.deriv_eq, ← iteratedDeriv_succ]
  have hkey := key n s hs
  have hform : iteratedDeriv n (fun z : ℂ => (z + a)⁻¹) s =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (s + a) ^ (-(n : ℤ) - 1) := by
    rw [iteratedDeriv_eq_iterate]
    have hlin := congr_fun (iter_deriv_inv_linear n (1 : ℂ) a) s
    simpa [show (-1 - (n : ℤ) = -(n : ℤ) - 1) by ring] using hlin
  simpa [hform] using hkey

theorem hasMellin_finset_sum {ι : Type*} (p : Finset ι) (f : ι → ℝ → ℂ) (v : ι → ℂ)
    (s : ℂ) (h : ∀ i ∈ p, HasMellin (f i) s (v i)) :
    HasMellin (fun t => ∑ i ∈ p, f i t) s (∑ i ∈ p, v i) := by
  classical
  induction p using Finset.induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_empty, MellinConvergent, smul_zero]
      exact integrableOn_zero
    · simp [mellin, Finset.sum_empty]
  | insert i p hi ih =>
    have hfun : (fun t => ∑ j ∈ insert i p, f j t) = fun t => f i t + ∑ j ∈ p, f j t := by
      funext t
      rw [Finset.sum_insert hi]
    have hval : (∑ j ∈ insert i p, v j) = v i + ∑ j ∈ p, v j := Finset.sum_insert hi
    rw [hfun, hval]
    have hi' := h i (Finset.mem_insert_self i p)
    have hp := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have Hadd := hasMellin_add hi'.1 hp.1
    rw [hi'.2, hp.2] at Hadd
    exact Hadd

theorem exists_lt_withTop {x : ℝ} {b : WithTop ℝ} (hx : (x : WithTop ℝ) < b) :
    ∃ σ : ℝ, x < σ ∧ (σ : WithTop ℝ) < b := by
  cases b with
  | top =>
    exact ⟨x + 1, by linarith, WithTop.coe_lt_top _⟩
  | coe B =>
    have hxB : x < B := by simpa [WithTop.coe_lt_coe] using hx
    refine ⟨(x + B) / 2, by linarith, ?_⟩
    simpa [WithTop.coe_lt_coe] using (by linarith : (x + B) / 2 < B)

/-! ### Consequences of the convergence of a Mellin integral -/

theorem aestronglyMeasurable_of_mellinConvergent {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) : AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
  have h1 : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (1 - s) • ((t : ℂ) ^ (s - 1) • f t)) (volume.restrict (Ioi 0)) := by
    refine AEStronglyMeasurable.fun_smul ?_ hf.aestronglyMeasurable
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [smul_smul, ← cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht))]
  simp

theorem locallyIntegrableOn_of_mellinConvergent {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) : LocallyIntegrableOn f (Ioi 0) := by
  have h1 : LocallyIntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (1 - s) • ((t : ℂ) ^ (s - 1) • f t)) (Ioi 0) := by
    refine (hf.locallyIntegrableOn).continuousOn_smul isOpen_Ioi.isLocallyClosed ?_
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [smul_smul, ← cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht))]
  simp

theorem mellinConvergent_indicator {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s)
    {T : Set ℝ} (hT : MeasurableSet T) : MellinConvergent (T.indicator f) s := by
  have h := hf.indicator hT
  have hEq : T.indicator (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) =
      fun t : ℝ => (t : ℂ) ^ (s - 1) • T.indicator f t :=
    indicator_smul T (fun t : ℝ => (t : ℂ) ^ (s - 1)) f
  rw [hEq] at h
  exact h

/-- A function vanishing on `(0,1]` whose Mellin integral converges at `σ` has a convergent
Mellin integral at every `s` with `Re s ≤ σ`. -/
theorem mellinConvergent_of_le {f : ℝ → ℂ} (hf0 : ∀ t ∈ Ioc (0 : ℝ) 1, f t = 0) {σ : ℝ}
    (hσ : MellinConvergent f σ) {s : ℂ} (hs : s.re ≤ σ) : MellinConvergent f s := by
  have hmeas := aestronglyMeasurable_of_mellinConvergent hσ
  unfold MellinConvergent at hσ ⊢
  refine Integrable.mono hσ ?_ ?_
  · refine AEStronglyMeasurable.fun_smul ?_ hmeas
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rcases le_or_gt t 1 with h | h
    · rw [hf0 t ⟨ht, h⟩, smul_zero, smul_zero]
    · rw [norm_smul, norm_smul, norm_cpow_eq_rpow_re_of_pos ht,
        norm_cpow_eq_rpow_re_of_pos ht]
      refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h.le ?_) (norm_nonneg _)
      have : (s - 1).re ≤ ((σ : ℂ) - 1).re := by
        rw [sub_re, sub_re, one_re, ofReal_re]
        linarith
      exact this

/-- A function vanishing on `(0,1]` whose Mellin integral converges at `σ` has a Mellin
transform which is complex differentiable at every `s` with `Re s < σ`. -/
theorem mellin_differentiableAt_of_lt {f : ℝ → ℂ} (hf0 : ∀ t ∈ Ioc (0 : ℝ) 1, f t = 0)
    {σ : ℝ} (hσ : MellinConvergent f σ) {s : ℂ} (hs : s.re < σ) :
    DifferentiableAt ℂ (mellin f) s := by
  have hmeas := aestronglyMeasurable_of_mellinConvergent hσ
  set v : ℝ := (σ - s.re) / 2 with hv
  have hv0 : 0 < v := by rw [hv]; linarith
  set F : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) • f t with hF
  set F' : ℂ → ℝ → ℂ := fun z t => ((t : ℂ) ^ (z - 1) * (Real.log t : ℂ)) • f t with hF'
  set bound : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((σ : ℂ) - 1) • f t‖ / v with hbound
  have h1 : ∀ᶠ z : ℂ in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    refine Eventually.of_forall fun z => AEStronglyMeasurable.fun_smul ?_ hmeas
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
  have h2 : Integrable (F s) (volume.restrict (Ioi 0)) := mellinConvergent_of_le hf0 hσ hs.le
  have h3 : AEStronglyMeasurable (F' s) (volume.restrict (Ioi 0)) := by
    refine AEStronglyMeasurable.fun_smul ?_ hmeas
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_of_forall_continuousAt fun t ht =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
    · exact continuous_ofReal.comp_continuousOn
        (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)
  have h4 : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ z : ℂ, z ∈ Metric.ball s v → ‖F' z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    rcases le_or_gt t 1 with h | h
    · simp only [hF', hbound, hf0 t ⟨ht, h⟩, smul_zero, norm_zero]
      positivity
    · have hzre : z.re < s.re + v := by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        have := (re_le_norm (z - s)).trans_lt hz
        rw [sub_re] at this
        linarith
      have hlog : |Real.log t| ≤ t ^ v / v := by
        rw [abs_of_pos (Real.log_pos h)]
        exact Real.log_le_rpow_div ht.le hv0
      have hpow : t ^ (z.re - 1) ≤ t ^ (σ - v - 1) :=
        Real.rpow_le_rpow_of_exponent_le h.le (by rw [hv] at hzre ⊢; linarith)
      calc ‖F' z t‖ = t ^ (z.re - 1) * |Real.log t| * ‖f t‖ := by
            simp only [hF', norm_smul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re,
              norm_real, Real.norm_eq_abs]
        _ ≤ t ^ (σ - v - 1) * (t ^ v / v) * ‖f t‖ := by gcongr
        _ = bound t := by
            simp only [hbound, norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re,
              ofReal_re]
            have : t ^ (σ - 1) = t ^ (σ - v - 1) * t ^ v := by
              rw [← Real.rpow_add ht]; ring_nf
            rw [this]
            ring
  have h5 : Integrable bound (volume.restrict (Ioi 0)) := hσ.norm.div_const v
  have h6 : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi 0)),
      ∀ y : ℂ, y ∈ Metric.ball s v → HasDerivAt (fun z : ℂ => F z t) (F' y t) y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht y _
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have u1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (z - 1)) (t ^ (y - 1) * Real.log t) y := by
      convert! ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [ofReal_log (le_of_lt ht)]
      ring
    exact u1.smul_const (f t)
  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hv0) h1 h2 h3 h4 h5 h6
  exact main.2.differentiableAt

end Sol_MellinAsymptotics_mellin_eq_holomorphic_add_principalParts

open Sol_MellinAsymptotics_mellin_eq_holomorphic_add_principalParts in
theorem solution
    (φ : ℝ → ℂ) (a A : ℝ) (b : WithTop ℝ) (hab : (a : WithTop ℝ) < b)
    (hφ : ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b → MellinConvergent φ s)
    (S : Finset ℂ) (m : ℂ → ℕ) (c : ℂ → ℕ → ℂ)
    (hS : ∀ α ∈ S, A < (-α).re ∧ (-α).re ≤ a)
    (hexp : (fun t : ℝ => φ t - ∑ α ∈ S, ∑ k ∈ Finset.range (m α),
        c α k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k) =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-A)) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {s : ℂ | A < s.re ∧ (s.re : WithTop ℝ) < b} ∧
      ∀ s : ℂ, a < s.re → (s.re : WithTop ℝ) < b →
        mellin φ s = g s + ∑ α ∈ S, ∑ k ∈ Finset.range (m α),
          c α k * (-1) ^ k * (k.factorial : ℂ) / (s + α) ^ (k + 1) := by
  classical
  obtain ⟨σ₀, hσ₀a, hσ₀b⟩ := exists_lt_withTop hab
  have hφ₀ : MellinConvergent φ (σ₀ : ℂ) :=
    hφ σ₀ (by simpa using hσ₀a) (by simpa using hσ₀b)
  have hφloc : LocallyIntegrableOn φ (Set.Ioi 0) := locallyIntegrableOn_of_mellinConvergent hφ₀
  set E : ℝ → ℂ := fun t => ∑ α ∈ S, ∑ k ∈ Finset.range (m α),
    c α k * (t : ℂ) ^ α * (Real.log t : ℂ) ^ k with hE
  set cutoff : ℝ → ℂ := (Set.Ioc (0 : ℝ) 1).indicator E with hcutoff
  set ψ₁ : ℝ → ℂ := fun t => (Set.Ioc (0 : ℝ) 1).indicator φ t - cutoff t with hψ₁
  set ψ₂ : ℝ → ℂ := (Set.Ioc (0 : ℝ) 1)ᶜ.indicator φ with hψ₂
  have hEcont : ContinuousOn E (Set.Ioi 0) := by
    refine continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun k _ => ?_
    have := (continuousOn_cpowLog α k).const_smul (c α k)
    refine this.congr fun t _ => ?_
    simp [cpowLog, smul_eq_mul, mul_assoc]
  have hψ₂0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ψ₂ t = 0 := fun t ht =>
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ht) _
  refine ⟨fun s => mellin ψ₁ s + mellin ψ₂ s, ?_, ?_⟩
  · -- holomorphy on the wide strip
    intro s hs
    obtain ⟨hsA, hsb⟩ := hs
    refine (DifferentiableAt.add ?_ ?_).differentiableWithinAt
    · have hloc : LocallyIntegrableOn ψ₁ (Set.Ioi 0) :=
        (locallyIntegrableOn_indicator hφloc measurableSet_Ioc).sub
          (locallyIntegrableOn_indicator (hEcont.locallyIntegrableOn measurableSet_Ioi)
            measurableSet_Ioc)
      have htop : ψ₁ =O[atTop] (fun t : ℝ => t ^ (-(s.re + 1))) := by
        refine Asymptotics.IsBigO.of_bound 0 ?_
        filter_upwards [eventually_gt_atTop 1] with t ht
        have hnot : t ∉ Set.Ioc (0 : ℝ) 1 := fun h => lt_irrefl (1 : ℝ) (ht.trans_le h.2)
        simp [hψ₁, hcutoff, Set.indicator_of_notMem hnot]
      have hEq : (fun t : ℝ => φ t - E t) =ᶠ[𝓝[>] (0 : ℝ)] ψ₁ := by
        filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
        have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
        simp [hψ₁, hcutoff, Set.indicator_of_mem ht']
      have hbot : ψ₁ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-A)) :=
        hexp.congr' hEq EventuallyEq.rfl
      exact mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hbot hsA
    · have hx : ((max a s.re : ℝ) : WithTop ℝ) < b := by
        rcases le_total s.re a with hsa | hsa
        · rw [max_eq_left hsa]; exact hab
        · rw [max_eq_right hsa]; exact hsb
      obtain ⟨σ, hσgt, hσb⟩ := exists_lt_withTop hx
      have hσa : a < σ := lt_of_le_of_lt (le_max_left a s.re) hσgt
      have hσs : s.re < σ := lt_of_le_of_lt (le_max_right a s.re) hσgt
      have hconv : MellinConvergent ψ₂ (σ : ℂ) :=
        mellinConvergent_indicator (hφ σ (by simpa using hσa) (by simpa using hσb))
          measurableSet_Ioc.compl
      exact mellin_differentiableAt_of_lt hψ₂0 hconv hσs
  · -- the decomposition on the original strip
    intro s hsa hsb
    have hconv := hφ s hsa hsb
    have h1 : MellinConvergent ((Set.Ioc (0 : ℝ) 1).indicator φ) s :=
      mellinConvergent_indicator hconv measurableSet_Ioc
    have h2 : MellinConvergent ψ₂ s := mellinConvergent_indicator hconv measurableSet_Ioc.compl
    have hterm : ∀ β ∈ S, ∀ j ∈ Finset.range (m β),
        HasMellin ((Set.Ioc (0 : ℝ) 1).indicator
          (fun t => c β j * (t : ℂ) ^ β * (Real.log t : ℂ) ^ j)) s
          (c β j * (-1) ^ j * (j.factorial : ℂ) / (s + β) ^ (j + 1)) := by
      intro β hβ j _hj
      have hre : 0 < s.re + β.re := by
        have : -β.re ≤ a := by simpa [Complex.neg_re] using (hS β hβ).2
        linarith
      have hbase := hasMellin_cpowLogInd β j hre
      have hsm := hasMellin_const_smul hbase.1 (c β j)
      rw [hbase.2] at hsm
      have hfun : (fun t => (c β j) • cpowLogInd β j t) =
          (Set.Ioc (0 : ℝ) 1).indicator
            (fun t => c β j * (t : ℂ) ^ β * (Real.log t : ℂ) ^ j) := by
        funext t
        by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
        · simp [cpowLogInd, cpowLog, ht, Set.indicator_of_mem, smul_eq_mul, mul_assoc]
        · simp [cpowLogInd, ht, Set.indicator_of_notMem, smul_eq_mul]
      have hval : (c β j) • ((-1 : ℂ) ^ j * ((j.factorial : ℕ) : ℂ) *
          (s + β) ^ (-(j : ℤ) - 1)) =
          c β j * (-1) ^ j * (j.factorial : ℂ) / (s + β) ^ (j + 1) := by
        have hz : (s + β) ^ (-(j : ℤ) - 1) = ((s + β) ^ (j + 1))⁻¹ := by
          rw [show (-(j : ℤ) - 1) = -((j + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
            zpow_natCast]
        rw [hz, smul_eq_mul, div_eq_mul_inv]
        ring
      rw [hfun, hval] at hsm
      exact hsm
    have hcutFun : cutoff = fun t =>
        ∑ α ∈ S, ∑ j ∈ Finset.range (m α),
          (Set.Ioc (0 : ℝ) 1).indicator
            (fun u => c α j * (u : ℂ) ^ α * (Real.log u : ℂ) ^ j) t := by
      funext t
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · simp [hcutoff, hE, Set.indicator_of_mem ht]
      · simp [hcutoff, hE, Set.indicator_of_notMem ht]
    have hcut : HasMellin cutoff s (∑ α ∈ S, ∑ k ∈ Finset.range (m α),
          c α k * (-1) ^ k * (k.factorial : ℂ) / (s + α) ^ (k + 1)) := by
      rw [hcutFun]
      refine hasMellin_finset_sum S _ _ s fun α hα => ?_
      exact hasMellin_finset_sum (Finset.range (m α)) _ _ s fun j hj => hterm α hα j hj
    have hψ₁c : MellinConvergent ψ₁ s := (hasMellin_sub h1 hcut.1).1
    have hsplit1 := hasMellin_add hψ₁c hcut.1
    have hsplit2 := hasMellin_add hsplit1.1 h2
    have hfun : (fun t => (ψ₁ t + cutoff t) + ψ₂ t) = φ := by
      funext t
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · have h2' := hψ₂0 t ht
        simp only [hψ₁, hcutoff, Set.indicator_of_mem ht]
        rw [h2']
        ring
      · have hc : t ∈ (Set.Ioc (0 : ℝ) 1)ᶜ := ht
        simp only [hψ₁, hψ₂, hcutoff, Set.indicator_of_notMem ht, Set.indicator_of_mem hc]
        ring
    rw [hfun] at hsplit2
    rw [hsplit2.2, hsplit1.2, hcut.2]
    ring
