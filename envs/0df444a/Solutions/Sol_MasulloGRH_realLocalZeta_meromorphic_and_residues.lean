-- Prove2me | solution 1 for MasulloGRH.realLocalZeta_meromorphic_and_residues
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:19:05.704136+00:00
-- url     : https://prove2.me/submissions/4d0fc482-55db-4bf9-bed0-7c14f15f572e

import Mathlib

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Sol_MasulloGRH_realLocalZeta_meromorphic_and_residues

open Complex Set Filter Asymptotics Topology

noncomputable def tc (g : ℝ → ℂ) (k : ℕ) : ℂ := iteratedDeriv k g 0 / (k.factorial : ℂ)

noncomputable def T (g : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, tc g k * (t : ℂ) ^ k

noncomputable def R (g : ℝ → ℂ) (n : ℕ) : ℝ → ℂ := indicator (Ioc 0 1) (fun t => g t - T g n t)

noncomputable def G (g : ℝ → ℂ) : ℝ → ℂ := indicator (Ioi 1) g

noncomputable def F (g : ℝ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  mellin (R g n) s + mellin (G g) s + ∑ k ∈ Finset.range n, tc g k / (s + k)

noncomputable def Mf (g : ℝ → ℂ) (s : ℂ) : ℂ := F g (⌊-s.re⌋₊ + 1) s

structure Good (g : ℝ → ℂ) : Prop where
  smooth : ∀ n : ℕ, ContDiff ℝ n g
  integrable : Integrable g
  decay : ∀ a : ℝ, g =O[atTop] (fun t : ℝ => t ^ (-a))

variable {g : ℝ → ℂ}

lemma taylor_eq (n : ℕ) (x : ℝ) : taylorWithinEval g n univ 0 x = T g (n+1) x := by
  rw [taylor_within_apply]
  unfold T tc
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [iteratedDerivWithin_univ, sub_zero, Complex.real_smul]
  push_cast
  ring

lemma sub_T_isBigO (hg : Good g) (n : ℕ) :
    (fun t => g t - T g n t) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
  have h1 : (fun t => g t - T g (n+1) t) =o[𝓝 0] (fun t : ℝ => t ^ n) := by
    have := taylor_isLittleO_univ (f := g) (x₀ := 0) (n := n) (hg.smooth n)
    simpa [taylor_eq] using this
  have h2 : (fun t : ℝ => tc g n * (t : ℂ) ^ n) =O[𝓝 0] (fun t : ℝ => t ^ n) := by
    refine Asymptotics.IsBigO.of_bound ‖tc g n‖ (Eventually.of_forall fun t => ?_)
    simp [norm_pow]
  have : (fun t => g t - T g n t) = fun t => (g t - T g (n+1) t) + tc g n * (t:ℂ)^n := by
    ext t; simp only [T, Finset.sum_range_succ]; ring
  rw [this]
  exact h1.isBigO.add h2

lemma R_bot (hg : Good g) (n : ℕ) : R g n =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-(n:ℝ)))) := by
  have h1 := (sub_T_isBigO hg n).mono (nhdsWithin_le_nhds (s := Ioi 0))
  have h2 : (fun t : ℝ => t ^ n) =ᶠ[𝓝[>] 0] (fun t : ℝ => t ^ (-(-(n:ℝ)))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [neg_neg, Real.rpow_natCast]
  have h3 : R g n =ᶠ[𝓝[>] 0] (fun t => g t - T g n t) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    simp [R, indicator_of_mem (Ioo_subset_Ioc_self ht)]
  exact h1.congr' h3.symm h2

lemma R_top (n : ℕ) (a : ℝ) : R g n =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  have : R g n =ᶠ[atTop] (fun _ => (0:ℂ)) := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [R, indicator_of_notMem (fun h : t ∈ Ioc 0 1 => absurd h.2 (not_le.mpr ht))]
  exact (isBigO_zero _ _).congr' this.symm EventuallyEq.rfl

lemma R_integrable (hg : Good g) (n : ℕ) : Integrable (R g n) := by
  unfold R
  rw [integrable_indicator_iff measurableSet_Ioc]
  have hc0 : Continuous g := (hg.smooth 0).continuous
  have hc : Continuous (fun t => g t - T g n t) := by
    unfold T; fun_prop
  exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

lemma G_integrable (hg : Good g) : Integrable (G g) := hg.integrable.indicator measurableSet_Ioi

lemma G_top (hg : Good g) (a : ℝ) : G g =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  have : G g =ᶠ[atTop] g := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [G, indicator_of_mem (show t ∈ Ioi 1 from ht)]
  exact (hg.decay a).congr' this.symm EventuallyEq.rfl

lemma G_bot (b : ℝ) : G g =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  have : G g =ᶠ[𝓝[>] 0] (fun _ => (0:ℂ)) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    simp [G, indicator_of_notMem (show t ∉ Ioi 1 from fun h => absurd h (not_lt.mpr ht.2.le))]
  exact (isBigO_zero _ _).congr' this.symm EventuallyEq.rfl

lemma R_diff (hg : Good g) (n : ℕ) (s : ℂ) (hs : -(n:ℝ) < s.re) :
    DifferentiableAt ℂ (mellin (R g n)) s :=
  mellin_differentiableAt_of_isBigO_rpow ((R_integrable hg n).locallyIntegrable.locallyIntegrableOn _)
    (R_top n (s.re + 1)) (by linarith) (R_bot hg n) hs

lemma R_conv (hg : Good g) (n : ℕ) (s : ℂ) (hs : -(n:ℝ) < s.re) : MellinConvergent (R g n) s :=
  mellinConvergent_of_isBigO_rpow ((R_integrable hg n).locallyIntegrable.locallyIntegrableOn _)
    (R_top n (s.re + 1)) (by linarith) (R_bot hg n) hs

lemma G_diff (hg : Good g) (s : ℂ) : DifferentiableAt ℂ (mellin (G g)) s :=
  mellin_differentiableAt_of_isBigO_rpow ((G_integrable hg).locallyIntegrable.locallyIntegrableOn _)
    (G_top hg (s.re + 1)) (by linarith) (G_bot (s.re - 1)) (by linarith)

lemma G_conv (hg : Good g) (s : ℂ) : MellinConvergent (G g) s :=
  mellinConvergent_of_isBigO_rpow ((G_integrable hg).locallyIntegrable.locallyIntegrableOn _)
    (G_top hg (s.re + 1)) (by linarith) (G_bot (s.re - 1)) (by linarith)

lemma F_succ (hg : Good g) (n : ℕ) (s : ℂ) (hs : -(n:ℝ) < s.re) : F g (n+1) s = F g n s := by
  have hR : R g n = fun t => R g (n+1) t +
      tc g n • indicator (Ioc 0 1) (fun t : ℝ => (t:ℂ) ^ (n:ℂ)) t := by
    ext t
    by_cases ht : t ∈ Ioc 0 1
    · simp only [R, T, indicator_of_mem ht, Finset.sum_range_succ, Complex.cpow_natCast,
        smul_eq_mul]
      ring
    · simp [R, indicator_of_notMem ht]
  have h1 : MellinConvergent (R g (n+1)) s := R_conv hg (n+1) s (by push_cast; linarith)
  have hpow := hasMellin_cpow_Ioc (n:ℂ) (s := s) (by simp; linarith)
  have h2 := hasMellin_const_smul hpow.1 (tc g n)
  have h3 := hasMellin_add h1 h2.1
  have : mellin (R g n) s = mellin (R g (n+1)) s + tc g n * (1 / (s + n)) := by
    rw [hR, h3.2, h2.2, hpow.2, smul_eq_mul]
  unfold F
  rw [this, Finset.sum_range_succ]
  ring

lemma F_add (hg : Good g) (n : ℕ) (s : ℂ) (hs : -(n:ℝ) < s.re) :
    ∀ m : ℕ, F g (n+m) s = F g n s
  | 0 => rfl
  | m+1 => by
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    rw [← add_assoc, F_succ hg (n+m) s (by push_cast; linarith), F_add hg n s hs m]

lemma F_eq (hg : Good g) (n m : ℕ) (s : ℂ) (hn : -(n:ℝ) < s.re) (hm : -(m:ℝ) < s.re) :
    F g n s = F g m s := by
  rcases le_total n m with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (F_add hg n s hn k).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact F_add hg m s hm k

lemma N_lt (s : ℂ) : -((⌊-s.re⌋₊ + 1 : ℕ) : ℝ) < s.re := by
  have := Nat.lt_floor_add_one (-s.re)
  push_cast; linarith

lemma Mf_eq (hg : Good g) (n : ℕ) (s : ℂ) (hn : -(n:ℝ) < s.re) : Mf g s = F g n s :=
  F_eq hg _ n s (N_lt s) hn

lemma Mf_eventually (hg : Good g) (n : ℕ) (s₀ : ℂ) (hn : -(n:ℝ) < s₀.re) :
    Mf g =ᶠ[𝓝 s₀] F g n := by
  have : {s : ℂ | -(n:ℝ) < s.re} ∈ 𝓝 s₀ :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hn
  filter_upwards [this] with s hs
  exact Mf_eq hg n s hs

lemma H_analytic (hg : Good g) (n : ℕ) (s₀ : ℂ) (hn : -(n:ℝ) < s₀.re) :
    AnalyticAt ℂ (fun s => mellin (R g n) s + mellin (G g) s) s₀ := by
  have hU : IsOpen {s : ℂ | -(n:ℝ) < s.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun s => mellin (R g n) s + mellin (G g) s)
      {s : ℂ | -(n:ℝ) < s.re} := by
    intro s hs
    exact ((R_diff hg n s hs).add (G_diff hg s)).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hn)

lemma Mf_analytic (hg : Good g) (s₀ : ℂ) (h : ∀ m : ℕ, s₀ = -(m:ℂ) → tc g m = 0) :
    AnalyticAt ℂ (Mf g) s₀ := by
  have hn := N_lt s₀
  have hF : AnalyticAt ℂ (F g (⌊-s₀.re⌋₊ + 1)) s₀ := by
    have h1 := H_analytic hg (⌊-s₀.re⌋₊ + 1) s₀ hn
    have h2 : AnalyticAt ℂ (fun s => ∑ k ∈ Finset.range (⌊-s₀.re⌋₊ + 1), tc g k / (s + k)) s₀ := by
      apply Finset.analyticAt_fun_sum
      intro k _
      by_cases hk : tc g k = 0
      · simp only [hk, zero_div]; exact analyticAt_const
      · have : s₀ + k ≠ 0 := by
          intro h0; apply hk; apply h k; linear_combination h0
        exact analyticAt_const.div (analyticAt_id.add analyticAt_const) this
    exact h1.add h2
  exact hF.congr (Mf_eventually hg _ s₀ hn).symm

lemma Mf_meromorphic (hg : Good g) : MeromorphicOn (Mf g) univ := by
  intro s₀ _
  have hn := N_lt s₀
  have hF : MeromorphicAt (F g (⌊-s₀.re⌋₊ + 1)) s₀ := by
    have h1 := (H_analytic hg (⌊-s₀.re⌋₊ + 1) s₀ hn).meromorphicAt
    have h2 : MeromorphicAt
        (fun s => ∑ k ∈ Finset.range (⌊-s₀.re⌋₊ + 1), tc g k / (s + k)) s₀ := by
      apply MeromorphicAt.fun_sum
      intro k _
      exact (analyticAt_const.meromorphicAt).div
        ((analyticAt_id.add analyticAt_const).meromorphicAt)
    exact h1.add h2
  exact hF.congr ((Mf_eventually hg _ s₀ hn).symm.filter_mono nhdsWithin_le_nhds)

lemma Mf_residue (hg : Good g) (m : ℕ) :
    Tendsto (fun s : ℂ => (s + m) * Mf g s) (𝓝[≠] (-(m:ℂ))) (𝓝 (tc g m)) := by
  have hn : -((m+1 : ℕ):ℝ) < (-(m:ℂ)).re := by simp
  set H : ℂ → ℂ := fun s => mellin (R g (m+1)) s + mellin (G g) s +
    ∑ k ∈ Finset.range m, tc g k / (s + k) with hHdef
  have hH : ContinuousAt H (-(m:ℂ)) := by
    have h1 := H_analytic hg (m+1) _ hn
    have h2 : AnalyticAt ℂ (fun s => ∑ k ∈ Finset.range m, tc g k / (s + k)) (-(m:ℂ)) := by
      apply Finset.analyticAt_fun_sum
      intro k hk
      have hkm := Finset.mem_range.mp hk
      have : -(m:ℂ) + k ≠ 0 := by
        intro h0
        have h0' : (k:ℂ) = m := by linear_combination h0
        exact (Nat.ne_of_lt hkm) (by exact_mod_cast h0')
      exact analyticAt_const.div (analyticAt_id.add analyticAt_const) this
    exact (h1.add h2).continuousAt
  have hlim : Tendsto (fun s : ℂ => (s + m) * H s + tc g m) (𝓝 (-(m:ℂ)))
      (𝓝 ((-(m:ℂ) + m) * H (-(m:ℂ)) + tc g m)) :=
    (((continuous_id.add continuous_const).continuousAt.mul hH).add continuousAt_const).tendsto
  rw [neg_add_cancel, zero_mul, zero_add] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev := (Mf_eventually hg (m+1) (-(m:ℂ)) hn).filter_mono
    (nhdsWithin_le_nhds (s := {-(m:ℂ)}ᶜ))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
  rw [hs]
  have hne' : s + m ≠ 0 := by
    intro h0; apply hne; simp only [mem_singleton_iff]; linear_combination h0
  have hc : (s + m) * (tc g m / (s + m)) = tc g m := mul_div_cancel₀ _ hne'
  simp only [F, Finset.sum_range_succ, hHdef]
  linear_combination -hc

lemma Mf_eq_mellin (hg : Good g) (s : ℂ) (hs : 0 < s.re) : Mf g s = mellin g s := by
  rw [Mf_eq hg 0 s (by simpa using hs)]
  have h1 : MellinConvergent (R g 0) s := R_conv hg 0 s (by simpa using hs)
  have h2 : MellinConvergent (G g) s := G_conv hg s
  have h3 := hasMellin_add h1 h2
  simp only [F, Finset.sum_range_zero, add_zero]
  rw [← h3.2]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [R, G, T, Finset.sum_range_zero, sub_zero]
  congr 1
  by_cases h : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc 0 1 from ⟨ht, h⟩),
      indicator_of_notMem (show t ∉ Ioi 1 from not_lt.mpr h), add_zero]
  · rw [indicator_of_notMem (show t ∉ Ioc 0 1 from fun h' => h h'.2),
      indicator_of_mem (show t ∈ Ioi 1 from lt_of_not_ge h), zero_add]

lemma good_conv (hg : Good g) (s : ℂ) (hs : 0 < s.re) : MellinConvergent g s := by
  refine mellinConvergent_of_isBigO_rpow (hg.integrable.locallyIntegrable.locallyIntegrableOn _)
    (hg.decay (s.re + 1)) (by linarith) (b := 0) ?_ hs
  have h := ((hg.smooth 0).continuous.continuousAt (x := 0)).tendsto
  have := (h.isBigO_one ℝ).mono (nhdsWithin_le_nhds (s := Ioi 0))
  refine this.congr' EventuallyEq.rfl ?_
  filter_upwards with t
  simp


lemma good_f (f : SchwartzMap ℝ ℂ) : Good (fun x => f x) where
  smooth n := f.smooth n
  integrable := f.integrable
  decay a := by
    have := (f.isBigO_cocompact_rpow (-a)).mono atTop_le_cocompact
    refine this.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Real.norm_eq_abs, abs_of_pos ht]

lemma good_fneg (f : SchwartzMap ℝ ℂ) : Good (fun x => f (-x)) where
  smooth n := (f.smooth n).comp contDiff_neg
  integrable := f.integrable.comp_neg
  decay a := by
    have := (f.isBigO_cocompact_rpow (-a)).comp_tendsto
      (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)
    refine this.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [Real.norm_eq_abs, abs_of_pos ht]

lemma Good.add_mul {g₁ g₂ : ℝ → ℂ} (h₁ : Good g₁) (h₂ : Good g₂) (ε : ℂ) :
    Good (fun x => g₁ x + ε * g₂ x) where
  smooth n := (h₁.smooth n).add (contDiff_const.mul (h₂.smooth n))
  integrable := h₁.integrable.add (h₂.integrable.const_mul ε)
  decay a := (h₁.decay a).add ((h₂.decay a).const_mul_left ε)

lemma tc_eq (f : SchwartzMap ℝ ℂ) (ε : ℂ) (m : ℕ) :
    tc (fun x => f x + ε * f (-x)) m =
      (1 + ε * (-1) ^ m) * iteratedDeriv m (fun x : ℝ => f x) 0 / (m.factorial : ℂ) := by
  unfold tc
  have hc1 : ContDiff ℝ m (fun x : ℝ => f x) := f.smooth m
  have hc2 : ContDiff ℝ m (fun x : ℝ => ε * f (-x)) :=
    contDiff_const.mul ((f.smooth m).comp contDiff_neg)
  rw [iteratedDeriv_fun_add hc1.contDiffAt hc2.contDiffAt]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, neg_zero, Complex.real_smul]
  push_cast
  ring

lemma integral_split (Φ : ℝ → ℂ) (h1 : IntegrableOn Φ (Ioi 0))
    (h2 : IntegrableOn (fun x => Φ (-x)) (Ioi 0)) :
    ∫ x, Φ x = (∫ x in Ioi 0, Φ x) + ∫ x in Ioi 0, Φ (-x) := by
  have h2' : IntegrableOn Φ (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    have := IntegrableOn.comp_neg_Iio (c := (0:ℝ)) (f := fun x => Φ (-x)) (by simpa using h2)
    simpa using this
  have hint : Integrable Φ := by
    have := h2'.union h1
    rwa [Iic_union_Ioi, integrableOn_univ] at this
  rw [← integral_add_compl (μ := volume) (s := Ioi (0:ℝ)) measurableSet_Ioi hint, compl_Ioi,
    integral_comp_neg_Ioi, neg_zero]

lemma integral_eq_mellin (f : SchwartzMap ℝ ℂ) (ε : ℂ) (σ : ℝ → ℂ)
    (hσp : ∀ x : ℝ, 0 < x → σ x = 1) (hσn : ∀ x : ℝ, x < 0 → σ x = ε) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, f x * σ x * ((|x| : ℝ) : ℂ) ^ (s - 1) = mellin (fun x => f x + ε * f (-x)) s := by
  have c1 : MellinConvergent (fun x => f x) s := good_conv (good_f f) s hs
  have c2 : MellinConvergent (fun x => ε * f (-x)) s :=
    (good_conv (good_fneg f) s hs).const_smul ε
  have e1 : EqOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • f x)
      (fun x : ℝ => f x * σ x * ((|x| : ℝ) : ℂ) ^ (s - 1)) (Ioi 0) := by
    intro x hx
    simp only
    rw [hσp x hx, abs_of_pos (show (0:ℝ) < x from hx), smul_eq_mul]
    ring
  have e2 : EqOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • (ε * f (-x)))
      (fun x : ℝ => f (-x) * σ (-x) * ((|-x| : ℝ) : ℂ) ^ (s - 1)) (Ioi 0) := by
    intro x hx
    simp only
    rw [hσn (-x) (neg_lt_zero.mpr hx), abs_neg, abs_of_pos (show (0:ℝ) < x from hx), smul_eq_mul]
    ring
  rw [integral_split _ (c1.congr_fun e1 measurableSet_Ioi) (c2.congr_fun e2 measurableSet_Ioi)]
  have i1 : ∫ x in Ioi 0, f x * σ x * ((|x| : ℝ) : ℂ) ^ (s - 1) = mellin (fun x => f x) s :=
    (setIntegral_congr_fun measurableSet_Ioi e1).symm
  have i2 : ∫ x in Ioi 0, f (-x) * σ (-x) * ((|-x| : ℝ) : ℂ) ^ (s - 1) =
      mellin (fun x => ε * f (-x)) s :=
    (setIntegral_congr_fun measurableSet_Ioi e2).symm
  rw [i1, i2]
  exact (hasMellin_add c1 c2).2.symm

end Sol_MasulloGRH_realLocalZeta_meromorphic_and_residues

open Sol_MasulloGRH_realLocalZeta_meromorphic_and_residues in
theorem solution (f : SchwartzMap ℝ ℂ) :
    ∃ M₀ M₁ : ℂ → ℂ, MeromorphicOn M₀ Set.univ ∧ MeromorphicOn M₁ Set.univ ∧
      (∀ s : ℂ, 0 < s.re → M₀ s = ∫ x : ℝ, f x * ((|x| : ℝ) : ℂ) ^ (s - 1)) ∧
      (∀ s : ℂ, 0 < s.re →
        M₁ s = ∫ x : ℝ, f x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) ∧
      (∀ s : ℂ, (∀ m : ℕ, Even m → s ≠ -(m : ℂ)) → AnalyticAt ℂ M₀ s) ∧
      (∀ s : ℂ, (∀ m : ℕ, Odd m → s ≠ -(m : ℂ)) → AnalyticAt ℂ M₁ s) ∧
      (∀ m : ℕ, Even m →
        Filter.Tendsto (fun s : ℂ => (s + m) * M₀ s) (nhdsWithin (-(m : ℂ)) {-(m : ℂ)}ᶜ)
          (nhds (2 * iteratedDeriv m (fun x : ℝ => f x) 0 / (m.factorial : ℂ)))) ∧
      (∀ m : ℕ, Odd m →
        Filter.Tendsto (fun s : ℂ => (s + m) * M₁ s) (nhdsWithin (-(m : ℂ)) {-(m : ℂ)}ᶜ)
          (nhds (2 * iteratedDeriv m (fun x : ℝ => f x) 0 / (m.factorial : ℂ)))) := by
  have hg0 := (good_f f).add_mul (good_fneg f) 1
  have hg1 := (good_f f).add_mul (good_fneg f) (-1)
  refine ⟨Mf (fun x => f x + 1 * f (-x)), Mf (fun x => f x + (-1) * f (-x)),
    Mf_meromorphic hg0, Mf_meromorphic hg1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [Mf_eq_mellin hg0 s hs]
    have := integral_eq_mellin f 1 (fun _ => 1) (fun _ _ => rfl) (fun _ _ => rfl) s hs
    simp only [mul_one] at this
    exact this.symm
  · intro s hs
    rw [Mf_eq_mellin hg1 s hs]
    exact (integral_eq_mellin f (-1) (fun x => ((Real.sign x : ℝ) : ℂ))
      (fun x hx => by simp [Real.sign_of_pos hx]) (fun x hx => by simp [Real.sign_of_neg hx])
      s hs).symm
  · intro s hs
    apply Mf_analytic hg0
    intro m hm
    rw [tc_eq]
    rcases Nat.even_or_odd m with he | ho
    · exact absurd hm (hs m he)
    · rw [ho.neg_one_pow]; ring
  · intro s hs
    apply Mf_analytic hg1
    intro m hm
    rw [tc_eq]
    rcases Nat.even_or_odd m with he | ho
    · rw [he.neg_one_pow]; ring
    · exact absurd hm (hs m ho)
  · intro m hm
    have := Mf_residue hg0 m
    rw [tc_eq, hm.neg_one_pow] at this
    convert this using 2
    ring
  · intro m hm
    have := Mf_residue hg1 m
    rw [tc_eq, hm.neg_one_pow] at this
    convert this using 2
    ring
