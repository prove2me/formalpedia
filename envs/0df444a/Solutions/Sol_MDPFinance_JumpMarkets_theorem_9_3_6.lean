-- Prove2me | solution 1 for MDPFinance.JumpMarkets.theorem_9_3_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:50:56.702688+00:00
-- url     : https://prove2.me/submissions/1beddd25-8d55-483c-a27b-81cf6ea241b5

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket
import Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_3_4
import Theorems.Thm_MDPFinance_JumpMarkets_proposition_9_3_2

open MeasureTheory Filter Topology MDPFinance.JumpMarkets
open scoped ENNReal

namespace SolTheorem936

variable {d : ℕ}

lemma isBoundingFunction_max_zero (M : JumpMarket d) (bf : ℝ × ℝ → ℝ) (alpha : ℝ)
    (hb : M.IsBoundingFunction bf alpha) :
    M.IsBoundingFunction bf (max 0 alpha) := by
  refine ⟨hb.1, hb.2.1, fun p hp a => (hb.2.2 p hp a).trans ?_⟩
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right 0 alpha) (hb.1 p hp).le)

lemma control_ext {a b : Control d} (h : a.val = b.val) : a = b := by
  cases a; cases b; congr

lemma lintegral_lam_exp (lam : ℝ) (hlam : 0 < lam) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ s in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (lam * Real.exp (-lam * s)) =
      ENNReal.ofReal (1 - Real.exp (-lam * t)) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun x => -Real.exp (-lam * x)) (lam * Real.exp (-lam * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun x => -lam * x) (-lam) s := by
      simpa using (hasDerivAt_id s).const_mul (-lam)
    exact (h1.exp.neg).congr_deriv (by ring)
  have hcont : Continuous (fun s => lam * Real.exp (-lam * s)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hint : IntervalIntegrable (fun s => lam * Real.exp (-lam * s)) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [mul_zero, Real.exp_zero, sub_neg_eq_add] at hftc
  have h_ae_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)] (fun s => lam * Real.exp (-lam * s)) :=
    Filter.Eventually.of_forall fun s => mul_nonneg hlam.le (Real.exp_pos _).le
  have h_int_on : IntegrableOn (fun s => lam * Real.exp (-lam * s)) (Set.Ioo 0 t) volume :=
    hcont.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal h_int_on h_ae_nonneg,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht, hftc]
  congr 1
  ring

lemma phi_eq_of_uncontrolled (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (a : Control d) (t x : ℝ) :
    M.phi a t x = x * Real.exp (∫ _s in Set.Ioc (0 : ℝ) t, M.rho) := by
  unfold JumpMarket.phi
  congr 3
  ext s
  simp [hun]

lemma phi_nonneg_of_uncontrolled (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (a : Control d) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    M.phi a t x = x * Real.exp (M.rho * t) := by
  rw [phi_eq_of_uncontrolled M hun a t x]
  congr 2
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le ht, sub_zero, smul_eq_mul, mul_comm]

lemma measurable_phi_of_uncontrolled (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (a : Control d) (x : ℝ) :
    Measurable (fun s => M.phi a s x) := by
  have h : (fun s => M.phi a s x) =
      fun s => if 0 ≤ s then x * Real.exp (M.rho * s) else x * Real.exp 0 := by
    ext s
    split_ifs with hs
    · exact phi_nonneg_of_uncontrolled M hun a hs x
    · rw [phi_eq_of_uncontrolled M hun a s x, Set.Ioc_eq_empty (by linarith), MeasureTheory.setIntegral_empty]
  rw [h]
  exact Measurable.ite measurableSet_Ici
    (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
    measurable_const

noncomputable def zeroJumpMarket (M : JumpMarket d) : JumpMarket d where
  rho := M.rho
  rho_nonneg := M.rho_nonneg
  mu := M.mu
  lam := M.lam
  lam_pos := M.lam_pos
  QY := Measure.dirac 0
  QY_prob := Measure.dirac.isProbabilityMeasure
  QY_supp := by
    rw [Measure.dirac_apply' _ (by
      have : {y : Fin d → ℝ | ∃ i, y i ≤ -1} = ⋃ i : Fin d, (fun y : Fin d → ℝ => y i) ⁻¹' Set.Iic (-1) := by
        ext y; simp
      rw [this]
      exact MeasurableSet.iUnion fun i => measurable_pi_apply i measurableSet_Iic)]
    simp [Set.indicator_of_notMem]
  QY_integrable := by
    rw [lintegral_dirac]
    simp
  T := M.T
  T_pos := M.T_pos
  U := M.U
  U_nonneg := M.U_nonneg
  U_mono := M.U_mono
  U_concave := M.U_concave
  U_cont := M.U_cont

lemma zeroJumpMarket_step_eq (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (bond : ℝ × ℝ → Control d) (hbond : ∀ p, (bond p).val = fun _ _ => 0)
    (a : Control d) (q : ℝ × ℝ) :
    (zeroJumpMarket M).step a q = M.step (bond q) q := by
  unfold JumpMarket.step
  change (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind _) = _
  congr 1
  ext s : 1
  have hphi : (zeroJumpMarket M).phi a s q.2 = M.phi (bond q) s q.2 := by
    rw [phi_eq_of_uncontrolled (zeroJumpMarket M) hun a s q.2,
        phi_eq_of_uncontrolled M hun (bond q) s q.2]
    rfl
  have hm1 : Measurable (fun y : Fin d → ℝ => (q.1 + s, (zeroJumpMarket M).phi a s q.2 * (1 + ∑ i, a.val s i * y i))) := by
    refine Measurable.prodMk measurable_const (measurable_const.mul (measurable_const.add ?_))
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  change (Measure.dirac (0 : Fin d → ℝ)).map _ = M.QY.map _
  rw [Measure.map_dirac' hm1 0]
  have hconst : (fun y : Fin d → ℝ => (q.1 + s, M.phi (bond q) s q.2 * (1 + ∑ i, (bond q).val s i * y i))) =
      fun _ => (q.1 + s, (zeroJumpMarket M).phi a s q.2 * (1 + ∑ i, a.val s i * (0 : Fin d → ℝ) i)) := by
    ext y : 1
    simp [hbond q, hphi]
  have := M.QY_prob
  rw [hconst, Measure.map_const, measure_univ, one_smul]

lemma zeroJumpMarket_chainCyl_eq (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (bond : ℝ × ℝ → Control d) (hbond : ∀ p, (bond p).val = fun _ _ => 0)
    (g : HistPolicy d) :
    ∀ (m n : ℕ) (h : Fin (n + 1) → ℝ × ℝ) (B : ℕ → Set (ℝ × ℝ)),
      (zeroJumpMarket M).chainCyl g n h m B =
        M.chainCyl (ofMarkov fun _ => bond) n h m B
  | 0, _, _, _ => rfl
  | m + 1, n, h, B => by
      simp only [JumpMarket.chainCyl]
      rw [zeroJumpMarket_step_eq M hun bond hbond (g n h) (h (Fin.last n))]
      congr 1
      ext q
      exact zeroJumpMarket_chainCyl_eq M hun bond hbond g m (n + 1) (Fin.snoc h q) (fun i => B (i + 1))

noncomputable def wBond (M : JumpMarket d) (p : ℝ × ℝ) : ℝ :=
  M.U (max 0 p.2 * Real.exp (M.rho * (M.T - p.1)))

lemma continuous_wBond (M : JumpMarket d) : Continuous (wBond M) := by
  have hcont : Continuous (fun p : ℝ × ℝ => max 0 p.2 * Real.exp (M.rho * (M.T - p.1))) :=
    (continuous_const.max continuous_snd).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_fst)))
  exact M.U_cont.comp_continuous hcont fun p => mul_nonneg (le_max_left 0 p.2) (Real.exp_pos _).le

lemma zeroJumpMarket_Q_eq (M : JumpMarket d)
    (a : Control d) (p : ℝ × ℝ) :
    (zeroJumpMarket M).Q a p =
      (((volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
          (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind
        (fun s => Measure.dirac (p.1 + s, (zeroJumpMarket M).phi a s p.2))) := by
  unfold JumpMarket.Q
  change (((volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
      (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))).bind _) = _
  congr 1
  ext s : 1
  have hm1 : Measurable (fun y : Fin d → ℝ => (p.1 + s, (zeroJumpMarket M).phi a s p.2 * (1 + ∑ i, a.val s i * y i))) := by
    refine Measurable.prodMk measurable_const (measurable_const.mul (measurable_const.add ?_))
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  change (Measure.dirac (0 : Fin d → ℝ)).map _ = _
  rw [Measure.map_dirac' hm1 0]
  simp

lemma zeroJumpMarket_IsTOf_wBond (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (c0 : Control d) :
    (zeroJumpMarket M).IsTOf (wBond M) (wBond M) := by
  intro p hp
  have hpt : p.1 ≤ M.T := hp.1.2
  have hp2 : 0 ≤ p.2 := hp.2
  have hsub : 0 ≤ M.T - p.1 := sub_nonneg.mpr hpt
  have hval : ∀ a : Control d,
      (zeroJumpMarket M).r a p + ∫ q, wBond M q ∂((zeroJumpMarket M).Q a p) = wBond M p := by
    intro a
    have hr : (zeroJumpMarket M).r a p = Real.exp (-M.lam * (M.T - p.1)) * wBond M p := by
      unfold JumpMarket.r wBond
      change Real.exp (-M.lam * (M.T - p.1)) * M.U ((zeroJumpMarket M).phi a (M.T - p.1) p.2) = _
      rw [phi_nonneg_of_uncontrolled (zeroJumpMarket M) hun a hsub p.2, max_eq_right hp2]
      rfl
    have hdirac_meas : Measurable (fun s : ℝ => Measure.dirac (p.1 + s, (zeroJumpMarket M).phi a s p.2)) :=
      Measure.measurable_dirac.comp (Measurable.prodMk (measurable_const.add measurable_id)
        (measurable_phi_of_uncontrolled (zeroJumpMarket M) hun a p.2))
    let μs := (volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))).withDensity
        (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)))
    have hQ : (zeroJumpMarket M).Q a p = μs.bind (fun s => Measure.dirac (p.1 + s, (zeroJumpMarket M).phi a s p.2)) :=
      zeroJumpMarket_Q_eq M a p
    let S : Set (ℝ × ℝ) := {q | wBond M q ≠ wBond M p}
    have hS_meas : MeasurableSet S := (isOpen_ne.preimage (continuous_wBond M)).measurableSet
    have hQS : ((zeroJumpMarket M).Q a p) S = 0 := by
      rw [hQ, Measure.bind_apply hS_meas hdirac_meas.aemeasurable]
      have h_ind : ∀ s ∈ Set.Ioo (0 : ℝ) (M.T - p.1),
          (Measure.dirac (p.1 + s, (zeroJumpMarket M).phi a s p.2)) S = 0 := by
        intro s hs
        rw [Measure.dirac_apply' _ hS_meas, Set.indicator_of_notMem]
        change ¬ (wBond M _ ≠ wBond M p)
        rw [not_not]
        unfold wBond
        rw [phi_nonneg_of_uncontrolled (zeroJumpMarket M) hun a hs.1.le p.2]
        have h_nonneg : 0 ≤ p.2 * Real.exp (M.rho * s) := mul_nonneg hp2 (Real.exp_pos _).le
        change M.U (max 0 (p.2 * Real.exp (M.rho * s)) * Real.exp (M.rho * (M.T - (p.1 + s)))) = _
        rw [max_eq_right h_nonneg, max_eq_right hp2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      have h_ae_res : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))),
          (Measure.dirac (p.1 + s, (zeroJumpMarket M).phi a s p.2)) S = 0 :=
        (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall h_ind)
      have h_ae_μs : ∀ᵐ s ∂μs, (Measure.dirac (p.1 + s, (zeroJumpMarket M).phi a s p.2)) S = 0 :=
        withDensity_absolutelyContinuous _ _ h_ae_res
      rw [lintegral_congr_ae h_ae_μs, lintegral_zero]
    have hae : wBond M =ᵐ[(zeroJumpMarket M).Q a p] fun _ => wBond M p := by
      rw [Filter.EventuallyEq, ae_iff]
      exact hQS
    have h_univ : ((zeroJumpMarket M).Q a p) Set.univ = ENNReal.ofReal (1 - Real.exp (-M.lam * (M.T - p.1))) := by
      rw [hQ, Measure.bind_apply MeasurableSet.univ hdirac_meas.aemeasurable]
      simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, lintegral_const, one_mul]
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_lam_exp M.lam M.lam_pos (M.T - p.1) hsub
    have h_int : ∫ q, wBond M q ∂((zeroJumpMarket M).Q a p) =
        (1 - Real.exp (-M.lam * (M.T - p.1))) * wBond M p := by
      rw [integral_congr_ae hae, integral_const, smul_eq_mul]
      congr 1
      rw [Measure.real, h_univ, ENNReal.toReal_ofReal]
      linarith [Real.exp_le_one_iff.mpr (by nlinarith [M.lam_pos] : -M.lam * (M.T - p.1) ≤ 0)]
    rw [hr, h_int]
    ring
  have hset : {y : ℝ | ∃ a : Control d, y = (zeroJumpMarket M).r a p + ∫ q, wBond M q ∂((zeroJumpMarket M).Q a p)} =
      {wBond M p} := by
    ext y
    simp only [Set.mem_ofPred, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl⟩; exact hval a
    · rintro rfl; exact ⟨c0, (hval c0).symm⟩
  rw [hset]
  exact isLUB_singleton

lemma zeroJumpMarket_IMcv_wBond (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (gamma0 alpha0 : ℝ) (hb0 : (zeroJumpMarket M).IsBoundingFunction ((zeroJumpMarket M).bfun gamma0) alpha0)
    (c0 : Control d) :
    (zeroJumpMarket M).IMcv ((zeroJumpMarket M).bfun gamma0) (wBond M) := by
  obtain ⟨hbf_pos, ⟨cr, hcr⟩, -⟩ := hb0
  refine ⟨?_, (continuous_wBond M).continuousOn, ?_, ?_, ?_, ?_⟩
  · refine ⟨Real.exp (M.lam * M.T) * |cr|, fun p hp => ?_⟩
    have hpt : p.1 ≤ M.T := hp.1.2
    have hpt0 : 0 ≤ p.1 := hp.1.1
    have hp2 : 0 ≤ p.2 := hp.2
    have hsub : 0 ≤ M.T - p.1 := sub_nonneg.mpr hpt
    have hr : (zeroJumpMarket M).r c0 p = Real.exp (-M.lam * (M.T - p.1)) * wBond M p := by
      unfold JumpMarket.r wBond
      change Real.exp (-M.lam * (M.T - p.1)) * M.U ((zeroJumpMarket M).phi c0 (M.T - p.1) p.2) = _
      rw [phi_nonneg_of_uncontrolled (zeroJumpMarket M) hun c0 hsub p.2, max_eq_right hp2]
      rfl
    have hw_eq : wBond M p = Real.exp (M.lam * (M.T - p.1)) * (zeroJumpMarket M).r c0 p := by
      rw [hr, ← mul_assoc, ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero, one_mul]
    rw [hw_eq, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
    refine mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [M.lam_pos])) ?_ (abs_nonneg _) (Real.exp_pos _).le
    calc |(zeroJumpMarket M).r c0 p| ≤ cr * (zeroJumpMarket M).bfun gamma0 p := hcr p hp c0
      _ ≤ |cr| * (zeroJumpMarket M).bfun gamma0 p :=
        mul_le_mul_of_nonneg_right (le_abs_self cr) (hbf_pos p hp).le
  · intro t _
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hx0 : 0 ≤ x := Set.mem_Ici.mp hx
    have hy0 : 0 ≤ y := Set.mem_Ici.mp hy
    have habx : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
    dsimp only [wBond, smul_eq_mul]
    rw [max_eq_right hx0, max_eq_right hy0, max_eq_right habx]
    let c := Real.exp (M.rho * (M.T - t))
    have hc : 0 ≤ c := (Real.exp_pos _).le
    have h := M.U_concave.concaveOn.2 (mul_nonneg hx0 hc) (mul_nonneg hy0 hc) ha hb hab
    simpa only [c, smul_eq_mul, add_mul, mul_assoc] using h
  · intro t _ x1 hx1 x2 hx2 hle
    dsimp [wBond]
    rw [max_eq_right (Set.mem_Ici.mp hx1), max_eq_right (Set.mem_Ici.mp hx2)]
    have h1 : 0 ≤ x1 * Real.exp (M.rho * (M.T - t)) := mul_nonneg hx1 (Real.exp_pos _).le
    have h2 : 0 ≤ x2 * Real.exp (M.rho * (M.T - t)) := mul_nonneg hx2 (Real.exp_pos _).le
    exact M.U_mono.monotoneOn h1 h2 (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le)
  · intro x hx t1 _ t2 _ hle
    dsimp [wBond]
    rw [max_eq_right hx]
    have h1 : 0 ≤ x * Real.exp (M.rho * (M.T - t2)) := mul_nonneg hx (Real.exp_pos _).le
    have h2 : 0 ≤ x * Real.exp (M.rho * (M.T - t1)) := mul_nonneg hx (Real.exp_pos _).le
    refine M.U_mono.monotoneOn h1 h2 (mul_le_mul_of_nonneg_left ?_ hx)
    exact Real.exp_le_exp.mpr (by nlinarith [M.rho_nonneg])
  · intro p hp
    dsimp [wBond]
    rw [max_eq_right hp.2]
    have hsub : 0 ≤ M.T - p.1 := sub_nonneg.mpr hp.1.2
    have h1 : 1 ≤ Real.exp (M.rho * (M.T - p.1)) :=
      Real.one_le_exp (mul_nonneg M.rho_nonneg hsub)
    have h2 : p.2 ≤ p.2 * Real.exp (M.rho * (M.T - p.1)) := by
      calc p.2 = p.2 * 1 := (mul_one _).symm
        _ ≤ p.2 * Real.exp (M.rho * (M.T - p.1)) := mul_le_mul_of_nonneg_left h1 hp.2
    exact M.U_mono.monotoneOn hp.2 (mul_nonneg hp.2 (Real.exp_pos _).le) h2

lemma Jstat_bond_eq (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g))
    (bond : ℝ × ℝ → Control d) (hbond : ∀ p, (bond p).val = fun _ _ => 0) :
    ∀ p ∈ M.E, M.Jstat Pr bond p = ENNReal.ofReal (wBond M p) := by
  let M0 := zeroJumpMarket M
  obtain ⟨gamma0, hgamma0, hprop⟩ := (proposition_9_3_2 M0).2.2
  obtain ⟨halpha0_lt, hb0⟩ := hprop gamma0 le_rfl
  have hb0_max := isBoundingFunction_max_zero M0 (M0.bfun gamma0) (M0.alphaGamma gamma0) hb0
  have halpha0_max_lt : max 0 (M0.alphaGamma gamma0) < 1 := max_lt zero_lt_one halpha0_lt
  let Pr0 : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ) := fun _ => Pr (ofMarkov fun _ => bond)
  have hPr0 : ∀ g, M0.IsChainLaw g (Pr0 g) := by
    intro g
    obtain ⟨hprob, hcyl⟩ := hPr (ofMarkov fun _ => bond)
    refine ⟨hprob, fun p m B hB => ?_⟩
    rw [hcyl p m B hB]
    congr 1
    ext q
    exact (zeroJumpMarket_chainCyl_eq M hun bond hbond g m 0 (fun _ => q) (fun i => B (i + 1))).symm
  obtain ⟨v0, hv0_imcv, hv0_V, -, -, ⟨hv0_T, hv0_uniq⟩, -, ⟨fstar, -, -, hfstar_J⟩, -, -⟩ :=
    theorem_9_3_4 M0 gamma0 (max 0 (M0.alphaGamma gamma0)) hb0_max (le_max_left _ _) halpha0_max_lt Pr0 hPr0
  have hw_imcv : M0.IMcv (M0.bfun gamma0) (wBond M) :=
    zeroJumpMarket_IMcv_wBond M hun gamma0 (M0.alphaGamma gamma0) hb0 (bond (0, 0))
  have hw_T : M0.IsTOf (wBond M) (wBond M) :=
    zeroJumpMarket_IsTOf_wBond M hun (bond (0, 0))
  have hw_eq_v0 : ∀ p ∈ M.E, wBond M p = v0 p := hv0_uniq (wBond M) hw_imcv hw_T
  intro p hp
  have hJ_eq : M.Jstat Pr bond p = M0.Jstat Pr0 fstar p := by
    unfold JumpMarket.Jstat JumpMarket.Jinfpi
    congr 1 with w
    congr 1 with k
    have hT : M0.T = M.T := rfl
    have hr_eq : M.r (bond (w k)) (w k) = M0.r (fstar (w k)) (w k) := by
      unfold JumpMarket.r
      change Real.exp (-M.lam * (M.T - (w k).1)) * M.U (M.phi (bond (w k)) (M.T - (w k).1) (w k).2) =
        Real.exp (-M.lam * (M.T - (w k).1)) * M.U ((zeroJumpMarket M).phi (fstar (w k)) (M.T - (w k).1) (w k).2)
      rw [phi_eq_of_uncontrolled M hun, phi_eq_of_uncontrolled (zeroJumpMarket M) hun]
      rfl
    rw [hT, hr_eq]
  rw [hJ_eq, hfstar_J p hp, hv0_V p hp, hw_eq_v0 p hp]

lemma measurable_map_of_measurable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure β) [SFinite ν] (F : α → β → γ) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun a => ν.map (F a)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have h1 : ∀ a, (ν.map (F a)) s = ∫⁻ b, s.indicator 1 (F a b) ∂ν := by
    intro a
    rw [Measure.map_apply (hF.of_uncurry_left) hs, ← lintegral_indicator_one (hF.of_uncurry_left hs)]
    rfl
  simp_rw [h1]
  exact ((measurable_one.indicator hs).comp hF).lintegral_prod_right'

lemma measurable_Q_kernel (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (a : Control d) (p : ℝ × ℝ) :
    Measurable (fun s : ℝ => M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))) := by
  have := M.QY_prob
  refine measurable_map_of_measurable M.QY _ ?_
  refine Measurable.prodMk (measurable_const.add measurable_fst) ?_
  refine ((measurable_phi_of_uncontrolled M hun a p.2).comp measurable_fst).mul (measurable_const.add ?_)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp (a.meas.comp measurable_fst)).mul ((measurable_pi_apply i).comp measurable_snd)

lemma ae_QY_gt_neg_one (M : JumpMarket d) : ∀ᵐ y ∂M.QY, ∀ i : Fin d, -1 < y i := by
  rw [ae_iff]
  convert M.QY_supp using 2
  ext y
  simp [not_forall]

lemma one_add_sum_nonneg_of_gt_neg_one {u y : Fin d → ℝ} (hu : u ∈ Ucal d) (hy : ∀ i, -1 < y i) :
    0 ≤ 1 + ∑ i, u i * y i := by
  have h1 : -∑ i, u i ≤ ∑ i, u i * y i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := hu.1 i
    have hyi := (hy i).le
    nlinarith
  linarith [hu.2]

lemma ae_Q_mem_E (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (a : Control d) {p : ℝ × ℝ} (hp : p ∈ M.E) :
    ∀ᵐ q ∂(M.Q a p), q ∈ M.E := by
  have hE_meas : MeasurableSet M.E := measurableSet_Icc.prod measurableSet_Ici
  rw [ae_iff]
  change (M.Q a p) M.Eᶜ = 0
  unfold JumpMarket.Q
  rw [Measure.bind_apply hE_meas.compl (measurable_Q_kernel M hun a p).aemeasurable]
  have h_ind : ∀ s ∈ Set.Ioo (0 : ℝ) (M.T - p.1),
      (M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))) M.Eᶜ = 0 := by
    intro s hs
    have hm1 : Measurable (fun y : Fin d → ℝ => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i))) := by
      refine Measurable.prodMk measurable_const (measurable_const.mul (measurable_const.add ?_))
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
    rw [Measure.map_apply hm1 hE_meas.compl]
    have h_ae : ∀ᵐ y ∂M.QY, (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)) ∈ M.E := by
      filter_upwards [ae_QY_gt_neg_one M] with y hy
      refine ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hs.2]⟩, ?_⟩
      rw [phi_nonneg_of_uncontrolled M hun a hs.1.le p.2]
      exact mul_nonneg (mul_nonneg hp.2 (Real.exp_pos _).le) (one_add_sum_nonneg_of_gt_neg_one (a.mem s) hy)
    exact ae_iff.mp h_ae
  have h_ae_res : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1))),
      (M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i)))) M.Eᶜ = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall h_ind)
  have h_ae_μs := withDensity_absolutelyContinuous (volume.restrict (Set.Ioo (0 : ℝ) (M.T - p.1)))
    (fun s => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) h_ae_res
  rw [lintegral_congr_ae h_ae_μs, lintegral_zero]

lemma L_Jstat_bond_eq (M : JumpMarket d) (hun : ∀ i, M.mu i = M.rho)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g))
    (bond : ℝ × ℝ → Control d) (hbond : ∀ p, (bond p).val = fun _ _ => 0)
    (a : Control d) {p : ℝ × ℝ} (hp : p ∈ M.E) :
    M.L (M.Jstat Pr bond) a p =
      ENNReal.ofReal (Real.exp (-M.lam * (M.T - p.1)) * wBond M p) +
      ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - p.1),
        ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          (∫⁻ y, ENNReal.ofReal (M.U (max 0 (p.2 * Real.exp (M.rho * (M.T - p.1)) *
            (1 + ∑ i, a.val s i * y i)))) ∂M.QY) := by
  unfold JumpMarket.L
  have hsub : 0 ≤ M.T - p.1 := sub_nonneg.mpr hp.1.2
  have hr : M.r a p = Real.exp (-M.lam * (M.T - p.1)) * wBond M p := by
    unfold JumpMarket.r wBond
    rw [phi_nonneg_of_uncontrolled M hun a hsub p.2, max_eq_right hp.2]
  rw [hr]
  congr 1
  have hae : M.Jstat Pr bond =ᵐ[M.Q a p] fun q => ENNReal.ofReal (wBond M q) := by
    filter_upwards [ae_Q_mem_E M hun a hp] with q hq
    exact Jstat_bond_eq M hun Pr hPr bond hbond q hq
  rw [lintegral_congr_ae hae]
  have hw_meas : Measurable (fun q => ENNReal.ofReal (wBond M q)) :=
    ENNReal.measurable_ofReal.comp (continuous_wBond M).measurable
  unfold JumpMarket.Q
  rw [Measure.lintegral_bind (measurable_Q_kernel M hun a p).aemeasurable hw_meas.aemeasurable]
  have h_dens_meas : Measurable (fun s : ℝ => ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))
  have h_inner_meas : Measurable (fun s : ℝ => ∫⁻ q, ENNReal.ofReal (wBond M q) ∂(M.QY.map (fun y => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i))))) :=
    (Measure.measurable_lintegral hw_meas).comp (measurable_Q_kernel M hun a p)
  rw [lintegral_withDensity_eq_lintegral_mul _ h_dens_meas h_inner_meas]
  refine setLIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  dsimp [Pi.mul_apply]
  congr 1
  have hm1 : Measurable (fun y : Fin d → ℝ => (p.1 + s, M.phi a s p.2 * (1 + ∑ i, a.val s i * y i))) := by
    refine Measurable.prodMk measurable_const (measurable_const.mul (measurable_const.add ?_))
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  rw [lintegral_map hw_meas hm1]
  congr 1 with y
  unfold wBond
  dsimp
  rw [phi_nonneg_of_uncontrolled M hun a hs.1.le p.2]
  have h_exp_pos : 0 ≤ Real.exp (M.rho * (M.T - (p.1 + s))) := (Real.exp_pos _).le
  rw [max_mul_of_nonneg _ _ h_exp_pos, zero_mul]
  congr 3
  calc p.2 * Real.exp (M.rho * s) * (1 + ∑ i, a.val s i * y i) * Real.exp (M.rho * (M.T - (p.1 + s)))
      = p.2 * (Real.exp (M.rho * s) * Real.exp (M.rho * (M.T - (p.1 + s)))) * (1 + ∑ i, a.val s i * y i) := by ring
    _ = p.2 * Real.exp (M.rho * (M.T - p.1)) * (1 + ∑ i, a.val s i * y i) := by
        rw [← Real.exp_add]
        congr 3
        ring

lemma differentiableAt_U_of_pos (M : JumpMarket d) (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ M.U z :=
  (hU1.differentiableOn one_ne_zero).differentiableAt (IsOpen.mem_nhds isOpen_Ioi hz)

lemma concave_le_tangent (M : JumpMarket d) (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    {z x : ℝ} (hz : 0 < z) (hx : 0 ≤ x) :
    M.U x ≤ M.U z + deriv M.U z * (x - z) := by
  have hdiff := differentiableAt_U_of_pos M hU1 hz
  rcases lt_trichotomy z x with hlt | rfl | hgt
  · have h := M.U_concave.concaveOn.slope_le_deriv hz.le hx hlt hdiff
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hlt)] at h
    linarith
  · simp
  · have h := M.U_concave.concaveOn.deriv_le_slope hx hz.le hgt hdiff
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hgt)] at h
    linarith

lemma deriv_U_pos (M : JumpMarket d) (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    0 < deriv M.U z := by
  have h1 := concave_le_tangent M hU1 hz (by linarith : 0 ≤ z + 1)
  have h2 : M.U z < M.U (z + 1) := M.U_mono hz.le (by linarith : 0 ≤ z + 1) (by linarith)
  linarith

lemma deriv_U_antitone (M : JumpMarket d) (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    {z1 z2 : ℝ} (hz1 : 0 < z1) (hle : z1 ≤ z2) :
    deriv M.U z2 ≤ deriv M.U z1 := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact le_rfl
  · have h1 := concave_le_tangent M hU1 hz1 (hz1.trans hlt).le
    have h2 := concave_le_tangent M hU1 (hz1.trans hlt) hz1.le
    have h3 : 0 ≤ (deriv M.U z1 - deriv M.U z2) * (z2 - z1) := by linarith
    have h4 : 0 ≤ deriv M.U z1 - deriv M.U z2 := nonneg_of_mul_nonneg_left h3 (sub_pos.mpr hlt)
    linarith

lemma integrable_coord_QY (M : JumpMarket d) (i : Fin d) :
    Integrable (fun y : Fin d → ℝ => y i) M.QY := by
  have hid : Integrable (id : (Fin d → ℝ) → (Fin d → ℝ)) M.QY :=
    ⟨measurable_id.aestronglyMeasurable, M.QY_integrable⟩
  exact (integrable_pi_iff.mp hid) i

lemma lintegral_U_le_of_EY_nonpos (M : JumpMarket d) (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    (hEY : ∀ i : Fin d, ∫ y, y i ∂M.QY ≤ 0)
    {z : ℝ} (hz : 0 ≤ z) {u : Fin d → ℝ} (hu : u ∈ Ucal d) :
    ∫⁻ y, ENNReal.ofReal (M.U (max 0 (z * (1 + ∑ i, u i * y i)))) ∂M.QY ≤
      ENNReal.ofReal (M.U z) := by
  have := M.QY_prob
  rcases eq_or_lt_of_le hz with rfl | hz_pos
  · simp [lintegral_const]
  · let g : (Fin d → ℝ) → ℝ := fun y => M.U z + ∑ i : Fin d, (deriv M.U z * z * u i) * y i
    have hg_int : Integrable g M.QY :=
      (integrable_const (M.U z)).add
        (integrable_finset_sum _ fun i _ => (integrable_coord_QY M i).const_mul _)
    have h_ae : ∀ᵐ y ∂M.QY, 0 ≤ M.U (max 0 (z * (1 + ∑ i, u i * y i))) ∧
        M.U (max 0 (z * (1 + ∑ i, u i * y i))) ≤ g y := by
      filter_upwards [ae_QY_gt_neg_one M] with y hy
      have h1 : 0 ≤ z * (1 + ∑ i, u i * y i) :=
        mul_nonneg hz_pos.le (one_add_sum_nonneg_of_gt_neg_one hu hy)
      rw [max_eq_right h1]
      refine ⟨M.U_nonneg _ h1, ?_⟩
      have htan := concave_le_tangent M hU1 hz_pos h1
      have h_eq : M.U z + deriv M.U z * (z * (1 + ∑ i, u i * y i) - z) = g y := by
        dsimp [g]
        rw [show z * (1 + ∑ i, u i * y i) - z = z * ∑ i, u i * y i by ring,
            ← mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
      linarith
    have hg_nonneg : 0 ≤ᵐ[M.QY] g := by
      filter_upwards [h_ae] with y hy using hy.1.trans hy.2
    have h_le : ∫⁻ y, ENNReal.ofReal (M.U (max 0 (z * (1 + ∑ i, u i * y i)))) ∂M.QY ≤
        ∫⁻ y, ENNReal.ofReal (g y) ∂M.QY := by
      refine lintegral_mono_ae ?_
      filter_upwards [h_ae] with y hy using ENNReal.ofReal_le_ofReal hy.2
    rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg] at h_le
    refine h_le.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp [g]
    rw [integral_add (integrable_const _) (integrable_finset_sum _ fun i _ => (integrable_coord_QY M i).const_mul _),
        integral_const, probReal_univ, one_smul,
        integral_finset_sum _ fun i _ => (integrable_coord_QY M i).const_mul _]
    have hsum_le : ∑ i : Fin d, ∫ y, (deriv M.U z * z * u i) * y i ∂M.QY ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      rw [integral_const_mul]
      have h_coeff : 0 ≤ deriv M.U z * z * u i :=
        mul_nonneg (mul_nonneg (deriv_U_pos M hU1 hz_pos).le hz_pos.le) (hu.1 i)
      exact mul_nonpos_of_nonneg_of_nonpos h_coeff (hEY i)
    linarith

lemma lintegral_U_gt_of_EY_pos (M : JumpMarket d) (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    (hUint : ∀ x : ℝ, 0 < x → ∃ ε > (0 : ℝ), ∀ u : Fin d → ℝ, ‖u‖ < ε →
      ∀ i : Fin d, Integrable (fun y : Fin d → ℝ => deriv M.U (x + ∑ j, u j * y j) * y i) M.QY)
    {z : ℝ} (hz : 0 < z) {i0 : Fin d} (hEY : 0 < ∫ y, y i0 ∂M.QY) :
    ∃ u : Fin d → ℝ, u ∈ Ucal d ∧
      ENNReal.ofReal (M.U z) <
        ∫⁻ y, ENNReal.ofReal (M.U (max 0 (z * (1 + ∑ i, u i * y i)))) ∂M.QY := by
  have := M.QY_prob
  obtain ⟨ε, hε, hUint_z⟩ := hUint z hz
  let δ0 : ℝ := min (1 / 2) (ε / (2 * z))
  have hδ0_pos : 0 < δ0 := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ0_le_half : δ0 ≤ 1 / 2 := min_le_left _ _
  have hδ0_le_eps : δ0 ≤ ε / (2 * z) := min_le_right _ _
  have h_int_δ : ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ0 →
      Integrable (fun y : Fin d → ℝ => deriv M.U (z + (δ * z) * y i0) * y i0) M.QY := by
    intro δ hδ0 hδ_le
    let u : Fin d → ℝ := Pi.single i0 (δ * z)
    have hu_norm : ‖u‖ < ε := by
      have h1 : ‖u‖ ≤ δ * z := by
        refine (pi_norm_le_iff_of_nonneg (mul_nonneg hδ0 hz.le)).mpr fun j => ?_
        rcases eq_or_ne j i0 with rfl | hne
        · simp [u, Real.norm_of_nonneg (mul_nonneg hδ0 hz.le)]
        · simp [u, hne, mul_nonneg hδ0 hz.le]
      have h2 : δ * z ≤ δ0 * z := mul_le_mul_of_nonneg_right hδ_le hz.le
      have h3 : δ0 * z ≤ ε / 2 := by
        have := (le_div_iff₀ (by linarith : 0 < 2 * z)).mp hδ0_le_eps
        linarith
      linarith
    have h_int := hUint_z u hu_norm i0
    convert h_int using 2 with y
    congr 2
    rw [Fintype.sum_eq_single i0 (fun j hj => by simp [u, hj])]
    simp [u]
  let δn : ℕ → ℝ := fun n => δ0 / ((n : ℝ) + 1)
  have hδn_pos : ∀ n, 0 < δn n := fun n => div_pos hδ0_pos (by positivity)
  have hδn_le : ∀ n, δn n ≤ δ0 := fun n => div_le_self hδ0_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let Fn : ℕ → (Fin d → ℝ) → ℝ := fun n y => deriv M.U (z + (δn n * z) * y i0) * y i0
  let F0 : (Fin d → ℝ) → ℝ := fun y => deriv M.U z * y i0
  let Fδ0 : (Fin d → ℝ) → ℝ := fun y => deriv M.U (z + (δ0 * z) * y i0) * y i0
  have hF0_int : Integrable F0 M.QY := (integrable_coord_QY M i0).const_mul (deriv M.U z)
  have hFδ0_int : Integrable Fδ0 M.QY := h_int_δ δ0 hδ0_pos.le le_rfl
  let bound : (Fin d → ℝ) → ℝ := fun y => ‖F0 y‖ + ‖Fδ0 y‖
  have hbound_int : Integrable bound M.QY := hF0_int.norm.add hFδ0_int.norm
  have hFn_meas : ∀ n, AEStronglyMeasurable (Fn n) M.QY :=
    fun n => (h_int_δ (δn n) (hδn_pos n).le (hδn_le n)).aestronglyMeasurable
  have hFn_bound : ∀ n, ∀ᵐ y ∂M.QY, ‖Fn n y‖ ≤ bound y := by
    intro n
    filter_upwards [ae_QY_gt_neg_one M] with y hy
    have hy0 : -1 < y i0 := hy i0
    have hδn_lt : δn n ≤ 1 / 2 := (hδn_le n).trans hδ0_le_half
    have h_prod_n_nonneg : 0 ≤ δn n * z := mul_nonneg (hδn_pos n).le hz.le
    have h_prod_n_le : δn n * z ≤ z / 2 := by nlinarith
    have h_prod_0_nonneg : 0 ≤ δ0 * z := mul_nonneg hδ0_pos.le hz.le
    have h_prod_0_le : δ0 * z ≤ z / 2 := by nlinarith
    have hz_n : 0 < z + (δn n * z) * y i0 := by nlinarith
    have hz_0 : 0 < z + (δ0 * z) * y i0 := by nlinarith
    rcases le_or_gt 0 (y i0) with hy_nonneg | hy_neg
    · have hle : deriv M.U (z + (δn n * z) * y i0) ≤ deriv M.U z :=
        deriv_U_antitone M hU1 hz (by nlinarith)
      have hpos : 0 ≤ deriv M.U (z + (δn n * z) * y i0) := (deriv_U_pos M hU1 hz_n).le
      have hnorm : ‖Fn n y‖ ≤ ‖F0 y‖ := by
        change ‖deriv M.U (z + (δn n * z) * y i0) * y i0‖ ≤ ‖deriv M.U z * y i0‖
        rw [norm_mul, norm_mul, Real.norm_of_nonneg hpos, Real.norm_of_nonneg (deriv_U_pos M hU1 hz).le]
        exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      exact hnorm.trans (le_add_of_nonneg_right (norm_nonneg _))
    · have h_prod_le_0 : δn n * z ≤ δ0 * z := mul_le_mul_of_nonneg_right (hδn_le n) hz.le
      have hle_z : z + (δ0 * z) * y i0 ≤ z + (δn n * z) * y i0 := by nlinarith
      have hle : deriv M.U (z + (δn n * z) * y i0) ≤ deriv M.U (z + (δ0 * z) * y i0) :=
        deriv_U_antitone M hU1 hz_0 hle_z
      have hpos : 0 ≤ deriv M.U (z + (δn n * z) * y i0) := (deriv_U_pos M hU1 hz_n).le
      have hpos0 : 0 ≤ deriv M.U (z + (δ0 * z) * y i0) := (deriv_U_pos M hU1 hz_0).le
      have hnorm : ‖Fn n y‖ ≤ ‖Fδ0 y‖ := by
        change ‖deriv M.U (z + (δn n * z) * y i0) * y i0‖ ≤ ‖deriv M.U (z + (δ0 * z) * y i0) * y i0‖
        rw [norm_mul, norm_mul, Real.norm_of_nonneg hpos, Real.norm_of_nonneg hpos0]
        exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      exact hnorm.trans (le_add_of_nonneg_left (norm_nonneg _))
  have h_deriv_cont : ContinuousAt (deriv M.U) z :=
    (hU1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).continuousAt (IsOpen.mem_nhds isOpen_Ioi hz)
  have hδn_tendsto : Tendsto δn atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hFn_tendsto : ∀ᵐ y ∂M.QY, Tendsto (fun n => Fn n y) atTop (𝓝 (F0 y)) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h_inner : Tendsto (fun n => z + (δn n * z) * y i0) atTop (𝓝 z) := by
      have h1 : Tendsto (fun n => (δn n * z) * y i0) atTop (𝓝 ((0 * z) * y i0)) :=
        (hδn_tendsto.mul_const z).mul_const (y i0)
      simpa using tendsto_const_nhds.add h1
    exact (h_deriv_cont.tendsto.comp h_inner).mul_const (y i0)
  have h_int_tendsto := tendsto_integral_of_dominated_convergence bound hFn_meas hbound_int hFn_bound hFn_tendsto
  have hF0_pos : 0 < ∫ y, F0 y ∂M.QY := by
    dsimp [F0]
    rw [integral_const_mul]
    exact mul_pos (deriv_U_pos M hU1 hz) hEY
  obtain ⟨N, hN⟩ := ( (tendsto_order.mp h_int_tendsto).1 0 hF0_pos ).exists
  let δ := δn N
  let u : Fin d → ℝ := Pi.single i0 δ
  refine ⟨u, ?_, ?_⟩
  · refine ⟨fun i => ?_, ?_⟩
    · rcases eq_or_ne i i0 with rfl | hne
      · simp [u, δ, (hδn_pos N).le]
      · simp [u, hne]
    · rw [Fintype.sum_eq_single i0 (fun j hj => by simp [u, hj])]
      dsimp [u]
      rw [Pi.single_eq_same]
      exact (hδn_le N).trans (hδ0_le_half.trans (by norm_num))
  · have h_int_N : Integrable (Fn N) M.QY := h_int_δ δ (hδn_pos N).le (hδn_le N)
    let h : (Fin d → ℝ) → ℝ := fun y => M.U z + (δ * z) * Fn N y
    have hh_int : Integrable h M.QY := (integrable_const (M.U z)).add (h_int_N.const_mul (δ * z))
    have hh_max_int : Integrable (fun y => max 0 (h y)) M.QY := (integrable_const 0).sup hh_int
    have hh_int_val : ∫ y, h y ∂M.QY = M.U z + (δ * z) * ∫ y, Fn N y ∂M.QY := by
      dsimp [h]
      rw [integral_add (integrable_const _) (h_int_N.const_mul _), integral_const, probReal_univ, one_smul,
          integral_const_mul]
    have h_strict : ENNReal.ofReal (M.U z) < ENNReal.ofReal (∫ y, max 0 (h y) ∂M.QY) := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (M.U_nonneg z hz.le)]
      have h_pos_term : 0 < (δ * z) * ∫ y, Fn N y ∂M.QY := mul_pos (mul_pos (hδn_pos N) hz) hN
      have h_le_max : ∫ y, h y ∂M.QY ≤ ∫ y, max 0 (h y) ∂M.QY :=
        integral_mono hh_int hh_max_int (fun y => le_max_right 0 (h y))
      linarith
    have h_eq_lint : ENNReal.ofReal (∫ y, max 0 (h y) ∂M.QY) = ∫⁻ y, ENNReal.ofReal (max 0 (h y)) ∂M.QY :=
      ofReal_integral_eq_lintegral_ofReal hh_max_int (Filter.Eventually.of_forall fun y => le_max_left 0 (h y))
    rw [h_eq_lint] at h_strict
    refine h_strict.trans_le (lintegral_mono_ae ?_)
    filter_upwards [ae_QY_gt_neg_one M] with y hy
    apply ENNReal.ofReal_le_ofReal
    have hy0 : -1 < y i0 := hy i0
    have hδ_lt : δ ≤ 1 / 2 := (hδn_le N).trans hδ0_le_half
    have h_prod_nonneg : 0 ≤ δ * z := mul_nonneg (hδn_pos N).le hz.le
    have h_prod_le : δ * z ≤ z / 2 := by nlinarith
    have hsum : ∑ i, u i * y i = δ * y i0 := by
      rw [Fintype.sum_eq_single i0 (fun j hj => by simp [u, hj])]
      simp [u]
    rw [hsum]
    have h1 : 0 < z * (1 + δ * y i0) := by nlinarith
    rw [max_eq_right h1.le]
    refine max_le (M.U_nonneg _ h1.le) ?_
    have htan := concave_le_tangent M hU1 h1 hz.le
    have h_eq : z + (δ * z) * y i0 = z * (1 + δ * y i0) := by ring
    dsimp [h, Fn, δ] at htan ⊢
    rw [h_eq]
    nlinarith

end SolTheorem936

open SolTheorem936

theorem solution {d : ℕ} (M : JumpMarket d)
    (huncontrolled : ∀ i : Fin d, M.mu i = M.rho)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    (hUint : ∀ x : ℝ, 0 < x → ∃ ε > (0 : ℝ), ∀ u : Fin d → ℝ, ‖u‖ < ε →
      ∀ i : Fin d, Integrable (fun y : Fin d → ℝ => deriv M.U (x + ∑ j, u j * y j) * y i) M.QY)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g))
    (bond : ℝ × ℝ → Control d)
    (hbond : ∀ p : ℝ × ℝ, (bond p).val = fun _ _ => 0) :
    ((∀ p ∈ M.E, M.Jstat Pr bond p = M.V Pr p) ↔ ∀ i : Fin d, ∫ y, y i ∂M.QY ≤ 0) := by
  have hb_max := isBoundingFunction_max_zero M (M.bfun gamma) alpha hb
  have halpha_max_lt : max 0 alpha < 1 := max_lt zero_lt_one halpha
  obtain ⟨v, -, hV, hJinf, -, -, -, -, -, h_howard, h_no_imp⟩ :=
    theorem_9_3_4 M gamma (max 0 alpha) hb_max (le_max_left 0 alpha) halpha_max_lt Pr hPr
  have hbond_const : bond = fun _ => bond (0, 0) := by
    ext p : 1
    exact control_ext (by rw [hbond p, hbond (0, 0)])
  have hbond_meas : Measurable bond := by
    rw [hbond_const]
    exact measurable_const
  constructor
  · intro h_opt i0
    by_contra! h_pos
    let p0 : ℝ × ℝ := (0, 1)
    have hp0 : p0 ∈ M.E := ⟨⟨le_rfl, M.T_pos.le⟩, Set.mem_Ici.mpr zero_le_one⟩
    let z0 : ℝ := Real.exp (M.rho * M.T)
    have hz0 : 0 < z0 := Real.exp_pos _
    obtain ⟨u, hu_mem, hu_gt⟩ := lintegral_U_gt_of_EY_pos M hU1 hUint hz0 h_pos
    let a_u : Control d := ⟨fun _ => u, measurable_const, fun _ => hu_mem⟩
    have hL_gt : M.Jstat Pr bond p0 < M.L (M.Jstat Pr bond) a_u p0 := by
      rw [Jstat_bond_eq M huncontrolled Pr hPr bond hbond p0 hp0,
          L_Jstat_bond_eq M huncontrolled Pr hPr bond hbond a_u hp0]
      dsimp [p0]
      simp only [sub_zero, one_mul]
      have hw0 : wBond M (0, 1) = M.U z0 := by
        unfold wBond
        dsimp [z0]
        rw [max_eq_right zero_le_one, sub_zero, one_mul]
      rw [hw0]
      simp only [a_u]
      have h_pull : ∫⁻ s in Set.Ioo (0 : ℝ) M.T,
          ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
            (∫⁻ y, ENNReal.ofReal (M.U (max 0 (z0 * (1 + ∑ i, u i * y i)))) ∂M.QY) =
          (∫⁻ s in Set.Ioo (0 : ℝ) M.T, ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) *
            (∫⁻ y, ENNReal.ofReal (M.U (max 0 (z0 * (1 + ∑ i, u i * y i)))) ∂M.QY) :=
        lintegral_mul_const _
          (ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))))
      rw [h_pull, lintegral_lam_exp M.lam M.lam_pos M.T M.T_pos.le]
      have h_exp_lt : Real.exp (-M.lam * M.T) < 1 :=
        Real.exp_lt_one_iff.mpr (by nlinarith [M.lam_pos, M.T_pos])
      have h_one_sub_pos : 0 < 1 - Real.exp (-M.lam * M.T) := sub_pos.mpr h_exp_lt
      have h_lhs : ENNReal.ofReal (M.U z0) =
          ENNReal.ofReal (Real.exp (-M.lam * M.T) * M.U z0) +
            ENNReal.ofReal (1 - Real.exp (-M.lam * M.T)) * ENNReal.ofReal (M.U z0) := by
        rw [← ENNReal.ofReal_mul h_one_sub_pos.le,
            ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (M.U_nonneg z0 hz0.le))
              (mul_nonneg h_one_sub_pos.le (M.U_nonneg z0 hz0.le))]
        congr 1
        ring
      rw [h_lhs]
      refine ENNReal.add_lt_add_left (ENNReal.ofReal_ne_top) ?_
      exact ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr h_one_sub_pos).ne' ENNReal.ofReal_ne_top hu_gt
    let h_pol : ℝ × ℝ → Control d := fun p => if p = p0 then a_u else bond p
    have hh_meas : Measurable h_pol :=
      Measurable.ite (measurableSet_singleton p0) measurable_const hbond_meas
    have h_imp := (h_howard bond h_pol hbond_meas hh_meas {p0} (measurableSet_singleton p0)
      (fun p _ hp_eq => by
        rw [Set.mem_singleton_iff.mp hp_eq]
        dsimp [h_pol]
        rw [if_pos rfl]
        exact hL_gt)
      (fun p _ hp_ne => if_neg (Set.mem_singleton_iff.not.mp hp_ne))).2 p0 hp0 (Set.mem_singleton p0)
    have h_le_V : M.Jstat Pr h_pol p0 ≤ M.V Pr p0 := by
      rw [hV p0 hp0, ← hJinf p0 hp0]
      unfold JumpMarket.Jstat JumpMarket.Jinf
      exact le_iSup₂_of_le (fun _ => h_pol) (fun _ => hh_meas) le_rfl
    have h_lt_V := h_imp.trans_le h_le_V
    exact h_lt_V.ne (h_opt p0 hp0)
  · intro hEY p hp
    rw [hV p hp, ← hJinf p hp]
    refine h_no_imp bond hbond_meas (fun q hq a => ?_) p hp
    rw [L_Jstat_bond_eq M huncontrolled Pr hPr bond hbond a hq,
        Jstat_bond_eq M huncontrolled Pr hPr bond hbond q hq]
    have hsub : 0 ≤ M.T - q.1 := sub_nonneg.mpr hq.1.2
    let zq := q.2 * Real.exp (M.rho * (M.T - q.1))
    have hzq : 0 ≤ zq := mul_nonneg hq.2 (Real.exp_pos _).le
    have hwq : wBond M q = M.U zq := by
      unfold wBond
      rw [max_eq_right hq.2]
    have h_inner_le : ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - q.1),
        ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
          (∫⁻ y, ENNReal.ofReal (M.U (max 0 (zq * (1 + ∑ i, a.val s i * y i)))) ∂M.QY) ≤
        (∫⁻ s in Set.Ioo (0 : ℝ) (M.T - q.1), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) *
          ENNReal.ofReal (wBond M q) := by
      calc ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - q.1),
            ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) *
              (∫⁻ y, ENNReal.ofReal (M.U (max 0 (zq * (1 + ∑ i, a.val s i * y i)))) ∂M.QY)
          ≤ ∫⁻ s in Set.Ioo (0 : ℝ) (M.T - q.1),
            ENNReal.ofReal (M.lam * Real.exp (-M.lam * s)) * ENNReal.ofReal (wBond M q) := by
              refine lintegral_mono fun s => mul_le_mul_of_nonneg_left ?_ zero_le'
              rw [hwq]
              exact lintegral_U_le_of_EY_nonpos M hU1 hEY hzq (a.mem s)
        _ = (∫⁻ s in Set.Ioo (0 : ℝ) (M.T - q.1), ENNReal.ofReal (M.lam * Real.exp (-M.lam * s))) *
              ENNReal.ofReal (wBond M q) :=
              lintegral_mul_const (ENNReal.ofReal (wBond M q))
                (ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))))
    refine (add_le_add le_rfl h_inner_le).trans ?_
    rw [lintegral_lam_exp M.lam M.lam_pos (M.T - q.1) hsub]
    have h_exp_le : Real.exp (-M.lam * (M.T - q.1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [M.lam_pos])
    have h_w_nonneg : 0 ≤ wBond M q := by
      rw [hwq]
      exact M.U_nonneg zq hzq
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr h_exp_le),
        ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le h_w_nonneg)
          (mul_nonneg (sub_nonneg.mpr h_exp_le) h_w_nonneg)]
    apply ENNReal.ofReal_le_ofReal
    linarith
