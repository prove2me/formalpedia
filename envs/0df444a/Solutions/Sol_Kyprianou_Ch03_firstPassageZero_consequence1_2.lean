-- Prove2me | solution 2 for Kyprianou.Ch03.firstPassageZero_consequence1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T20:20:02.753815+00:00
-- url     : https://prove2.me/submissions/c102e211-085c-438c-a8d0-728f96443e18

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_exponentRegularity_infiniteLimitNonSubordinator

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03.FirstPassageZeroConsequence1Proof

/-! ### 1. Continuity and positivity of `L.ψ` above the maximal root `φ` -/

private lemma exp_sub_one_sub_le_half_sq {u : ℝ} (hu : u ≤ 0) :
    0 ≤ Real.exp u - 1 - u ∧ Real.exp u - 1 - u ≤ u ^ 2 / 2 := by
  have h0 : 0 ≤ Real.exp u - 1 - u := by
    have := Real.add_one_le_exp u
    linarith
  refine ⟨h0, ?_⟩
  let g : ℝ → ℝ := fun t => t ^ 2 / 2 - (Real.exp t - 1 - t)
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (t - (Real.exp t - 1)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have hpow := (hasDerivAt_pow 2 t).div_const 2
      have heq : (2 : ℝ) * t ^ (2 - 1) / 2 = t := by ring
      simpa [heq] using hpow
    have h2 : HasDerivAt (fun s : ℝ => Real.exp s - 1 - s) (Real.exp t - 1) t := by
      have ha : HasDerivAt (fun s : ℝ => Real.exp s - 1) (Real.exp t) t :=
        (Real.hasDerivAt_exp t).sub_const 1
      exact ha.sub (hasDerivAt_id t)
    exact h1.sub h2
  have hg_anti : AntitoneOn g (Iic 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic 0) ?_ ?_ ?_
    · exact fun t _ => (hg_deriv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg_deriv t).differentiableAt.differentiableWithinAt
    · intro t _
      rw [(hg_deriv t).deriv]
      have := Real.add_one_le_exp t
      linarith
  have hle : g 0 ≤ g u := hg_anti hu (Set.mem_Iic.mpr le_rfl) hu
  dsimp only [g] at hle
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.exp_zero, sub_self] at hle
  linarith

private lemma abs_jumpIntegrand_le {a y : ℝ} (ha : 0 ≤ a) (hy : y < 0) :
    |Real.exp (a * y) - 1 - a * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
      max 1 (a ^ 2 / 2) * min 1 (y ^ 2) := by
  have hay : a * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hy.le
  by_cases hy1 : -1 < y
  · have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, hy.trans zero_lt_one⟩
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hbound := exp_sub_one_sub_le_half_sq hay
    have hysq : y ^ 2 ≤ 1 := by nlinarith
    rw [abs_of_nonneg hbound.1, min_eq_right hysq]
    have hmul : (a * y) ^ 2 / 2 = (a ^ 2 / 2) * y ^ 2 := by ring
    rw [hmul] at hbound
    exact hbound.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg y))
  · have hnot : y ∉ Ioo (-1 : ℝ) 1 := fun h => hy1 h.1
    rw [Set.indicator_of_notMem hnot, mul_zero, sub_zero]
    have hysq : 1 ≤ y ^ 2 := by nlinarith
    rw [min_eq_left hysq, mul_one]
    have hexp_le : Real.exp (a * y) ≤ 1 := Real.exp_le_one_iff.mpr hay
    have hexp_pos : 0 < Real.exp (a * y) := Real.exp_pos _
    rw [abs_of_nonpos (sub_nonpos.mpr hexp_le)]
    exact (by linarith : -(Real.exp (a * y) - 1) ≤ 1).trans (le_max_left _ _)

private lemma continuousOn_laplaceExponent_Ici
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) :
    ContinuousOn L.ψ (Ici (0 : ℝ)) := by
  have hmin_int : Integrable (fun y : ℝ => min 1 (y ^ 2)) L.ν := by
    refine ⟨(by fun_prop : Measurable (fun y : ℝ => min 1 (y ^ 2))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (fun y : ℝ => ‖min 1 (y ^ 2)‖ₑ) = fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2)) := by
      ext y
      rw [Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg y))]
    simpa only [heq] using L.ν_integrable
  have hjump_cont_Icc : ∀ R : ℝ, 0 < R →
      ContinuousOn
        (fun θ : ℝ =>
          ∫ y in Iio (0 : ℝ),
            (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν)
        (Icc 0 R) := by
    intro R hR
    let bound : ℝ → ℝ := fun y => max 1 (R ^ 2 / 2) * min 1 (y ^ 2)
    refine continuousOn_of_dominated (bound := bound) ?_ ?_ ?_ ?_
    · intro θ _
      have hind : Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
        measurable_const.indicator measurableSet_Ioo
      have hm : Measurable (fun y : ℝ =>
          Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) :=
        ((Real.measurable_exp.comp (measurable_id.const_mul θ)).sub measurable_const).sub
          ((measurable_id.const_mul θ).mul hind)
      exact hm.aestronglyMeasurable
    · intro θ hθ
      filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      rw [Real.norm_eq_abs]
      have h1 := abs_jumpIntegrand_le hθ.1 hy
      have h2 : max 1 (θ ^ 2 / 2) ≤ max 1 (R ^ 2 / 2) := by
        refine max_le_max_left 1 ?_
        have hsq : θ ^ 2 ≤ R ^ 2 := by nlinarith [hθ.1, hθ.2]
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (le_min zero_le_one (sq_nonneg y)))
    · exact (hmin_int.const_mul (max 1 (R ^ 2 / 2))).integrableOn
    · filter_upwards [ae_restrict_mem measurableSet_Iio] with y _
      have hcont : Continuous (fun θ : ℝ =>
          Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
        fun_prop
      exact hcont.continuousOn
  have hjump_cont :
      ContinuousOn
        (fun θ : ℝ =>
          ∫ y in Iio (0 : ℝ),
            (Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) ∂L.ν)
        (Ici 0) := by
    intro θ hθ
    have hR : 0 < θ + 1 := by linarith [show (0 : ℝ) ≤ θ from hθ]
    have hc := hjump_cont_Icc (θ + 1) hR θ ⟨hθ, by linarith⟩
    have hnhds : Icc (0 : ℝ) (θ + 1) ∈ 𝓝[Ici (0 : ℝ)] θ := by
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨1, zero_lt_one, ?_⟩
      intro u hu
      have hdist : |u - θ| < 1 := by simpa [Real.dist_eq] using hu.1
      have hu_lt : u < θ + 1 := by linarith [(abs_lt.mp hdist).2]
      exact ⟨hu.2, hu_lt.le⟩
    exact hc.mono_of_mem_nhdsWithin hnhds
  have hpoly : ContinuousOn (fun θ : ℝ => L.c * θ + L.σ ^ 2 * θ ^ 2 / 2) (Ici 0) := by
    fun_prop
  exact hpoly.add hjump_cont

private lemma psi_pos_of_gt_maximalRoot
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P, Antitone (fun t : NNReal => L.X t omega)))
    (phi : ℝ)
    (hRoot : 0 ≤ phi ∧ L.ψ phi = 0 ∧ ∀ θ : ℝ, 0 ≤ θ → L.ψ θ = 0 → θ ≤ phi) :
    ∀ θ : ℝ, phi < θ → 0 < L.ψ θ := by
  have hTend : Tendsto L.ψ atTop atTop :=
    exponentRegularity_infiniteLimitNonSubordinator P F L hNotDecreasing
  have hCont : ContinuousOn L.ψ (Ici 0) := continuousOn_laplaceExponent_Ici L
  intro θ hθ
  have hθ0 : 0 ≤ θ := le_trans hRoot.1 hθ.le
  by_contra hle
  push Not at hle
  have hne : L.ψ θ ≠ 0 := fun h0 => not_le_of_gt hθ (hRoot.2.2 θ hθ0 h0)
  have hlt : L.ψ θ < 0 := lt_of_le_of_ne hle hne
  have hev : ∀ᶠ u in atTop, 0 < L.ψ u := hTend.eventually (eventually_gt_atTop 0)
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨M, hM⟩
  let θ₂ : ℝ := max (θ + 1) M
  have hθ_lt : θ < θ₂ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hψ2 : 0 < L.ψ θ₂ := hM θ₂ (le_max_right _ _)
  have hsub : Icc θ θ₂ ⊆ Ici 0 := fun u hu => hθ0.trans hu.1
  have hmem : (0 : ℝ) ∈ Icc (L.ψ θ) (L.ψ θ₂) := ⟨hlt.le, hψ2.le⟩
  rcases intermediate_value_Icc hθ_lt.le (hCont.mono hsub) hmem with ⟨u, hu, hu0⟩
  have hu_le : u ≤ phi := hRoot.2.2 u (hθ0.trans hu.1) hu0
  linarith [hu.1]

/-! ### 2. Pathwise rational characterization and no-overshoot for `firstHittingTime` -/

private noncomputable def untopReal (a : WithTop NNReal) : ℝ :=
  ((WithTop.untopD (0 : NNReal) a : NNReal) : ℝ)

private lemma untopReal_nonneg (a : WithTop NNReal) : 0 ≤ untopReal a :=
  NNReal.coe_nonneg _

private lemma untopReal_coe (t : NNReal) : untopReal (t : WithTop NNReal) = (t : ℝ) := rfl

private lemma measurable_untopReal : Measurable untopReal := by
  have huntop : Measurable (WithTop.untopD (0 : NNReal)) := by
    refine measurable_of_Iio fun r => ?_
    by_cases hr : (0 : NNReal) < r
    · have hpre : (WithTop.untopD (0 : NNReal)) ⁻¹' Iio r = Iio (r : WithTop NNReal) ∪ {⊤} := by
        ext a
        cases a with
        | top => simp [hr]
        | coe t =>
          simp only [mem_preimage, mem_Iio, mem_union, mem_singleton_iff, WithTop.coe_ne_top, or_false]
          change t < r ↔ (t : WithTop NNReal) < (r : WithTop NNReal)
          exact WithTop.coe_lt_coe.symm
      rw [hpre]
      exact measurableSet_Iio.union (measurableSet_singleton ⊤)
    · have hr0 : r = 0 := le_antisymm (not_lt.mp hr) bot_le
      subst hr0
      have hpre : (WithTop.untopD (0 : NNReal)) ⁻¹' Iio (0 : NNReal) = ∅ := by
        ext a
        cases a <;> simp
      rw [hpre]
      exact MeasurableSet.empty
  exact NNReal.continuous_coe.measurable.comp huntop

private noncomputable def hitRat {Omega : Type} (X : NNReal → Omega → ℝ) (x : ℝ) (t : NNReal) :
    Set Omega :=
  {ω | ∃ q : ℚ, 0 < q ∧ Real.toNNReal (q : ℝ) < t ∧ x < X (Real.toNNReal (q : ℝ)) ω}

private lemma hitRat_eq_lt_firstHittingTime
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (x : ℝ) (t : NNReal) :
    hitRat L.X x t = {ω | firstHittingTime L.X (Set.Ioi x) ω < (t : WithTop NNReal)} := by
  ext ω
  simp only [hitRat, mem_ofPred_eq, firstHittingTime, sInf_lt_iff, mem_image,
    exists_exists_and_eq_and]
  constructor
  · rintro ⟨q, hq_pos, hq_lt, hX⟩
    have hq_nn : ((Real.toNNReal (q : ℝ)) : ℝ) = (q : ℝ) :=
      Real.coe_toNNReal (q : ℝ) (Rat.cast_nonneg.mpr hq_pos.le)
    have hq_pos' : (0 : NNReal) < Real.toNNReal (q : ℝ) := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_zero, hq_nn]
      exact Rat.cast_pos.mpr hq_pos
    exact ⟨Real.toNNReal (q : ℝ), ⟨hq_pos', hX⟩, WithTop.coe_lt_coe.mpr hq_lt⟩
  · rintro ⟨s, ⟨hs_pos, hXs⟩, hs_lt⟩
    have hs_lt' : s < t := WithTop.coe_lt_coe.mp hs_lt
    have hXs' : x < L.X s ω := hXs
    have hcont := L.rightCont ω s
    rw [Metric.continuousWithinAt_iff] at hcont
    rcases hcont (L.X s ω - x) (sub_pos.mpr hXs') with ⟨δ, hδ_pos, hδ⟩
    let hi : ℝ := min (t : ℝ) ((s : ℝ) + δ)
    have hs_hi : (s : ℝ) < hi := lt_min (NNReal.coe_lt_coe.mpr hs_lt') (by linarith)
    rcases exists_rat_btwn hs_hi with ⟨q, hsq, hqhi⟩
    have hq_pos : (0 : ℚ) < q := by
      have h0q : (0 : ℝ) < (q : ℝ) := lt_trans (NNReal.coe_pos.mpr hs_pos) hsq
      exact Rat.cast_pos.mp h0q
    have hq_nn : ((Real.toNNReal (q : ℝ)) : ℝ) = (q : ℝ) :=
      Real.coe_toNNReal (q : ℝ) (Rat.cast_nonneg.mpr hq_pos.le)
    have hq_lt_t : Real.toNNReal (q : ℝ) < t := by
      rw [← NNReal.coe_lt_coe, hq_nn]
      exact lt_of_lt_of_le hqhi (min_le_left _ _)
    have hs_le_q : s ≤ Real.toNNReal (q : ℝ) := by
      rw [← NNReal.coe_le_coe, hq_nn]
      exact hsq.le
    have hdist : dist (Real.toNNReal (q : ℝ)) s < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (by rw [hq_nn]; exact hsq.le)), hq_nn]
      linarith [lt_of_lt_of_le hqhi (min_le_right _ _)]
    have hXdist := hδ hs_le_q hdist
    rw [Real.dist_eq] at hXdist
    have hXq : x < L.X (Real.toNNReal (q : ℝ)) ω := by
      linarith [(abs_lt.mp hXdist).1]
    exact ⟨q, hq_pos, hq_lt_t, hXq⟩

private lemma measurableSet_lt_firstHittingTime
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (x : ℝ) (t : NNReal) :
    MeasurableSet[F t] {ω | firstHittingTime L.X (Set.Ioi x) ω < (t : WithTop NNReal)} := by
  rw [← hitRat_eq_lt_firstHittingTime L x t]
  have heq : hitRat L.X x t =
      ⋃ q : {q : ℚ // 0 < q ∧ Real.toNNReal (q : ℝ) < t},
        {ω | x < L.X (Real.toNNReal (q.1 : ℝ)) ω} := by
    ext ω
    simp [hitRat, and_assoc]
  rw [heq]
  refine MeasurableSet.iUnion fun q => ?_
  have hmeas : Measurable[F (Real.toNNReal (q.1 : ℝ))] (L.X (Real.toNNReal (q.1 : ℝ))) :=
    L.adapted (Real.toNNReal (q.1 : ℝ))
  exact F.mono q.2.2.le _ (hmeas measurableSet_Ioi)

private lemma measurable_firstHittingTime
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (x : ℝ) :
    Measurable (firstHittingTime L.X (Set.Ioi x)) := by
  refine measurable_of_Iio fun a => ?_
  cases a with
  | top =>
    have heq : firstHittingTime L.X (Set.Ioi x) ⁻¹' Iio (⊤ : WithTop NNReal) =
        ⋃ n : ℕ, {ω | firstHittingTime L.X (Set.Ioi x) ω < ((n : NNReal) : WithTop NNReal)} := by
      ext ω
      simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        cases hτ : firstHittingTime L.X (Set.Ioi x) ω with
        | top => simp [hτ] at h
        | coe t =>
          rcases exists_nat_gt (t : ℝ) with ⟨n, hn⟩
          refine ⟨n, ?_⟩
          exact WithTop.coe_lt_coe.mpr (by exact_mod_cast hn)
      · rintro ⟨n, hn⟩
        exact lt_trans hn (WithTop.coe_lt_top _)
    rw [heq]
    exact MeasurableSet.iUnion fun n => F.le n _ (measurableSet_lt_firstHittingTime L x n)
  | coe t =>
    exact F.le t _ (measurableSet_lt_firstHittingTime L x t)

private lemma X_le_of_le_firstHittingTime
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {x : ℝ} (hx : 0 ≤ x)
    (t : NNReal) (ω : Omega)
    (hle : (t : WithTop NNReal) ≤ firstHittingTime L.X (Set.Ioi x) ω) :
    L.X t ω ≤ x := by
  by_cases ht0 : t = 0
  · subst ht0
    rw [L.X_zero ω]
    exact hx
  · have ht_pos : 0 < t := pos_iff_ne_zero.mpr ht0
    rcases L.leftLim ω t ht_pos with ⟨l, hl⟩
    -- Build an explicit sequence s_k ↑ t strictly from below so no NeBot instance is needed
    let seq : ℕ → NNReal := fun k => t * ((k + 1 : NNReal) / (k + 2 : NNReal))
    have hseq_pos : ∀ k : ℕ, 0 < seq k := fun k =>
      mul_pos ht_pos (div_pos (by positivity) (by positivity))
    have hseq_lt : ∀ k : ℕ, seq k < t := fun k => by
      dsimp only [seq]
      have hlt1 : ((k + 1 : NNReal) / (k + 2 : NNReal)) < 1 := by
        rw [div_lt_one (by positivity)]
        exact_mod_cast Nat.lt_succ_self (k + 1)
      simpa using mul_lt_mul_of_pos_left hlt1 ht_pos
    have hseq_tend : Tendsto seq atTop (𝓝[<] t) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hseq_lt⟩
      have hdiv : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) atTop (𝓝 1) := by
        have hrew : (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
            fun k : ℕ => 1 - 1 / ((k : ℝ) + 2) := by
          ext k
          have hne : (k : ℝ) + 2 ≠ 0 := by positivity
          field_simp [hne]
          ring
        rw [hrew]
        have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
          refine h1.congr fun k => ?_
          change (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) = (1 : ℝ) / ((k : ℝ) + 2)
          push_cast
          ring
        simpa using tendsto_const_nhds.sub h0
      have hcoe : Tendsto (fun k => (seq k : ℝ)) atTop (𝓝 (t : ℝ)) := by
        have hmul := hdiv.const_mul (t : ℝ)
        simpa [seq, mul_one] using hmul
      exact NNReal.tendsto_coe.mp hcoe
    have hl_le : l ≤ x := by
      refine le_of_tendsto (hl.comp hseq_tend) (Eventually.of_forall fun k => ?_)
      by_contra hgt
      push Not at hgt
      have hτ_le : firstHittingTime L.X (Set.Ioi x) ω ≤ (seq k : WithTop NNReal) :=
        csInf_le (OrderBot.bddBelow _) ⟨seq k, ⟨hseq_pos k, hgt⟩, rfl⟩
      have hts : (t : WithTop NNReal) ≤ (seq k : WithTop NNReal) := hle.trans hτ_le
      exact not_lt_of_ge (WithTop.coe_le_coe.mp hts) (hseq_lt k)
    exact (L.noPosJumps ω t l ht_pos hl).trans hl_le

private lemma X_eq_of_firstHittingTime_eq
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {x : ℝ} (hx : 0 ≤ x)
    (t₀ : NNReal) (ω : Omega)
    (heq : firstHittingTime L.X (Set.Ioi x) ω = (t₀ : WithTop NNReal)) :
    L.X t₀ ω = x := by
  have hle : L.X t₀ ω ≤ x := X_le_of_le_firstHittingTime L hx t₀ ω heq.ge
  have hge : x ≤ L.X t₀ ω := by
    by_contra hlt
    push Not at hlt
    have hcont := L.rightCont ω t₀
    rw [Metric.continuousWithinAt_iff] at hcont
    rcases hcont (x - L.X t₀ ω) (sub_pos.mpr hlt) with ⟨δ, hδ_pos, hδ⟩
    let t₁ : NNReal := t₀ + ⟨δ / 2, by positivity⟩
    have ht₀_lt : (t₀ : WithTop NNReal) < (t₁ : WithTop NNReal) := by
      refine WithTop.coe_lt_coe.mpr ?_
      change (t₀ : ℝ) < (t₀ : ℝ) + δ / 2
      linarith
    have hτ_lt : firstHittingTime L.X (Set.Ioi x) ω < (t₁ : WithTop NNReal) := heq ▸ ht₀_lt
    simp only [firstHittingTime, sInf_lt_iff, mem_image, exists_exists_and_eq_and] at hτ_lt
    rcases hτ_lt with ⟨s, ⟨hs_pos, hXs⟩, hs_lt⟩
    have hXs' : x < L.X s ω := hXs
    have hs_lt' : s < t₁ := WithTop.coe_lt_coe.mp hs_lt
    have ht₀_le_s : t₀ ≤ s := by
      have hτ_le : firstHittingTime L.X (Set.Ioi x) ω ≤ (s : WithTop NNReal) :=
        csInf_le (OrderBot.bddBelow _) ⟨s, ⟨hs_pos, hXs⟩, rfl⟩
      exact WithTop.coe_le_coe.mp (heq ▸ hτ_le)
    have hdist : dist s t₀ < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht₀_le_s))]
      have : (s : ℝ) < (t₀ : ℝ) + δ / 2 := NNReal.coe_lt_coe.mpr hs_lt'
      linarith
    have hXdist := hδ ht₀_le_s hdist
    rw [Real.dist_eq] at hXdist
    linarith [(abs_lt.mp hXdist).2, hXs']
  exact le_antisymm hle hge

/-! ### 3. Exponential martingale identity on `F s`-measurable sets -/

private noncomputable def expMart
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (θ : ℝ) (t : NNReal) (ω : Omega) : ℝ :=
  Real.exp (θ * L.X t ω - (t : ℝ) * L.ψ θ)

private lemma expMart_nonneg
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (θ : ℝ) (t : NNReal) (ω : Omega) :
    0 ≤ expMart L θ t ω :=
  (Real.exp_pos _).le

private lemma expMart_integrable
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {θ : ℝ} (hθ : 0 ≤ θ) (t : NNReal) :
    Integrable (expMart L θ t) P := by
  have heq : expMart L θ t = fun ω => Real.exp (-(t : ℝ) * L.ψ θ) * Real.exp (θ * L.X t ω) := by
    ext ω
    dsimp only [expMart]
    rw [← Real.exp_add]
    congr 1; ring
  rw [heq]
  exact (L.laplace t θ hθ).1.const_mul _

private lemma integral_expMart_eq_one
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {θ : ℝ} (hθ : 0 ≤ θ) (t : NNReal) :
    ∫ ω, expMart L θ t ω ∂P = 1 := by
  have heq : expMart L θ t = fun ω => Real.exp (-(t : ℝ) * L.ψ θ) * Real.exp (θ * L.X t ω) := by
    ext ω
    dsimp only [expMart]
    rw [← Real.exp_add]
    congr 1; ring
  rw [heq, integral_const_mul, (L.laplace t θ hθ).2, ← Real.exp_add]
  change Real.exp (-(t : ℝ) * L.ψ θ + (t : ℝ) * L.ψ θ) = 1
  simp

private lemma setIntegral_expMart_eq
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) {θ : ℝ} (hθ : 0 ≤ θ)
    {s t : NNReal} (hst : s ≤ t) {B : Set Omega} (hB : MeasurableSet[F s] B) :
    ∫ ω in B, expMart L θ t ω ∂P = ∫ ω in B, expMart L θ s ω ∂P := by
  have hBm : MeasurableSet B := F.le s B hB
  have hX_meas : ∀ u : NNReal, Measurable (L.X u) :=
    fun u => (L.adapted u).mono (F.le u) le_rfl
  let Z : NNReal → Omega → ℝ≥0∞ := fun u ω => ENNReal.ofReal (expMart L θ u ω)
  let W : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (θ * y - ((t - s : NNReal) : ℝ) * L.ψ θ))
  have hZ_measF : Measurable[F s] (Z s) := by
    have hXs : Measurable[F s] (L.X s) := L.adapted s
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((hXs.const_mul θ).sub measurable_const))
  have hW_meas : Measurable W := by fun_prop
  have hfac : ∀ ω,
      B.indicator (Z t) ω =
        W (L.X t ω - L.X s ω) * B.indicator (Z s) ω := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      dsimp only [Z, W, expMart]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      rw [NNReal.coe_sub hst]
      ring
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  have hinc_meas : Measurable (fun ω => L.X t ω - L.X s ω) := (hX_meas t).sub (hX_meas s)
  have hf_meas : Measurable[MeasurableSpace.comap (fun ω => L.X t ω - L.X s ω) inferInstance]
      (fun ω => W (L.X t ω - L.X s ω)) :=
    hW_meas.comp (Measurable.of_comap_le le_rfl)
  have hg_meas : Measurable[F s] (B.indicator (Z s)) := hZ_measF.indicator hB
  have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.mp hinc_meas) (F.le s) (L.indepIncrements s t hst) hf_meas hg_meas
  have hW_int : ∫⁻ ω, W (L.X t ω - L.X s ω) ∂P = 1 := by
    have hident := (L.stationaryIncrements s t hst).comp hW_meas
    change ∫⁻ ω, (W ∘ fun ω => L.X t ω - L.X s ω) ω ∂P = 1
    rw [hident.lintegral_eq]
    have h1 := integral_expMart_eq_one L hθ (t - s)
    change ∫⁻ ω, ENNReal.ofReal (expMart L θ (t - s) ω) ∂P = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (expMart_integrable L hθ (t - s))
      (ae_of_all _ (expMart_nonneg L θ (t - s))), h1, ENNReal.ofReal_one]
  have hlin : ∫⁻ ω in B, Z t ω ∂P = ∫⁻ ω in B, Z s ω ∂P := by
    rw [← lintegral_indicator hBm, ← lintegral_indicator hBm]
    simp_rw [hfac]
    rw [hmul, hW_int, one_mul]
  have hIt : IntegrableOn (expMart L θ t) B P := (expMart_integrable L hθ t).integrableOn
  have hIs : IntegrableOn (expMart L θ s) B P := (expMart_integrable L hθ s).integrableOn
  have ht_eq := ofReal_integral_eq_lintegral_ofReal hIt (ae_of_all _ (expMart_nonneg L θ t))
  have hs_eq := ofReal_integral_eq_lintegral_ofReal hIs (ae_of_all _ (expMart_nonneg L θ s))
  have hof : ENNReal.ofReal (∫ ω in B, expMart L θ t ω ∂P) =
      ENNReal.ofReal (∫ ω in B, expMart L θ s ω ∂P) := by
    rw [ht_eq, hs_eq]
    exact hlin
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (expMart_nonneg L θ t))
    (integral_nonneg (expMart_nonneg L θ s))).mp hof

/-! ### 4. Single-`L^1` uniform integrability helper (8-line proof via truncation) -/

private lemma exists_delta_setIntegral_lt
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} [IsFiniteMeasure P] {f : Omega → ℝ}
    (hf : Integrable f P) (hf_nonneg : ∀ ω, 0 ≤ f ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set Omega, MeasurableSet s → (P s).toReal < δ →
      ∫ ω in s, f ω ∂P < ε := by
  have htend : Tendsto (fun K : ℕ => ∫ ω, (f ω - min (f ω) (K : ℝ)) ∂P) atTop (𝓝 0) := by
    have h0 : ∫ ω, (0 : ℝ) ∂P = 0 := integral_zero _ _
    rw [← h0]
    refine tendsto_integral_of_dominated_convergence f ?_ hf ?_ ?_
    · intro K
      exact (hf.aestronglyMeasurable.sub
        (hf.aestronglyMeasurable.inf aestronglyMeasurable_const))
    · intro K
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
      have hmin_nn : 0 ≤ min (f ω) (K : ℝ) := le_min (hf_nonneg ω) (Nat.cast_nonneg K)
      linarith
    · filter_upwards with ω
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (f ω)) ?_
      intro K hK
      have hle : f ω ≤ (K : ℝ) := (Nat.le_ceil (f ω)).trans (Nat.cast_le.mpr hK)
      rw [min_eq_left hle, sub_self]
  rw [Metric.tendsto_atTop] at htend
  rcases htend (ε / 2) (half_pos hε) with ⟨K, hK⟩
  have hK' := hK (max K 1) (le_max_left _ _)
  let K1 : ℕ := max K 1
  have hK1_pos : (0 : ℝ) < (K1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1))
  have htail : ∫ ω, (f ω - min (f ω) (K1 : ℝ)) ∂P < ε / 2 := by
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun ω => sub_nonneg.mpr (min_le_left _ _))] at hK'
    exact hK'
  refine ⟨ε / (2 * (K1 : ℝ)), by positivity, fun s _ hPs => ?_⟩
  have hmin_int : Integrable (fun ω => min (f ω) (K1 : ℝ)) P := by
    refine hf.mono' (hf.aestronglyMeasurable.inf aestronglyMeasurable_const) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf_nonneg ω) (Nat.cast_nonneg K1))]
    exact min_le_left _ _
  have hsub_int : Integrable (fun ω => f ω - min (f ω) (K1 : ℝ)) P := hf.sub hmin_int
  have hsplit : ∫ ω in s, f ω ∂P =
      (∫ ω in s, (f ω - min (f ω) (K1 : ℝ)) ∂P) + ∫ ω in s, min (f ω) (K1 : ℝ) ∂P := by
    rw [← integral_add hsub_int.integrableOn hmin_int.integrableOn]
    congr 1; ext ω; ring
  have h1 : ∫ ω in s, (f ω - min (f ω) (K1 : ℝ)) ∂P ≤ ∫ ω, (f ω - min (f ω) (K1 : ℝ)) ∂P :=
    setIntegral_le_integral hsub_int (ae_of_all _ fun ω => sub_nonneg.mpr (min_le_left _ _))
  have h2 : ∫ ω in s, min (f ω) (K1 : ℝ) ∂P ≤ (K1 : ℝ) * (P s).toReal := by
    have hle : ∫ ω in s, min (f ω) (K1 : ℝ) ∂P ≤ ∫ ω in s, (K1 : ℝ) ∂P := by
      refine integral_mono_of_nonneg (ae_of_all _ fun ω => le_min (hf_nonneg ω) (Nat.cast_nonneg K1))
        (integrableOn_const (measure_ne_top P s)) (ae_of_all _ fun ω => min_le_right _ _)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at hle
    exact hle
  have h3 : (K1 : ℝ) * (P s).toReal < ε / 2 := by
    have := mul_lt_mul_of_pos_left hPs hK1_pos
    have hmul : (K1 : ℝ) * (ε / (2 * (K1 : ℝ))) = ε / 2 := by field_simp
    linarith
  linarith

private lemma integral_sub_min_le_tail
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {G : Set Omega} (hG : MeasurableSet G)
    {f : Omega → ℝ} (hf_int : Integrable f P) (hf_meas : Measurable f)
    (hf_nn : ∀ ω, 0 ≤ f ω) {R : ℝ} (hR_nn : 0 ≤ R) :
    0 ≤ (∫ ω in G, f ω ∂P) - (∫ ω in G, min (f ω) R ∂P) ∧
    (∫ ω in G, f ω ∂P) - (∫ ω in G, min (f ω) R ∂P) ≤
      ∫ ω in G ∩ {ω | R < f ω}, f ω ∂P := by
  have hmin_int : IntegrableOn (fun ω => min (f ω) R) G P :=
    (hf_int.mono' (hf_int.aestronglyMeasurable.inf aestronglyMeasurable_const)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        change |min (f ω) R| ≤ f ω
        rw [abs_of_nonneg (le_min (hf_nn ω) hR_nn)]
        exact min_le_left _ _)).integrableOn
  rw [← integral_sub hf_int.integrableOn hmin_int]
  refine ⟨integral_nonneg fun ω => sub_nonneg.mpr (min_le_left _ _), ?_⟩
  have hs_meas : MeasurableSet (G ∩ {ω | R < f ω}) := hG.inter (hf_meas measurableSet_Ioi)
  rw [← integral_indicator hG, ← integral_indicator hs_meas]
  refine integral_mono_of_nonneg
    (ae_of_all _ fun ω => Set.indicator_nonneg (fun ω' _ => sub_nonneg.mpr (min_le_left _ _)) ω)
    (hf_int.indicator hs_meas) (ae_of_all _ fun ω => ?_)
  by_cases hGω : ω ∈ G
  · rw [Set.indicator_of_mem hGω]
    by_cases hRω : R < f ω
    · have hmem : ω ∈ G ∩ {ω | R < f ω} := ⟨hGω, hRω⟩
      rw [Set.indicator_of_mem hmem]
      have : 0 ≤ min (f ω) R := le_min (hf_nn ω) hR_nn
      linarith
    · rw [Set.indicator_of_notMem (fun h => hRω h.2), min_eq_left (not_lt.mp hRω), sub_self]
  · rw [Set.indicator_of_notMem hGω, Set.indicator_of_notMem (fun h => hGω h.1)]

/-! ### 5. Stopped martingale identity at `τ_x^+` for `θ > φ` and finite horizon `n` -/

private lemma stopped_expMart_horizon_eq
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    {x : ℝ} (hx : 0 ≤ x)
    {θ : ℝ} (hθ : 0 ≤ θ) (hψ_pos : 0 < L.ψ θ)
    (n : ℕ) :
    let τ := firstHittingTime L.X (Set.Ioi x)
    let Gn : Set Omega := {ω | τ ω < ((n : NNReal) : WithTop NNReal)}
    ∫ ω in Gn, expMart L θ n ω ∂P =
      ∫ ω in Gn, Real.exp (θ * x - untopReal (τ ω) * L.ψ θ) ∂P := by
  intro τ Gn
  have hGn_meas : MeasurableSet Gn := F.le n _ (measurableSet_lt_firstHittingTime L x n)
  let Z : Omega → ℝ := fun ω => Real.exp (θ * x - untopReal (τ ω) * L.ψ θ)
  have hZ_meas : Measurable Z :=
    Real.measurable_exp.comp
      (measurable_const.sub ((measurable_untopReal.comp (measurable_firstHittingTime L x)).mul_const (L.ψ θ)))
  have hZ_le : ∀ ω, Z ω ≤ Real.exp (θ * x) := by
    intro ω
    dsimp only [Z]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ untopReal (τ ω) * L.ψ θ := mul_nonneg (untopReal_nonneg _) hψ_pos.le
    linarith
  have hZ_nn : ∀ ω, 0 ≤ Z ω := fun _ => (Real.exp_pos _).le
  -- Dyadic grid approximations
  let d : ℕ → ℕ → NNReal := fun m k => (k : NNReal) / ((2 : NNReal) ^ m)
  let N : ℕ → ℕ := fun m => n * 2 ^ m
  have hd_mono : ∀ m {j k : ℕ}, j ≤ k → d m j ≤ d m k := fun m _ _ hjk =>
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hjk) bot_le
  have hd_N : ∀ m, d m (N m) = (n : NNReal) := by
    intro m
    dsimp only [d, N]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact mul_div_cancel_right₀ (n : NNReal) (pow_ne_zero m (by norm_num : (2 : NNReal) ≠ 0))
  have hd_le_n : ∀ m k, k ≤ N m → d m k ≤ (n : NNReal) := fun m k hk => by
    rw [← hd_N m]; exact hd_mono m hk
  let A : ℕ → ℕ → Set Omega := fun m k =>
    {ω | τ ω < (d m k : WithTop NNReal)} \ {ω | τ ω < (d m (k - 1) : WithTop NNReal)}
  have hA_measF : ∀ m k, MeasurableSet[F (d m k)] (A m k) := by
    intro m k
    have h1 := measurableSet_lt_firstHittingTime L x (d m k)
    have h2 := F.mono (hd_mono m (Nat.sub_le k 1)) _ (measurableSet_lt_firstHittingTime L x (d m (k - 1)))
    exact h1.diff h2
  have hA_meas : ∀ m k, MeasurableSet (A m k) := fun m k => F.le (d m k) _ (hA_measF m k)
  have hA_disj : ∀ m, PairwiseDisjoint (Finset.Icc 1 (N m) : Set ℕ) (A m) := by
    intro m i hi j hj hij
    rw [Function.onFun, Set.disjoint_left]
    intro ω hωi hωj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi_le : i ≤ j - 1 := Nat.le_sub_one_of_lt hlt
      exact hωj.2 (lt_of_lt_of_le hωi.1 (WithTop.coe_le_coe.mpr (hd_mono m hi_le)))
    · have hj_le : j ≤ i - 1 := Nat.le_sub_one_of_lt hgt
      exact hωi.2 (lt_of_lt_of_le hωj.1 (WithTop.coe_le_coe.mpr (hd_mono m hj_le)))
  have hA_union : ∀ m, (⋃ k ∈ Finset.Icc 1 (N m), A m k) = Gn := by
    intro m
    ext ω
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
    constructor
    · rintro ⟨k, ⟨_, hkN⟩, hω⟩
      exact lt_of_lt_of_le hω.1 (WithTop.coe_le_coe.mpr (hd_le_n m k hkN))
    · intro hω
      have hω' : τ ω < ((n : NNReal) : WithTop NNReal) := hω
      have hex : ∃ k : ℕ, τ ω < (d m k : WithTop NNReal) := ⟨N m, by rwa [hd_N m]⟩
      let k₀ := Nat.find hex
      have hk₀_spec : τ ω < (d m k₀ : WithTop NNReal) := Nat.find_spec hex
      have hk₀_pos : 1 ≤ k₀ := by
        by_contra h0
        have hk0 : k₀ = 0 := by omega
        rw [hk0] at hk₀_spec
        have hd0 : d m 0 = 0 := by simp [d]
        rw [hd0] at hk₀_spec
        exact not_lt_of_ge (bot_le : (0 : WithTop NNReal) ≤ τ ω) hk₀_spec
      have hk₀_le : k₀ ≤ N m := Nat.find_min' hex (by rwa [hd_N m])
      have hk₀_prev : ¬ τ ω < (d m (k₀ - 1) : WithTop NNReal) :=
        Nat.find_min hex (Nat.sub_lt hk₀_pos Nat.zero_lt_one)
      exact ⟨k₀, ⟨hk₀_pos, hk₀_le⟩, hk₀_spec, hk₀_prev⟩
  let Y : ℕ → Omega → ℝ := fun m ω =>
    ∑ k ∈ Finset.Icc 1 (N m), (A m k).indicator (expMart L θ (d m k)) ω
  have hY_nn : ∀ m ω, 0 ≤ Y m ω := fun m ω =>
    Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => expMart_nonneg L θ _ _) _
  have hY_meas : ∀ m, Measurable (Y m) := fun m => by
    refine Finset.measurable_sum _ fun k _ => ?_
    have hM : Measurable (expMart L θ (d m k)) :=
      Real.measurable_exp.comp
        ((((L.adapted (d m k)).mono (F.le _) le_rfl).const_mul θ).sub measurable_const)
    exact hM.indicator (hA_meas m k)
  have hY_eq_on : ∀ m k, k ∈ Finset.Icc 1 (N m) → ∀ ω ∈ A m k, Y m ω = expMart L θ (d m k) ω := by
    intro m k hk ω hω
    dsimp only [Y]
    rw [Finset.sum_eq_single k]
    · exact Set.indicator_of_mem hω _
    · intro j hj hjk
      have hnot : ω ∉ A m j := Set.disjoint_left.mp (hA_disj m hk hj hjk.symm) hω
      exact Set.indicator_of_notMem hnot _
    · intro hnot; exact absurd hk hnot
  have hY_int : ∀ m, Integrable (Y m) P := fun m =>
    integrable_finsetSum _ fun k _ => (expMart_integrable L hθ (d m k)).indicator (hA_meas m k)
  have hY_sum_int : ∀ m, ∫ ω in Gn, Y m ω ∂P = ∫ ω in Gn, expMart L θ n ω ∂P := by
    intro m
    rw [← hA_union m]
    rw [integral_biUnion_finset (Finset.Icc 1 (N m)) (fun k _ => hA_meas m k) (hA_disj m)
      (fun k _ => (hY_int m).integrableOn)]
    rw [integral_biUnion_finset (Finset.Icc 1 (N m)) (fun k _ => hA_meas m k) (hA_disj m)
      (fun k _ => (expMart_integrable L hθ n).integrableOn)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hcongr : ∫ ω in A m k, Y m ω ∂P = ∫ ω in A m k, expMart L θ (d m k) ω ∂P :=
      setIntegral_congr_fun (hA_meas m k) (hY_eq_on m k hk)
    rw [hcongr]
    exact (setIntegral_expMart_eq L hθ (hd_le_n m k (Finset.mem_Icc.mp hk).2) (hA_measF m k)).symm
  have hY_tail_eq : ∀ m (R : ℝ),
      ∫ ω in Gn ∩ {ω | R < Y m ω}, Y m ω ∂P =
        ∫ ω in Gn ∩ {ω | R < Y m ω}, expMart L θ n ω ∂P := by
    intro m R
    let B : ℕ → Set Omega := fun k => A m k ∩ {ω | R < expMart L θ (d m k) ω}
    have hB_measF : ∀ k, MeasurableSet[F (d m k)] (B k) := by
      intro k
      have hM : Measurable[F (d m k)] (expMart L θ (d m k)) :=
        Real.measurable_exp.comp
          (((L.adapted (d m k)).const_mul θ).sub measurable_const)
      exact (hA_measF m k).inter (hM measurableSet_Ioi)
    have hB_meas : ∀ k, MeasurableSet (B k) := fun k => F.le (d m k) _ (hB_measF k)
    have hB_disj : PairwiseDisjoint (Finset.Icc 1 (N m) : Set ℕ) B := by
      intro i hi j hj hij
      exact (hA_disj m hi hj hij).mono inter_subset_left inter_subset_left
    have hB_union : (⋃ k ∈ Finset.Icc 1 (N m), B k) = Gn ∩ {ω | R < Y m ω} := by
      ext ω
      simp only [mem_iUnion, Finset.mem_Icc, exists_prop, mem_inter_iff, mem_ofPred_eq, B]
      constructor
      · rintro ⟨k, hk, hωA, hωR⟩
        have hGnω : ω ∈ Gn := by
          rw [← hA_union m]
          exact mem_biUnion (Finset.mem_Icc.mpr hk) hωA
        rw [← hY_eq_on m k (Finset.mem_Icc.mpr hk) ω hωA] at hωR
        exact ⟨hGnω, hωR⟩
      · rintro ⟨hGnω, hωR⟩
        rw [← hA_union m] at hGnω
        rcases mem_iUnion₂.mp hGnω with ⟨k, hk, hωA⟩
        rw [hY_eq_on m k hk ω hωA] at hωR
        exact ⟨k, Finset.mem_Icc.mp hk, hωA, hωR⟩
    rw [← hB_union]
    rw [integral_biUnion_finset (Finset.Icc 1 (N m)) (fun k _ => hB_meas k) hB_disj
      (fun k _ => (hY_int m).integrableOn)]
    rw [integral_biUnion_finset (Finset.Icc 1 (N m)) (fun k _ => hB_meas k) hB_disj
      (fun k _ => (expMart_integrable L hθ n).integrableOn)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hcongr : ∫ ω in B k, Y m ω ∂P = ∫ ω in B k, expMart L θ (d m k) ω ∂P :=
      setIntegral_congr_fun (hB_meas k) fun ω hω => hY_eq_on m k hk ω hω.1
    rw [hcongr]
    exact (setIntegral_expMart_eq L hθ (hd_le_n m k (Finset.mem_Icc.mp hk).2) (hB_measF k)).symm
  -- Pointwise convergence Y m ω → Z ω on Gn
  have hY_tendsto : ∀ ω ∈ Gn, Tendsto (fun m => Y m ω) atTop (𝓝 (Z ω)) := by
    intro ω hω
    cases hτ : τ ω with
    | top =>
      have hω' : τ ω < ((n : NNReal) : WithTop NNReal) := hω
      rw [hτ] at hω'
      exact absurd hω' (not_lt_of_ge le_top)
    | coe t₀ =>
      have hXt₀ : L.X t₀ ω = x := X_eq_of_firstHittingTime_eq L hx t₀ ω hτ
      have hZω : Z ω = expMart L θ t₀ ω := by
        dsimp only [Z, expMart]
        rw [hτ, untopReal_coe, hXt₀]
      rw [hZω]
      have hkm : ∀ m, ∃ k, k ∈ Finset.Icc 1 (N m) ∧ ω ∈ A m k := by
        intro m
        have hω' : ω ∈ ⋃ k ∈ Finset.Icc 1 (N m), A m k := by rwa [hA_union m]
        rcases mem_iUnion₂.mp hω' with ⟨k, hk, hAk⟩
        exact ⟨k, hk, hAk⟩
      choose km hkm_mem hkm_A using hkm
      have hY_eq : ∀ m, Y m ω = expMart L θ (d m (km m)) ω :=
        fun m => hY_eq_on m (km m) (hkm_mem m) ω (hkm_A m)
      simp_rw [hY_eq]
      have hd_ge : ∀ m, t₀ ≤ d m (km m) := fun m => by
        have hlt : τ ω < (d m (km m) : WithTop NNReal) := (hkm_A m).1
        rw [hτ] at hlt
        exact (WithTop.coe_lt_coe.mp hlt).le
      have hd_tend : Tendsto (fun m => d m (km m)) atTop (𝓝[Ici t₀] t₀) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall hd_ge⟩
        rw [Metric.tendsto_atTop]
        intro ε hε
        have h2 : Tendsto (fun m : ℕ => (1 : ℝ) / ((2 : ℝ) ^ m)) atTop (𝓝 0) := by
          simpa [one_div] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 : ℝ) / 2 < 1)
        rcases (Metric.tendsto_atTop.mp h2) ε hε with ⟨M, hM⟩
        refine ⟨M, fun m hm => ?_⟩
        rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hd_ge m)))]
        have hprev : d m (km m - 1) ≤ t₀ := by
          have hnot : ¬ τ ω < (d m (km m - 1) : WithTop NNReal) := (hkm_A m).2
          rw [hτ] at hnot
          exact WithTop.coe_le_coe.mp (not_lt.mp hnot)
        have hdiff : (d m (km m) : ℝ) - (d m (km m - 1) : ℝ) = (1 : ℝ) / (2 : ℝ) ^ m := by
          have hk1 : 1 ≤ km m := (Finset.mem_Icc.mp (hkm_mem m)).1
          have hk1' : ((km m - 1 : ℕ) : ℝ) = (km m : ℝ) - 1 := by
            simpa using (Nat.cast_sub hk1 : ((km m - 1 : ℕ) : ℝ) = (km m : ℝ) - ((1 : ℕ) : ℝ))
          dsimp only [d]
          simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat, hk1']
          ring
        have hle_diff : (d m (km m) : ℝ) - (t₀ : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ m := by
          have : (d m (km m - 1) : ℝ) ≤ (t₀ : ℝ) := NNReal.coe_le_coe.mpr hprev
          linarith
        have hM' := hM m hm
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hM'
        linarith
      have hX_tend : Tendsto (fun m => L.X (d m (km m)) ω) atTop (𝓝 (L.X t₀ ω)) :=
        (L.rightCont ω t₀).tendsto.comp hd_tend
      have hd_coe_tend : Tendsto (fun m => (d m (km m) : ℝ)) atTop (𝓝 (t₀ : ℝ)) :=
        (NNReal.continuous_coe.tendsto t₀).comp (tendsto_nhdsWithin_iff.mp hd_tend).1
      exact Real.continuous_exp.continuousAt.tendsto.comp
        ((hX_tend.const_mul θ).sub (hd_coe_tend.mul_const (L.ψ θ)))
  -- Combine via single-L^1 truncation: |LHS - RHS| ≤ ε for every ε > 0
  refine eq_of_forall_dist_le fun ε hε => ?_
  rcases exists_delta_setIntegral_lt (expMart_integrable L hθ n) (expMart_nonneg L θ n)
    (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
  let R : ℝ := max (Real.exp (θ * x) + 1) (2 / δ)
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hR_gt : Real.exp (θ * x) < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR_inv : 1 / R < δ := by
    have h2 : 2 / δ ≤ R := le_max_right _ _
    have h1 : 1 / R ≤ δ / 2 := by
      rw [div_le_div_iff₀ hR_pos zero_lt_two]
      have := mul_le_mul_of_nonneg_right h2 hδ_pos.le
      rw [div_mul_cancel₀ _ hδ_pos.ne'] at this
      linarith
    linarith
  have htail_lt : ∀ m, ∫ ω in Gn ∩ {ω | R < Y m ω}, Y m ω ∂P < ε / 2 := by
    intro m
    rw [hY_tail_eq m R]
    have hset_meas : MeasurableSet (Gn ∩ {ω | R < Y m ω}) :=
      hGn_meas.inter ((hY_meas m) measurableSet_Ioi)
    have hP_le : (P (Gn ∩ {ω | R < Y m ω})).toReal ≤ 1 / R := by
      have hmarkov : R * (P (Gn ∩ {ω | R < Y m ω})).toReal ≤ ∫ ω in Gn, Y m ω ∂P := by
        have h1 : ∫ ω in Gn ∩ {ω | R < Y m ω}, R ∂P ≤ ∫ ω in Gn ∩ {ω | R < Y m ω}, Y m ω ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun _ => hR_pos.le) (hY_int m).integrableOn
            (by filter_upwards [ae_restrict_mem hset_meas] with ω hω; exact hω.2.le)
        rw [setIntegral_const, smul_eq_mul, mul_comm] at h1
        have h2 : ∫ ω in Gn ∩ {ω | R < Y m ω}, Y m ω ∂P ≤ ∫ ω in Gn, Y m ω ∂P :=
          setIntegral_mono_set (hY_int m).integrableOn (ae_of_all _ (hY_nn m))
            (Eventually.of_forall inter_subset_left)
        exact h1.trans h2
      have hle1 : ∫ ω in Gn, Y m ω ∂P ≤ 1 := by
        rw [hY_sum_int m, ← integral_expMart_eq_one L hθ n]
        exact setIntegral_le_integral (expMart_integrable L hθ n) (ae_of_all _ (expMart_nonneg L θ n))
      rw [le_div_iff₀' hR_pos]
      exact hmarkov.trans hle1
    exact hδ _ hset_meas (lt_of_le_of_lt hP_le hR_inv)
  -- Dominated convergence for min (Y m) R on Gn
  have htrunc_tend : Tendsto (fun m => ∫ ω in Gn, min (Y m ω) R ∂P) atTop (𝓝 (∫ ω in Gn, Z ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => R) ?_
      (integrableOn_const (measure_ne_top P Gn)) ?_ ?_
    · intro m
      exact ((hY_int m).aestronglyMeasurable.inf aestronglyMeasurable_const).restrict
    · intro m
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hY_nn m ω) hR_pos.le)]
      exact min_le_right _ _
    · filter_upwards [ae_restrict_mem hGn_meas] with ω hω
      have hminZ : min (Z ω) R = Z ω := min_eq_left ((hZ_le ω).trans hR_gt.le)
      rw [← hminZ]
      exact (hY_tendsto ω hω).min tendsto_const_nhds
  rcases (Metric.tendsto_atTop.mp htrunc_tend) (ε / 2) (half_pos hε) with ⟨m, hm⟩
  have hm0 := hm m (le_refl m)
  rw [Real.dist_eq] at hm0 ⊢
  have hdiff_trunc :
      0 ≤ (∫ ω in Gn, Y m ω ∂P) - (∫ ω in Gn, min (Y m ω) R ∂P) ∧
      (∫ ω in Gn, Y m ω ∂P) - (∫ ω in Gn, min (Y m ω) R ∂P) ≤
        ∫ ω in Gn ∩ {ω | R < Y m ω}, Y m ω ∂P :=
    integral_sub_min_le_tail hGn_meas (hY_int m) (hY_meas m) (hY_nn m) hR_pos.le
  rw [← hY_sum_int m]
  have htr : |∫ ω in Gn, Y m ω ∂P - ∫ ω in Gn, Z ω ∂P| ≤
      |(∫ ω in Gn, Y m ω ∂P) - (∫ ω in Gn, min (Y m ω) R ∂P)| +
      |(∫ ω in Gn, min (Y m ω) R ∂P) - (∫ ω in Gn, Z ω ∂P)| := by
    simpa [sub_add_sub_cancel] using
      abs_add_le ((∫ ω in Gn, Y m ω ∂P) - (∫ ω in Gn, min (Y m ω) R ∂P))
        ((∫ ω in Gn, min (Y m ω) R ∂P) - (∫ ω in Gn, Z ω ∂P))
  rw [abs_of_nonneg hdiff_trunc.1] at htr
  linarith [htail_lt m, hdiff_trunc.2, hm0]

/-! ### 6. Passage to `n → ∞` and then `θ ↓ φ` -/

private lemma laplace_firstHittingTime_eq
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    {x : ℝ} (hx : 0 ≤ x)
    {θ : ℝ} (hθ : 0 ≤ θ) (hψ_pos : 0 < L.ψ θ) :
    let τ := firstHittingTime L.X (Set.Ioi x)
    ∫ ω in {ω | τ ω ≠ ⊤}, Real.exp (-L.ψ θ * untopReal (τ ω)) ∂P =
      Real.exp (-θ * x) := by
  intro τ
  let S : Set Omega := {ω | τ ω ≠ ⊤}
  have hS_meas : MeasurableSet S := (measurable_firstHittingTime L x) (measurableSet_singleton ⊤).compl
  let Z : Omega → ℝ := fun ω => Real.exp (θ * x - untopReal (τ ω) * L.ψ θ)
  have hZ_meas : Measurable Z :=
    Real.measurable_exp.comp
      (measurable_const.sub ((measurable_untopReal.comp (measurable_firstHittingTime L x)).mul_const (L.ψ θ)))
  have hZ_le : ∀ ω, Z ω ≤ Real.exp (θ * x) := fun ω =>
    Real.exp_le_exp.mpr (by linarith [mul_nonneg (untopReal_nonneg (τ ω)) hψ_pos.le])
  have hZ_nn : ∀ ω, 0 ≤ Z ω := fun _ => (Real.exp_pos _).le
  have hdecomp : ∀ n : ℕ,
      (∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}, Z ω ∂P) +
      (∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}ᶜ, expMart L θ (n + 1 : ℕ) ω ∂P) = 1 := by
    intro n
    let Gn := {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}
    have hGn_meas : MeasurableSet Gn := F.le (n + 1 : ℕ) _ (measurableSet_lt_firstHittingTime L x (n + 1 : ℕ))
    rw [← stopped_expMart_horizon_eq P F L hx hθ hψ_pos (n + 1)]
    rw [integral_add_compl hGn_meas (expMart_integrable L hθ (n + 1 : ℕ))]
    exact integral_expMart_eq_one L hθ (n + 1 : ℕ)
  have hcomp_tend : Tendsto
      (fun n : ℕ => ∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}ᶜ,
        expMart L θ (n + 1 : ℕ) ω ∂P)
      atTop (𝓝 0) := by
    refine squeeze_zero
      (g := fun n : ℕ => Real.exp (θ * x - ((n + 1 : ℕ) : ℝ) * L.ψ θ))
      (fun n => integral_nonneg (expMart_nonneg L θ _))
      (fun n => ?_)
      ?_
    · let Gn := {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}
      have hGn_meas : MeasurableSet Gn := F.le (n + 1 : ℕ) _ (measurableSet_lt_firstHittingTime L x (n + 1 : ℕ))
      have hbound : ∫ ω in Gnᶜ, expMart L θ (n + 1 : ℕ) ω ∂P ≤
          ∫ ω in Gnᶜ, Real.exp (θ * x - ((n + 1 : ℕ) : ℝ) * L.ψ θ) ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ (expMart_nonneg L θ _))
          (integrableOn_const (measure_ne_top P Gnᶜ)) ?_
        filter_upwards [ae_restrict_mem hGn_meas.compl] with ω hω
        have hle : (((n + 1 : ℕ) : NNReal) : WithTop NNReal) ≤ τ ω := not_lt.mp hω
        have hXle : L.X (n + 1 : ℕ) ω ≤ x := X_le_of_le_firstHittingTime L hx (n + 1 : ℕ) ω hle
        dsimp only [expMart]
        refine Real.exp_le_exp.mpr ?_
        have h1 : θ * L.X (n + 1 : ℕ) ω ≤ θ * x := mul_le_mul_of_nonneg_left hXle hθ
        have hcast : (((n + 1 : ℕ) : NNReal) : ℝ) = ((n + 1 : ℕ) : ℝ) := by norm_cast
        rw [hcast]
        linarith
      rw [setIntegral_const, smul_eq_mul, Measure.real] at hbound
      have hP1 : (P Gnᶜ).toReal ≤ 1 := by
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      exact hbound.trans (by
        simpa using mul_le_mul_of_nonneg_right hP1 (Real.exp_nonneg (θ * x - ((n + 1 : ℕ) : ℝ) * L.ψ θ)))
    · have hlin : Tendsto (fun n : ℕ => θ * x - ((n + 1 : ℕ) : ℝ) * L.ψ θ) atTop atBot := by
        have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * L.ψ θ) atTop atTop :=
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).atTop_mul_const hψ_pos
        rw [tendsto_atBot]
        intro b
        filter_upwards [h1.eventually (eventually_ge_atTop (θ * x - b))] with n hn
        linarith
      exact Real.tendsto_exp_atBot.comp hlin
  have hfirst_tend : Tendsto
      (fun n : ℕ => ∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}, Z ω ∂P)
      atTop (𝓝 (∫ ω in S, Z ω ∂P)) := by
    have hrew : ∀ n : ℕ,
        ∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}, Z ω ∂P =
          ∫ ω, ({ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}).indicator Z ω ∂P := fun n =>
      (integral_indicator (F.le (n + 1 : ℕ) _ (measurableSet_lt_firstHittingTime L x (n + 1 : ℕ)))).symm
    simp_rw [hrew]
    rw [← integral_indicator hS_meas]
    refine tendsto_integral_of_dominated_convergence (fun _ => Real.exp (θ * x)) ?_
      (integrable_const _) ?_ ?_
    · intro n
      exact (hZ_meas.indicator (F.le (n + 1 : ℕ) _ (measurableSet_lt_firstHittingTime L x (n + 1 : ℕ)))).aestronglyMeasurable
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun ω' _ => hZ_nn ω') ω)]
      by_cases h : ω ∈ {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}
      · rw [Set.indicator_of_mem h]; exact hZ_le ω
      · rw [Set.indicator_of_notMem h]; exact (Real.exp_pos _).le
    · filter_upwards with ω
      cases hτ : τ ω with
      | top =>
        refine tendsto_const_nhds.congr fun n => ?_
        have hnot1 : ω ∉ {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)} := by
          simp [hτ]
        have hnot2 : ω ∉ S := by simp [S, hτ]
        rw [Set.indicator_of_notMem hnot1, Set.indicator_of_notMem hnot2]
      | coe t₀ =>
        rcases exists_nat_gt (t₀ : ℝ) with ⟨N0, hN0⟩
        refine tendsto_atTop_of_eventually_const (i₀ := N0) fun n hn => ?_
        have hmem1 : ω ∈ {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)} := by
          simp only [mem_ofPred_eq, hτ, WithTop.coe_lt_coe]
          rw [← NNReal.coe_lt_coe]
          have : (t₀ : ℝ) < ((n + 1 : ℕ) : ℝ) := by
            have hle : (N0 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
            push_cast
            linarith
          exact_mod_cast this
        have hmem2 : ω ∈ S := by
          change τ ω ≠ ⊤
          rw [hτ]
          exact WithTop.coe_ne_top
        rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
  have hsum_tend : Tendsto
      (fun n : ℕ =>
        (∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}, Z ω ∂P) +
        (∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}ᶜ, expMart L θ (n + 1 : ℕ) ω ∂P))
      atTop (𝓝 ((∫ ω in S, Z ω ∂P) + 0)) := hfirst_tend.add hcomp_tend
  have hZ_eq1 : ∫ ω in S, Z ω ∂P = 1 := by
    have hconst : Tendsto
        (fun n : ℕ =>
          (∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}, Z ω ∂P) +
          (∫ ω in {ω | τ ω < (((n + 1 : ℕ) : NNReal) : WithTop NNReal)}ᶜ, expMart L θ (n + 1 : ℕ) ω ∂P))
        atTop (𝓝 1) := by
      simp_rw [hdecomp]
      exact tendsto_const_nhds
    have heq := tendsto_nhds_unique hsum_tend hconst
    linarith
  have hZ_factor : Z = fun ω => Real.exp (θ * x) * Real.exp (-L.ψ θ * untopReal (τ ω)) := by
    ext ω
    dsimp only [Z]
    rw [← Real.exp_add]
    congr 1; ring
  rw [hZ_factor, integral_const_mul] at hZ_eq1
  have hmul := congrArg (fun v => Real.exp (-θ * x) * v) hZ_eq1
  rw [← mul_assoc, ← Real.exp_add] at hmul
  have hexp0 : Real.exp (-θ * x + θ * x) = 1 := by simp
  rw [hexp0, one_mul, mul_one] at hmul
  exact hmul

end Kyprianou.Ch03.FirstPassageZeroConsequence1Proof

open Kyprianou.Ch03 Kyprianou.Ch03.FirstPassageZeroConsequence1Proof

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      (forall x : Real, 0 <= x ->
        forall finiteTime : Omega -> NNReal,
          (forall omega,
            firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
              firstHittingTime L.X (Set.Ioi x) omega =
                (finiteTime omega : WithTop NNReal)) ->
          (P {omega : Omega |
            firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal =
              Real.exp (-phi * x)) := by
  intro phi hRoot x hx _ _
  let τ := firstHittingTime L.X (Set.Ioi x)
  let S : Set Omega := {ω | τ ω ≠ ⊤}
  have hset_eq : {omega : Omega | firstHittingTime L.X (Set.Ioi x) omega != ⊤} = S := by
    ext ω
    simp [S, τ, bne_iff_ne]
  rw [hset_eq]
  have hCont : ContinuousOn L.ψ (Ici 0) := continuousOn_laplaceExponent_Ici L
  have hψ_pos : ∀ θ : ℝ, phi < θ → 0 < L.ψ θ :=
    psi_pos_of_gt_maximalRoot P F L hNotDecreasing phi hRoot
  let θn : ℕ → ℝ := fun k => phi + 1 / ((k : ℝ) + 1)
  have hθn_gt : ∀ k : ℕ, phi < θn k := fun k => by
    dsimp only [θn]
    linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity]
  have hθn_nn : ∀ k : ℕ, 0 ≤ θn k := fun k => le_trans hRoot.1 (hθn_gt k).le
  have hθn_tend : Tendsto θn atTop (𝓝[Ici 0] phi) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall hθn_nn⟩
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [θn] using tendsto_const_nhds.add h1
  have hψn_tend : Tendsto (fun k => L.ψ (θn k)) atTop (𝓝 0) := by
    rw [← hRoot.2.1]
    exact (hCont phi hRoot.1).tendsto.comp hθn_tend
  have hτ_untop_meas : Measurable (fun ω => untopReal (τ ω)) :=
    measurable_untopReal.comp (measurable_firstHittingTime L x)
  have hLHS_tend : Tendsto
      (fun k => ∫ ω in S, Real.exp (-L.ψ (θn k) * untopReal (τ ω)) ∂P)
      atTop (𝓝 (∫ ω in S, (1 : ℝ) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
      (integrableOn_const (measure_ne_top P S)) ?_ ?_
    · intro k
      exact (Real.measurable_exp.comp (hτ_untop_meas.const_mul (-L.ψ (θn k)))).aestronglyMeasurable.restrict
    · intro k
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      refine Real.exp_le_one_iff.mpr ?_
      have hpos := hψ_pos (θn k) (hθn_gt k)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (untopReal_nonneg _)
    · filter_upwards with ω
      have h0 : Tendsto (fun k => -L.ψ (θn k) * untopReal (τ ω)) atTop (𝓝 0) := by
        simpa using (hψn_tend.neg).mul_const (untopReal (τ ω))
      have h1 : Tendsto (fun k => Real.exp (-L.ψ (θn k) * untopReal (τ ω))) atTop (𝓝 (Real.exp 0)) :=
        Real.continuous_exp.continuousAt.tendsto.comp h0
      simpa [Real.exp_zero] using h1
  have hRHS_tend : Tendsto (fun k => Real.exp (-θn k * x)) atTop (𝓝 (Real.exp (-phi * x))) := by
    have hθn_t : Tendsto θn atTop (𝓝 phi) := (tendsto_nhdsWithin_iff.mp hθn_tend).1
    exact Real.continuous_exp.continuousAt.tendsto.comp ((hθn_t.neg).mul_const x)
  have heq_k : ∀ k : ℕ,
      ∫ ω in S, Real.exp (-L.ψ (θn k) * untopReal (τ ω)) ∂P = Real.exp (-θn k * x) :=
    fun k => laplace_firstHittingTime_eq P F L hx (hθn_nn k) (hψ_pos (θn k) (hθn_gt k))
  simp_rw [heq_k] at hLHS_tend
  have hfinal := tendsto_nhds_unique hLHS_tend hRHS_tend
  simpa [setIntegral_const, Measure.real] using hfinal
