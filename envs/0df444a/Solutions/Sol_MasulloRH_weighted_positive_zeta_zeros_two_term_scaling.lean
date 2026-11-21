-- Prove2me | solution 1 for MasulloRH.weighted_positive_zeta_zeros_two_term_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:42:50.028164+00:00
-- url     : https://prove2.me/submissions/7c1f692d-92e4-43dc-82b3-9f8745fff23f

import Mathlib
import Theorems.Thm_RiemannVonMangoldt_riemann_von_mangoldt
import Definitions.Def_Zeta23_Statement_Seam

/-!
# Logarithmic coefficient of a weighted spectral count

The counting function `N` is first treated abstractly. A bound
`|N(t) - κ t log(1+t)| ≤ C t` at positive heights implies a uniform
error after dilation and pairing with an integrable test derivative.
The leading term is `κ log(1/ε) ∫ u f(u) du`.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace MasulloAudit

/-- The weighted absolute moment used to bound the dilation error on the positive half-line. -/
noncomputable def spectralTestMoment (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  u * |f u| * (1 + |Real.log u| + Real.log (1 + u))

private lemma scale_cumulative_point {N : ℝ → ℝ} {κ C ε u : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hu : 0 < u)
    (hN : ∀ t : ℝ, 0 < t → |N t - κ * t * Real.log (1 + t)| ≤ C * t) :
    |ε * N (u / ε) - κ * Real.log ε⁻¹ * u| ≤
      (C + κ) * (u * (1 + |Real.log u| + Real.log (1 + u))) := by
  have hlog : Real.log (1 + u / ε) = Real.log (ε + u) + Real.log ε⁻¹ := by
    rw [show 1 + u / ε = (ε + u) / ε by field_simp,
      Real.log_div (by positivity) hε.ne', Real.log_inv, sub_eq_add_neg]
  have hscale : |ε * N (u / ε) - κ * u * Real.log (1 + u / ε)| ≤ C * u := by
    have he := mul_le_mul_of_nonneg_left (hN (u / ε) (div_pos hu hε)) hε.le
    calc
      _ = ε * |N (u / ε) - κ * (u / ε) * Real.log (1 + u / ε)| := by
        rw [← abs_of_nonneg (a := ε) hε.le, ← abs_mul, abs_of_nonneg (a := ε) hε.le]
        congr 1
        field_simp
      _ ≤ ε * (C * (u / ε)) := he
      _ = _ := by field_simp
  have hlogBound : |Real.log (ε + u)| ≤ |Real.log u| + Real.log (1 + u) := by
    have hleft := Real.log_le_log hu (by linarith : u ≤ ε + u)
    have hright := Real.log_le_log (by positivity : 0 < ε + u) (by linarith : ε + u ≤ 1 + u)
    have hnonneg := Real.log_nonneg (by linarith : 1 ≤ 1 + u)
    exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log u)],
      by linarith [abs_nonneg (Real.log u)]⟩
  have hrew : ε * N (u / ε) - κ * Real.log ε⁻¹ * u =
      (ε * N (u / ε) - κ * u * Real.log (1 + u / ε)) + κ * u * Real.log (ε + u) := by
    rw [hlog]
    ring
  rw [hrew]
  calc
    _ ≤ |ε * N (u / ε) - κ * u * Real.log (1 + u / ε)| + |κ * u * Real.log (ε + u)| := abs_add_le _ _
    _ ≤ C * u + κ * u * (|Real.log u| + Real.log (1 + u)) := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hκ hu.le)]
      exact add_le_add hscale (mul_le_mul_of_nonneg_left hlogBound (mul_nonneg hκ hu.le))
    _ ≤ _ := by
      have hlog0 := Real.log_nonneg (by linarith : 1 ≤ 1 + u)
      have h0 : 0 ≤ C * u * (|Real.log u| + Real.log (1 + u)) := by positivity
      nlinarith [mul_nonneg hκ hu.le]

private lemma integrableOn_mul_testMoment {f : ℝ → ℝ} (hf : Measurable f)
    (hm : IntegrableOn (spectralTestMoment f) (Ioi (0 : ℝ))) :
    IntegrableOn (fun u ↦ u * f u) (Ioi (0 : ℝ)) := by
  refine hm.mono' (measurable_id.mul hf).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with u hu
  change 0 < u at hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu, spectralTestMoment]
  exact le_mul_of_one_le_right (by positivity) (by
    linarith [abs_nonneg (Real.log u), Real.log_nonneg (by linarith : 1 ≤ 1 + u)])

/-- Paired dilation of a cumulative count, with an explicit error uniform for `0 < ε ≤ 1`. -/
theorem cumulative_count_test_log_scaling (N f : ℝ → ℝ) (hNmeas : Measurable N) (hf : Measurable f)
    {κ C ε : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hN : ∀ t : ℝ, 0 < t → |N t - κ * t * Real.log (1 + t)| ≤ C * t)
    (hm : IntegrableOn (spectralTestMoment f) (Ioi (0 : ℝ))) :
    IntegrableOn (fun u ↦ ε * N (u / ε) * f u) (Ioi (0 : ℝ)) ∧
    |(∫ u in Ioi (0 : ℝ), ε * N (u / ε) * f u) -
      κ * Real.log ε⁻¹ * (∫ u in Ioi (0 : ℝ), u * f u)| ≤
      (C + κ) * (∫ u in Ioi (0 : ℝ), spectralTestMoment f u) := by
  let g : ℝ → ℝ := fun u ↦ ε * N (u / ε) * f u - κ * Real.log ε⁻¹ * (u * f u)
  have hgm : Measurable g := by
    dsimp only [g]
    fun_prop
  have hh := hm.const_mul (C + κ)
  have hdom : ∀ᵐ u ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
      ‖g u‖ ≤ (C + κ) * spectralTestMoment f u := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with u hu
    change 0 < u at hu
    have he := scale_cumulative_point hκ hC hε hε₁ hu hN
    dsimp only [g]
    rw [show ε * N (u / ε) * f u - κ * Real.log ε⁻¹ * (u * f u) =
        (ε * N (u / ε) - κ * Real.log ε⁻¹ * u) * f u by ring,
      Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (C + κ) * (u * (1 + |Real.log u| + Real.log (1 + u))) * |f u| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ = _ := by unfold spectralTestMoment; ring
  have hgi : IntegrableOn g (Ioi (0 : ℝ)) := hh.mono' hgm.aestronglyMeasurable hdom
  have hmain := (integrableOn_mul_testMoment hf hm).const_mul (κ * Real.log ε⁻¹)
  have hsi : IntegrableOn (fun u ↦ ε * N (u / ε) * f u) (Ioi (0 : ℝ)) := by
    simpa only [g, Pi.add_def, sub_add_cancel] using hgi.add hmain
  refine ⟨hsi, ?_⟩
  have hb := norm_integral_le_of_norm_le hh hdom
  rw [Real.norm_eq_abs, integral_const_mul] at hb
  dsimp only [g] at hb
  rw [integral_sub hsi hmain, integral_const_mul] at hb
  exact hb

/-- The integral of a test derivative to the right of a point. -/
noncomputable def positiveTail (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in Ici x, f u

private def spectralWedge (ε : ℝ) : Set (ℝ × ℝ) := {p | p.2 ∈ Ioc 0 (p.1 / ε)}

private lemma measurableSet_spectralWedge (ε : ℝ) : MeasurableSet (spectralWedge ε) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_fst.div_const ε))

private noncomputable def spectralWedgeTest (ε : ℝ) (f : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  (spectralWedge ε).indicator (fun p ↦ f p.1)

private lemma spectralWedgeTest_apply (ε : ℝ) (f : ℝ → ℝ) (u x : ℝ) :
    spectralWedgeTest ε f (u, x) = (Ioc 0 (u / ε)).indicator (fun _ ↦ f u) x := rfl

private lemma countFromMeasure_monotone (μ : Measure ℝ)
    (hfinite : ∀ t : ℝ, 0 < t → μ (Ioc 0 t) ≠ ∞) :
    Monotone (fun t : ℝ ↦ μ.real (Ioc 0 t)) := by
  intro a b hab
  by_cases hb : 0 < b
  · exact measureReal_mono (Ioc_subset_Ioc_right hab) (hfinite b hb)
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hb), Ioc_eq_empty_of_le (hab.trans (le_of_not_gt hb))]

private lemma integral_spectralWedge_right (μ : Measure ℝ) (ε : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    (∫ x, spectralWedgeTest ε f (u, x) ∂μ) = μ.real (Ioc 0 (u / ε)) * f u := by
  simp only [spectralWedgeTest_apply, integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul]

private lemma integral_norm_spectralWedge_right (μ : Measure ℝ) (ε : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    (∫ x, ‖spectralWedgeTest ε f (u, x)‖ ∂μ) = μ.real (Ioc 0 (u / ε)) * |f u| := by
  simp only [spectralWedgeTest_apply, norm_indicator_eq_indicator_norm, Real.norm_eq_abs,
    integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul]

private lemma integral_spectralWedge_left (f : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), spectralWedgeTest ε f (u, x)) =
      (Ioi (0 : ℝ)).indicator (fun x ↦ positiveTail f (ε * x)) x := by
  by_cases hx : 0 < x
  · have hf : (fun u ↦ spectralWedgeTest ε f (u, x)) = (Ici (ε * x)).indicator f := by
      funext u
      rw [spectralWedgeTest_apply]
      have heq : x ∈ Ioc 0 (u / ε) ↔ u ∈ Ici (ε * x) := by
        change (0 < x ∧ x ≤ u / ε) ↔ ε * x ≤ u
        rw [le_div_iff₀ hε, and_iff_right hx, mul_comm x ε]
      by_cases hu : u ∈ Ici (ε * x)
      · rw [indicator_of_mem hu, indicator_of_mem (heq.mpr hu)]
      · rw [indicator_of_notMem hu, indicator_of_notMem (heq.not.mpr hu)]
    rw [hf, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (show Ici (ε * x) ⊆ Ioi 0 from fun _ hu ↦ (mul_pos hε hx).trans_le hu),
      indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), positiveTail]
  · have he (u : ℝ) : x ∉ Ioc 0 (u / ε) := fun h ↦ hx h.1
    simp [spectralWedgeTest_apply, he, indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]

/-- Scaled Fubini identity between tail-test integration and cumulative counts. -/
theorem weighted_measure_tail_count_identity (μ : Measure ℝ) [SFinite μ]
    (f : ℝ → ℝ) (hf : Measurable f)
    {κ C ε : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hfinite : ∀ t : ℝ, 0 < t → μ (Ioc 0 t) ≠ ∞)
    (hN : ∀ t : ℝ, 0 < t → |μ.real (Ioc 0 t) - κ * t * Real.log (1 + t)| ≤ C * t)
    (hm : IntegrableOn (spectralTestMoment f) (Ioi (0 : ℝ))) :
    IntegrableOn (fun x ↦ positiveTail f (ε * x)) (Ioi (0 : ℝ)) μ ∧
    ε * (∫ x in Ioi (0 : ℝ), positiveTail f (ε * x) ∂μ) =
      ∫ u in Ioi (0 : ℝ), ε * μ.real (Ioc 0 (u / ε)) * f u := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let N := fun t : ℝ ↦ μ.real (Ioc 0 t)
  obtain ⟨hsI, _⟩ := cumulative_count_test_log_scaling N f
    (countFromMeasure_monotone μ hfinite).measurable hf hκ hC hε hε₁ hN hm
  have hG : Measurable (spectralWedgeTest ε f) :=
    (hf.comp measurable_fst).indicator (measurableSet_spectralWedge ε)
  have hGI : Integrable (spectralWedgeTest ε f) (ν.prod μ) := by
    refine (integrable_prod_iff hG.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with u hu
      change 0 < u at hu
      simp only [spectralWedgeTest_apply]
      exact (integrableOn_const (C := f u) (hfinite _ (div_pos hu hε))).integrable_indicator
        measurableSet_Ioc
    · simp only [integral_norm_spectralWedge_right]
      apply (hsI.norm.const_mul ε⁻¹).congr
      exact Eventually.of_forall (fun u ↦ by
        change ε⁻¹ * ‖ε * μ.real (Ioc 0 (u / ε)) * f u‖ = μ.real (Ioc 0 (u / ε)) * |f u|
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hε,
          abs_of_nonneg (measureReal_nonneg : 0 ≤ μ.real (Ioc 0 (u / ε))), ← mul_assoc, ← mul_assoc,
          inv_mul_cancel₀ hε.ne', one_mul])
  have htailI : IntegrableOn (fun x ↦ positiveTail f (ε * x)) (Ioi (0 : ℝ)) μ := by
    apply (integrable_indicator_iff measurableSet_Ioi).mp
    exact hGI.integral_prod_right.congr (Eventually.of_forall (integral_spectralWedge_left f hε))
  refine ⟨htailI, ?_⟩
  have heq : (∫ x in Ioi (0 : ℝ), positiveTail f (ε * x) ∂μ) =
      ∫ u in Ioi (0 : ℝ), N (u / ε) * f u := by
    rw [← integral_indicator measurableSet_Ioi]
    simp_rw [← integral_spectralWedge_left f hε]
    have hswap := integral_integral_swap (f := fun u x ↦ spectralWedgeTest ε f (u, x)) hGI
    change (∫ u in Ioi (0 : ℝ), ∫ x, spectralWedgeTest ε f (u, x) ∂μ) =
      ∫ x, (∫ u in Ioi (0 : ℝ), spectralWedgeTest ε f (u, x)) ∂μ at hswap
    rw [← hswap]
    simp only [integral_spectralWedge_right, N]
  rw [heq, ← integral_const_mul]
  simp only [mul_assoc, N]

end MasulloAudit

/-!
# Weighted count of positive-ordinate zeta zeros

The counting measure puts one Dirac mass at each positive zero ordinate,
weighted by its analytic multiplicity. Its cumulative mass matches `N(T)`
with the exact half-open convention `(0,T]`, including boundary zeros.
-/

open Asymptotics Filter MeasureTheory Set
open scoped ENNReal Topology SchwartzMap

namespace MasulloAudit

open Zeta23

/-- Labels for the positive nontrivial zeros. The real part is retained in the label. -/
def PositiveZetaZeroSet : Set ℂ := {ρ | IsNontrivialZero ρ ∧ 0 < ρ.im}

private lemma positiveZetaZeroSet_countable : PositiveZetaZeroSet.Countable := by
  have he : PositiveZetaZeroSet = ⋃ n : ℕ, zerosIn 0 (n : ℝ) := by
    ext ρ
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨hρ, hpos⟩
      obtain ⟨n, hn⟩ := exists_nat_ge ρ.im
      exact ⟨n, hρ, hpos, hn⟩
    · rintro ⟨n, hρ, hpos, _⟩
      exact ⟨hρ, hpos⟩
  rw [he]
  exact Set.countable_iUnion fun n ↦
    ((show (zerosIn 0 (n : ℝ)).Finite from ZetaSeam.finite_window_holds 0 n)).countable

private noncomputable def zeroAtom (ρ : PositiveZetaZeroSet) : Measure ℝ :=
  (zeroMult ρ.val : ℝ≥0∞) • Measure.dirac ρ.val.im

/-- Counting measure with analytic multiplicity at each positive ordinate. -/
noncomputable def positiveZetaZeroMeasure : Measure ℝ := Measure.sum zeroAtom

private instance positiveZetaZeroMeasure_sFinite : SFinite positiveZetaZeroMeasure := by
  let _ : Countable PositiveZetaZeroSet := positiveZetaZeroSet_countable.to_subtype
  let _ : ∀ ρ : PositiveZetaZeroSet, IsFiniteMeasure (zeroAtom ρ) := by
    intro ρ
    constructor
    rw [zeroAtom, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    exact ENNReal.natCast_lt_top _
  exact sfinite_sum_of_countable zeroAtom

private lemma positiveZetaZeroMeasure_mass (t : ℝ) :
    positiveZetaZeroMeasure (Ioc 0 t) = (Ncount 0 t : ℝ≥0∞) := by
  classical
  let f : PositiveZetaZeroSet → ℝ≥0∞ := fun ρ ↦ zeroAtom ρ (Ioc 0 t)
  let A : Set PositiveZetaZeroSet := {ρ | ρ.val.im ≤ t}
  have hsupport : Function.support f ⊆ A := by
    intro ρ hρ
    by_contra hbad
    have hn : ρ.val.im ∉ Ioc 0 t := fun ht ↦ hbad ht.2
    exact hρ (by simp [f, zeroAtom, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc,
      indicator_of_notMem hn])
  let e : A ≃ zerosIn 0 t :=
    { toFun := fun ρ ↦ ⟨ρ.val.val, ρ.val.property.1, ρ.val.property.2, ρ.property⟩
      invFun := fun ρ ↦ ⟨⟨ρ.val, ρ.property.1, ρ.property.2.1⟩, ρ.property.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hf (ρ : A) : f ρ.val = (zeroMult (e ρ).val : ℝ≥0∞) := by
    have hmem : ρ.val.val.im ∈ Ioc 0 t := ⟨ρ.val.property.2, ρ.property⟩
    simp [f, zeroAtom, Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Ioc,
      indicator_of_mem hmem, smul_eq_mul, e]
  have hZ : (zerosIn 0 t).Finite := ZetaSeam.finite_window_holds 0 t
  calc
    _ = ∑' ρ, f ρ := Measure.sum_apply zeroAtom measurableSet_Ioc
    _ = ∑' ρ : A, f ρ.val := (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' ρ : A, (zeroMult (e ρ).val : ℝ≥0∞) := tsum_congr hf
    _ = ∑' ρ : zerosIn 0 t, (zeroMult ρ.val : ℝ≥0∞) :=
      e.tsum_eq (fun ρ ↦ (zeroMult ρ.val : ℝ≥0∞))
    _ = _ := by
      have hSup : Function.support ((zerosIn 0 t).indicator (fun z ↦ (zeroMult z : ℝ≥0∞))) ⊆
          zerosIn 0 t := support_indicator_subset
      rw [tsum_subtype (zerosIn 0 t) (fun z ↦ (zeroMult z : ℝ≥0∞)),
        tsum_eq_finsum (hZ.subset hSup), ← finsum_mem_def, Ncount, Nat.cast_finsum_mem hZ]

private lemma positiveZetaZeroMeasure_count (t : ℝ) :
    positiveZetaZeroMeasure.real (Ioc 0 t) = (Ncount 0 t : ℝ) := by
  rw [Measure.real, positiveZetaZeroMeasure_mass, ENNReal.toReal_natCast]

private lemma zetaZeroCount_eq (t : ℝ) :
    RiemannVonMangoldt.zetaZeroCount t = (Ncount 0 t : ℝ) := by
  unfold RiemannVonMangoldt.zetaZeroCount Ncount
  have he : {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ t ∧ riemannZeta s = 0} =
      zerosIn 0 t := by
    ext s
    simp only [zerosIn, IsNontrivialZero, Set.mem_ofPred_eq]
    tauto
  have hZ : (zerosIn 0 t).Finite := ZetaSeam.finite_window_holds 0 t
  rw [he, Nat.cast_finsum_mem hZ]
  rfl

private lemma count_monotone : Monotone (fun t ↦ (Ncount 0 t : ℝ)) := by
  intro a b hab
  change (Ncount 0 a : ℝ) ≤ (Ncount 0 b : ℝ)
  rw [← positiveZetaZeroMeasure_count, ← positiveZetaZeroMeasure_count]
  refine measureReal_mono (Ioc_subset_Ioc_right hab) ?_
  rw [positiveZetaZeroMeasure_mass]
  exact ENNReal.natCast_ne_top _

private lemma exists_zero_free_low_window : ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, t < δ → Ncount 0 t = 0 := by
  classical
  have hz : (zerosIn 0 1).Finite := ZetaSeam.finite_window_holds 0 1
  let S := hz.toFinset
  by_cases hs : S.Nonempty
  · obtain ⟨ρ, hρ, hmin⟩ := S.exists_min_image Complex.im hs
    have hρ' := hz.mem_toFinset.mp hρ
    refine ⟨ρ.im, hρ'.2.1, fun t ht ↦ ?_⟩
    have he : zerosIn 0 t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz'
      have hz₁ : z ∈ zerosIn 0 1 :=
        ⟨hz'.1, hz'.2.1, hz'.2.2.trans (ht.le.trans hρ'.2.2)⟩
      exact (not_le.mpr ht) ((hmin z (hz.mem_toFinset.mpr hz₁)).trans hz'.2.2)
    simp [Ncount, he]
  · refine ⟨1, zero_lt_one, fun t ht ↦ ?_⟩
    have he : zerosIn 0 t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz'
      have hz₁ : z ∈ zerosIn 0 1 := ⟨hz'.1, hz'.2.1, hz'.2.2.trans ht.le⟩
      exact hs ⟨z, hz.mem_toFinset.mpr hz₁⟩
    simp [Ncount, he]

private lemma cumulative_count_all_positive_heights :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |(Ncount 0 t : ℝ) - (1 / (2 * Real.pi)) * t * Real.log (1 + t)| ≤ C * t := by
  let κ := 1 / (2 * Real.pi)
  have hκ : 0 < κ := by unfold κ; positivity
  obtain ⟨K, hK, hevent⟩ :=
    Asymptotics.isBigO_iff'.mp RiemannVonMangoldt.riemann_von_mangoldt
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hevent
  let A := max T₀ 1
  have hA : 1 ≤ A := le_max_right _ _
  let D := Real.log 2 + |Real.log (2 * Real.pi) + 1|
  have hD : 0 ≤ D := add_nonneg (Real.log_nonneg (by norm_num)) (abs_nonneg _)
  have hlarge (t : ℝ) (ht : A ≤ t) :
      |(Ncount 0 t : ℝ) - κ * t * Real.log (1 + t)| ≤ (K + κ * D) * t := by
    have ht₁ : 1 ≤ t := hA.trans ht
    have ht₀ : 0 < t := zero_lt_one.trans_le ht₁
    have hlog₀ : 0 ≤ Real.log t := Real.log_nonneg ht₁
    have he := hT₀ t ((le_max_left T₀ 1).trans ht)
    change ‖RiemannVonMangoldt.zetaZeroCount t -
       (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi))‖ ≤ K * ‖Real.log t‖ at he
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hlog₀, zetaZeroCount_eq,
      Real.log_div ht₀.ne' (by positivity)] at he
    let F := κ * t * (Real.log t - Real.log (2 * Real.pi) - 1)
    have hF : t / (2 * Real.pi) * (Real.log t - Real.log (2 * Real.pi)) - t / (2 * Real.pi) = F := by
      unfold F κ
      ring
    rw [hF] at he
    have hlog : |Real.log t - Real.log (1 + t)| ≤ Real.log 2 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ht₀ (by linarith)))]
      have hb := Real.log_le_log (by positivity : 0 < 1 + t) (by linarith : 1 + t ≤ 2 * t)
      rw [Real.log_mul (by norm_num) ht₀.ne'] at hb
      linarith
    have hdiff : |F - κ * t * Real.log (1 + t)| ≤ κ * t * D := by
      have heq : F - κ * t * Real.log (1 + t) =
          κ * t * ((Real.log t - Real.log (1 + t)) - (Real.log (2 * Real.pi) + 1)) := by
        unfold F
        ring
      rw [heq, abs_mul, abs_of_nonneg (mul_nonneg hκ.le ht₀.le)]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hlog le_rfl))
        (mul_nonneg hκ.le ht₀.le)
    calc
      _ ≤ |(Ncount 0 t : ℝ) - F| + |F - κ * t * Real.log (1 + t)| := by
        have heq : (Ncount 0 t : ℝ) - κ * t * Real.log (1 + t) =
            ((Ncount 0 t : ℝ) - F) + (F - κ * t * Real.log (1 + t)) := by ring
        rw [heq]
        exact abs_add_le _ _
      _ ≤ K * t + κ * t * D := add_le_add
        (he.trans (mul_le_mul_of_nonneg_left (Real.log_le_self ht₀.le) hK.le)) hdiff
      _ = _ := by ring
  obtain ⟨δ, hδ, hzero⟩ := exists_zero_free_low_window
  let B := (Ncount 0 A : ℝ) / δ
  have hB : 0 ≤ B := by unfold B; positivity
  have hlogA : 0 ≤ Real.log (1 + A) := Real.log_nonneg (by linarith)
  have hsmall (t : ℝ) (ht : 0 < t) (htA : t ≤ A) :
      |(Ncount 0 t : ℝ) - κ * t * Real.log (1 + t)| ≤ (B + κ * Real.log (1 + A)) * t := by
    have hNt : (Ncount 0 t : ℝ) ≤ B * t := by
      rcases lt_or_ge t δ with h | h
      · rw [hzero t h, Nat.cast_zero]
        positivity
      · calc
          _ ≤ (Ncount 0 A : ℝ) := count_monotone htA
          _ = B * δ := by unfold B; rw [div_mul_cancel₀ _ hδ.ne']
          _ ≤ _ := mul_le_mul_of_nonneg_left h hB
    have hlog : Real.log (1 + t) ≤ Real.log (1 + A) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog₀ : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    calc
      _ ≤ |(Ncount 0 t : ℝ)| + |κ * t * Real.log (1 + t)| := abs_sub _ _
      _ = (Ncount 0 t : ℝ) + κ * t * Real.log (1 + t) := by
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      _ ≤ B * t + κ * t * Real.log (1 + A) :=
        add_le_add hNt (mul_le_mul_of_nonneg_left hlog (by positivity))
      _ = _ := by ring
  have hlarge₀ : 0 ≤ K + κ * D := by positivity
  have hsmall₀ : 0 ≤ B + κ * Real.log (1 + A) := by positivity
  refine ⟨(K + κ * D) + (B + κ * Real.log (1 + A)), by positivity, fun t ht ↦ ?_⟩
  rcases le_or_gt A t with h | h
  · exact (hlarge t h).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsmall₀) ht.le)
  · exact (hsmall t ht h.le).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hlarge₀) ht.le)

private lemma positiveZetaZeroMeasure_restrict :
    positiveZetaZeroMeasure.restrict (Ioi 0) = positiveZetaZeroMeasure := by
  classical
  rw [positiveZetaZeroMeasure, Measure.restrict_sum _ measurableSet_Ioi]
  congr 1
  funext ρ
  change (zeroAtom (ρ : PositiveZetaZeroSet)).restrict (Ioi 0) = zeroAtom ρ
  rw [zeroAtom, Measure.restrict_smul, restrict_dirac, if_pos (show ρ.val.im ∈ Ioi (0 : ℝ) from ρ.property.2)]

/-- Exact Abel pairing with the cumulative positive-ordinate zero count. -/
theorem weighted_positive_zeta_zeros_count_identity (f : ℝ → ℝ) (hf : Measurable f)
    (hm : IntegrableOn (spectralTestMoment f) (Ioi (0 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    Summable (fun ρ : PositiveZetaZeroSet ↦ (zeroMult ρ.val : ℝ) * positiveTail f (ε * ρ.val.im)) ∧
    ε * (∑' ρ : PositiveZetaZeroSet, (zeroMult ρ.val : ℝ) * positiveTail f (ε * ρ.val.im)) =
      ∫ u in Ioi (0 : ℝ), ε * (Ncount 0 (u/ε) : ℝ) * f u := by
  obtain ⟨C, hC, hcount⟩ := cumulative_count_all_positive_heights
  have hκ : 0 ≤ 1 / (2 * Real.pi) := by positivity
  obtain ⟨hI, hB⟩ := weighted_measure_tail_count_identity positiveZetaZeroMeasure f hf hκ hC hε hε₁
    (fun t _ ↦ by rw [positiveZetaZeroMeasure_mass]; exact ENNReal.natCast_ne_top _)
    (fun t ht ↦ by rw [positiveZetaZeroMeasure_count]; exact hcount t ht) hm
  change Integrable (fun x ↦ positiveTail f (ε * x))
    (positiveZetaZeroMeasure.restrict (Ioi (0 : ℝ))) at hI
  rw [positiveZetaZeroMeasure_restrict] at hI hB
  have hsum := hasSum_integral_measure (show Integrable (fun x ↦ positiveTail f (ε * x))
      (Measure.sum zeroAtom) from hI)
  simp only [zeroAtom, integral_smul_measure, integral_dirac, ENNReal.toReal_natCast, smul_eq_mul]
    at hsum
  have hEq (u : ℝ) := positiveZetaZeroMeasure_count (u/ε)
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq]
  change ε * (∫ x : ℝ, positiveTail f (ε*x) ∂positiveZetaZeroMeasure) = _
  simpa only [hEq] using hB

private lemma small_log_moment {x : ℝ} (hx : 0 < x) : x * |Real.log x| ≤ 1 + x ^ 2 := by
  rcases le_or_gt x 1 with h | h
  · rw [abs_of_nonpos (Real.log_nonpos hx.le h), ← Real.log_inv]
    calc
      _ ≤ x * x⁻¹ := mul_le_mul_of_nonneg_left (Real.log_le_self (inv_nonneg.mpr hx.le)) hx.le
      _ = 1 := mul_inv_cancel₀ hx.ne'
      _ ≤ _ := le_add_of_nonneg_right (sq_nonneg _)
  · rw [abs_of_nonneg (Real.log_nonneg h.le)]
    exact (mul_le_mul_of_nonneg_left (Real.log_le_self hx.le) hx.le).trans (by nlinarith)

private lemma schwartz_testMoment (F : 𝓢(ℝ, ℝ)) :
    IntegrableOn (spectralTestMoment F) (Ioi (0 : ℝ)) := by
  have h₀ := F.integrable_pow_mul (volume : Measure ℝ) 0
  have h₁ := F.integrable_pow_mul (volume : Measure ℝ) 1
  have h₂ := (F.integrable_pow_mul (volume : Measure ℝ) 2).const_mul 2
  have hB : Integrable (fun x ↦ (‖x‖ ^ 0 * ‖F x‖) + (‖x‖ ^ 1 * ‖F x‖) +
      2 * (‖x‖ ^ 2 * ‖F x‖)) := (h₀.add h₁).add h₂
  refine hB.integrableOn.mono' (by unfold spectralTestMoment; fun_prop) ?_
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with x hx
  change 0 < x at hx
  have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hlogle : Real.log (1 + x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + x by positivity)
  have hle : x * (1 + |Real.log x| + Real.log (1 + x)) ≤ 1 + x + 2 * x ^ 2 := by
    nlinarith [small_log_moment hx, mul_le_mul_of_nonneg_left hlogle hx.le]
  simp only [Real.norm_eq_abs, abs_of_pos hx, pow_zero, one_mul, pow_one]
  unfold spectralTestMoment
  rw [abs_of_nonneg (by positivity)]
  calc
    _ = (x * (1 + |Real.log x| + Real.log (1 + x))) * |F x| := by ring
    _ ≤ (1 + x + 2 * x ^ 2) * |F x| := mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = _ := by ring

private lemma schwartz_tail_derivative (F : 𝓢(ℝ, ℝ)) (x : ℝ) :
    positiveTail (-(SchwartzMap.derivCLM ℝ ℝ F) : 𝓢(ℝ, ℝ)) x = F x := by
  let f : 𝓢(ℝ, ℝ) := -(SchwartzMap.derivCLM ℝ ℝ F)
  have hderiv (t : ℝ) : HasDerivAt (fun u ↦ -F u) (f t) t := (F.hasDerivAt t).neg
  have hlim : Tendsto (fun u ↦ -F u) atTop (𝓝 0) := by
    simpa only [neg_zero] using (F.tendsto_cocompact.mono_left atTop_le_cocompact).neg
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto (a := x) F.continuous.neg.continuousWithinAt
    (fun t _ ↦ hderiv t) f.integrable.integrableOn hlim
  change (∫ u in Ici x, f u) = F x
  rw [← setIntegral_congr_set Ioi_ae_eq_Ici, hi, zero_sub]
  exact neg_neg _

private lemma schwartz_derivative_moment (F : 𝓢(ℝ, ℝ)) :
    (∫ u in Ioi (0 : ℝ), u * (-(SchwartzMap.derivCLM ℝ ℝ F) : 𝓢(ℝ, ℝ)) u) =
      ∫ u in Ioi (0 : ℝ), F u := by
  let f : 𝓢(ℝ, ℝ) := -(SchwartzMap.derivCLM ℝ ℝ F)
  let P : 𝓢(ℝ, ℝ) := SchwartzMap.smulLeftCLM ℝ (id : ℝ → ℝ) F
  have hP (x : ℝ) : P x = x * F x :=
    SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id F x
  have hlim : Tendsto (fun u : ℝ ↦ u * F u) atTop (𝓝 0) := by
    have h := P.tendsto_cocompact.mono_left atTop_le_cocompact
    exact h.congr (fun u ↦ hP u)
  have hI : IntegrableOn (fun x : ℝ ↦ x * f x) (Ioi (0 : ℝ)) := by
    have hi := (f.integrable_pow_mul (volume : Measure ℝ) 1).integrableOn (s := Ioi (0 : ℝ))
    refine hi.mono' (by fun_prop) ?_
    exact Eventually.of_forall (fun x ↦ by rw [norm_mul, pow_one])
  have hderiv (t : ℝ) : HasDerivAt (fun u : ℝ ↦ u * F u) (F t - t * f t) t := by
    simpa [f, Pi.mul_def, mul_neg] using (hasDerivAt_id t).mul (F.hasDerivAt t)
  have hcont : Continuous (fun u : ℝ ↦ u * F u) := continuous_id.mul F.continuous
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt
    (fun t _ ↦ hderiv t) (F.integrable.integrableOn.sub hI) hlim
  rw [integral_sub F.integrable.integrableOn hI, zero_mul, sub_zero] at hi
  exact (sub_eq_zero.mp hi).symm

private noncomputable def rvmMain (t : ℝ) : ℝ :=
  (1/(2*Real.pi))*t*(Real.log t-Real.log (2*Real.pi)-1)

private noncomputable def rvmError (t : ℝ) : ℝ :=
  (Ncount 0 t : ℝ) - rvmMain t

private lemma rvmMain_continuous : Continuous rvmMain := by
  have hEq : rvmMain = fun t : ℝ ↦ (1/(2*Real.pi)) *
      (t*Real.log t-(Real.log (2*Real.pi)+1)*t) := by
    funext t
    unfold rvmMain
    ring
  rw [hEq]
  exact continuous_const.mul (Real.continuous_mul_log.sub (continuous_const.mul continuous_id))

private lemma rvmError_log_bound :
    ∃ K ≥ (0:ℝ), ∀ t > (0:ℝ), |rvmError t| ≤ K*(1+Real.log (1+t)) := by
  obtain ⟨K,hK,hBig⟩ := Asymptotics.isBigO_iff'.mp RiemannVonMangoldt.riemann_von_mangoldt
  obtain ⟨A₀,hA₀⟩ := eventually_atTop.mp hBig
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  obtain ⟨M,hM,hBound⟩ := (isCompact_Icc.image rvmMain_continuous :
      IsCompact (rvmMain '' Icc (0:ℝ) A)).isBounded.exists_pos_norm_le
  let L := (Ncount 0 A : ℝ)+M
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨K+L,by positivity,fun t ht ↦ ?_⟩
  have hLog : 0 ≤ Real.log (1+t) := Real.log_nonneg (by linarith)
  have hFact : 1 ≤ 1+Real.log (1+t) := by linarith
  rcases le_or_gt A t with h | h
  · have ht₁ : 1 ≤ t := hA.trans h
    have he := hA₀ t ((le_max_right _ _).trans h)
    change ‖RiemannVonMangoldt.zetaZeroCount t -
      (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi))‖ ≤ K * ‖Real.log t‖ at he
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.log_nonneg ht₁), zetaZeroCount_eq,
      Real.log_div ht.ne' (by positivity)] at he
    have he' : |rvmError t| ≤ K*Real.log t := by
      have hMain : rvmMain t = t/(2*Real.pi)*(Real.log t-Real.log (2*Real.pi)) - t/(2*Real.pi) := by
        unfold rvmMain
        ring
      simpa only [rvmError,hMain] using he
    calc
      _ ≤ K*Real.log t := he'
      _ ≤ K*(1+Real.log (1+t)) :=
        mul_le_mul_of_nonneg_left
          ((Real.log_le_log ht (by linarith)).trans (le_add_of_nonneg_left zero_le_one)) hK.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL) (by positivity)
  · have hT : |rvmMain t| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hBound _ ⟨t,⟨ht.le,h.le⟩,rfl⟩
    calc
      _ ≤ |(Ncount 0 t : ℝ)|+|rvmMain t| := abs_sub _ _
      _ ≤ L := by
        dsimp [L]
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        exact add_le_add (count_monotone h.le) hT
      _ ≤ L*(1+Real.log (1+t)) := le_mul_of_one_le_right hL hFact
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) (by positivity)

private lemma scaled_rvmError_point {K ε u : ℝ} (hK : 0 ≤ K)
    (hR : ∀ t > (0:ℝ), |rvmError t| ≤ K*(1+Real.log (1+t)))
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hu : 0 < u) :
    |ε*rvmError (u/ε)| ≤ K*ε*(1+Real.log ε⁻¹)*(1+u) := by
  have hLog : Real.log (1+u/ε) ≤ Real.log ε⁻¹ + u := by
    rw [show 1+u/ε = (ε+u)/ε by field_simp, Real.log_div (by positivity) hε.ne',
      Real.log_inv]
    have hL := Real.log_le_log (by positivity : 0 < ε+u)
      (show ε+u ≤ 1+u by linarith)
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1+u by positivity)]
  have hL0 : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg ((one_le_inv₀ hε).mpr hε₁)
  rw [abs_mul, abs_of_pos hε]
  calc
    _ ≤ ε*(K*(1+Real.log (1+u/ε))) :=
      mul_le_mul_of_nonneg_left (hR _ (div_pos hu hε)) hε.le
    _ ≤ ε*(K*((1+Real.log ε⁻¹)+u)) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      apply mul_le_mul_of_nonneg_left _ hK
      simpa only [add_assoc] using add_le_add le_rfl hLog
    _ ≤ _ := by
      have h := mul_nonneg hL0 hu.le
      have h' : (1+Real.log ε⁻¹)+u ≤ (1+Real.log ε⁻¹)*(1+u) := by linarith only [h]
      have h'' := mul_le_mul_of_nonneg_left h' (mul_nonneg hε.le hK)
      nlinarith only [h'']


private lemma log_mul_schwartz_integrableOn (F : 𝓢(ℝ, ℝ)) :
    IntegrableOn (fun u : ℝ ↦ Real.log u * F u) (Ioi 0) := by
  let A := Ioc (0:ℝ) 1
  let B := Ioi (1:ℝ)
  have hMeas : Measurable (fun u : ℝ ↦ Real.log u * F u) :=
    Real.measurable_log.mul F.continuous.measurable
  have hLog : IntegrableOn Real.log A :=
    (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := 1)).1
  let C := SchwartzMap.seminorm ℝ 0 0 F
  have hNear : IntegrableOn (fun u : ℝ ↦ Real.log u * F u) A := by
    refine (hLog.norm.const_mul C).mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ F x) (norm_nonneg _)
  have hFar : IntegrableOn (fun u : ℝ ↦ Real.log u * F u) B := by
    have hI := (F.integrable_pow_mul volume 1).integrableOn (s := B)
    refine hI.mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    have hu' : 1 < u := hu
    have hu0 := zero_lt_one.trans hu'
    rw [norm_mul, pow_one, Real.norm_of_nonneg (Real.log_nonneg hu'.le), Real.norm_of_nonneg hu0.le]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos hu0).trans (sub_le_self _ zero_le_one)) (norm_nonneg _)
  simpa only [A, B, Ioc_union_Ioi_eq_Ioi zero_le_one] using hNear.union hFar

private noncomputable def logPrimitive (b u : ℝ) : ℝ :=
  u*(Real.log u-b-1)

private lemma logPrimitive_continuous (b : ℝ) : Continuous (logPrimitive b) := by
  have hEq : logPrimitive b = fun u : ℝ ↦ u*Real.log u-(b+1)*u := by
    funext u
    unfold logPrimitive
    ring
  rw [hEq]
  exact Real.continuous_mul_log.sub (continuous_const.mul continuous_id)

private lemma logPrimitive_hasDerivAt (b : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (logPrimitive b) (Real.log u-b) u := by
  have h := (hasDerivAt_id u).mul
    (((Real.hasDerivAt_log hu.ne').sub_const b).sub_const 1)
  have hc : 1*(Real.log u-b-1) + u*u⁻¹ = Real.log u-b := by
    rw [one_mul, mul_inv_cancel₀ hu.ne']
    ring
  exact hc ▸ h

private lemma logPrimitive_mul_integrable (F : 𝓢(ℝ, ℝ)) (b : ℝ) :
    IntegrableOn (fun u : ℝ ↦ logPrimitive b u * F u) (Ioi 0) := by
  have he : Measurable (fun u : ℝ ↦ logPrimitive b u * F u) :=
    (logPrimitive_continuous b).measurable.mul F.continuous.measurable
  refine ((schwartz_testMoment F).const_mul (1+|b|)).mono' he.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  have hLog : 0 ≤ Real.log (1+u) := Real.log_nonneg (by linarith)
  have hB : |Real.log u-b-1| ≤ |Real.log u|+|b|+1 := by
    calc _ ≤ |Real.log u-b|+|1| := abs_sub _ _
         _ ≤ _ := by simpa only [abs_one] using add_le_add (abs_sub (Real.log u) b) le_rfl
  rw [Real.norm_eq_abs, logPrimitive, abs_mul, abs_mul, abs_of_pos hu0, spectralTestMoment]
  calc
    _ = (u*|F u|)*|Real.log u-b-1| := by ring
    _ ≤ (u*|F u|)*(|Real.log u|+|b|+1) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ (u*|F u|)*((1+|b|)*(1+|Real.log u|+Real.log (1+u))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (abs_nonneg b) (abs_nonneg (Real.log u)),
        mul_nonneg (abs_nonneg b) hLog]
    _ = _ := by ring

private lemma logPrimitive_mul_tendsto_zero (F : 𝓢(ℝ, ℝ)) (b : ℝ) :
    Tendsto (fun u : ℝ ↦ logPrimitive b u * F u) atTop (𝓝 0) := by
  let C := SchwartzMap.seminorm ℝ 3 0 F
  have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h' : Tendsto (fun u : ℝ ↦ (2+|b|)*C/u) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using h.const_mul ((2+|b|)*C)
  refine squeeze_zero_norm' ?_ h'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
  have hu0 := zero_lt_one.trans_le hu
  have hF : |F u| ≤ C/u^3 := by
    apply (le_div_iff₀ (pow_pos hu0 _)).mpr
    have hF := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 3 u
    rw [Real.norm_of_nonneg hu0.le, Real.norm_eq_abs (F u), mul_comm] at hF
    exact hF
  have hP : |logPrimitive b u| ≤ (2+|b|)*u^2 := by
    have hB : |Real.log u-b-1| ≤ Real.log u+|b|+1 := by
      calc _ ≤ |Real.log u-b|+|1| := abs_sub _ _
           _ ≤ _ := by simpa only [abs_one, abs_of_nonneg (Real.log_nonneg hu)] using
             add_le_add (abs_sub (Real.log u) b) le_rfl
    rw [logPrimitive, abs_mul, abs_of_pos hu0]
    calc
      _ ≤ u*(Real.log u+|b|+1) := mul_le_mul_of_nonneg_left hB hu0.le
      _ ≤ u*(u+|b|+1) := by
        exact mul_le_mul_of_nonneg_left
          (by linarith [Real.log_le_sub_one_of_pos hu0]) hu0.le
      _ ≤ _ := by
        have hB := mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hu)
        have hh : u+|b|+1 ≤ (2+|b|)*u := by linarith only [hB,hu]
        exact (mul_le_mul_of_nonneg_left hh hu0.le).trans_eq (by ring)
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ ((2+|b|)*u^2)*(C/u^3) := mul_le_mul hP hF (abs_nonneg _) (by positivity)
    _ = _ := by field_simp [hu0.ne']

private lemma schwartz_log_derivative_moment (F : 𝓢(ℝ, ℝ)) (b : ℝ) :
    (∫ u in Ioi (0:ℝ), logPrimitive b u * (-(SchwartzMap.derivCLM ℝ ℝ F) : 𝓢(ℝ, ℝ)) u) =
      ∫ u in Ioi (0:ℝ), (Real.log u-b)*F u := by
  let f : 𝓢(ℝ, ℝ) := -(SchwartzMap.derivCLM ℝ ℝ F)
  have hDer (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun x : ℝ ↦ logPrimitive b x * F x)
        ((Real.log u-b)*F u - logPrimitive b u * f u) u := by
    simpa only [f, neg_apply, SchwartzMap.derivCLM_apply, mul_neg, sub_neg_eq_add] using!
      (logPrimitive_hasDerivAt b hu).mul (F.hasDerivAt u)
  have hL : IntegrableOn (fun u : ℝ ↦ (Real.log u-b)*F u) (Ioi 0) := by
    simp_rw [sub_mul]
    exact (log_mul_schwartz_integrableOn F).sub (F.integrable.const_mul b).integrableOn
  have hF : IntegrableOn (fun u : ℝ ↦ logPrimitive b u * f u) (Ioi 0) :=
    logPrimitive_mul_integrable f b
  have hC := (logPrimitive_continuous b).mul F.continuous
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) hC.continuousWithinAt
    (fun u hu ↦ hDer u hu) (hL.sub hF) (logPrimitive_mul_tendsto_zero F b)
  change (∫ u in Ioi (0:ℝ), (Real.log u-b)*F u-logPrimitive b u*f u) =
    0-logPrimitive b 0*F 0 at h
  rw [integral_sub hL hF] at h
  simp only [logPrimitive, zero_mul, sub_zero] at h
  exact (sub_eq_zero.mp h).symm


private lemma integrableOn_one_add_mul_abs_schwartz (f : 𝓢(ℝ, ℝ)) :
    IntegrableOn (fun u : ℝ ↦ (1+u)*|f u|) (Ioi 0) := by
  have hA : Integrable (fun u : ℝ ↦ |f u|) := by
    simpa only [Real.norm_eq_abs] using (f.integrable (μ := volume)).norm
  have hB : Integrable (fun u : ℝ ↦ |u| *|f u|) := by
    simpa only [pow_one, Real.norm_eq_abs] using f.integrable_pow_mul volume 1
  have hI : IntegrableOn (fun u : ℝ ↦ |f u|+|u| *|f u|) (Ioi 0) :=
    (hA.add hB).integrableOn
  refine hI.congr_fun (fun u hu ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [abs_of_pos (show 0 < u from hu)]
  ring

private lemma rvm_scaled_error_integral_bound (f : 𝓢(ℝ, ℝ)) {K ε : ℝ}
    (hK : 0 ≤ K) (hR : ∀ t > (0:ℝ), |rvmError t| ≤ K*(1+Real.log (1+t)))
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    IntegrableOn (fun u : ℝ ↦ ε*rvmError (u/ε)*f u) (Ioi 0) ∧
    |∫ u in Ioi (0:ℝ), ε*rvmError (u/ε)*f u| ≤
      (K*(∫ u in Ioi (0:ℝ), (1+u)*|f u|))*ε*(1+Real.log ε⁻¹) := by
  let G (u : ℝ) := (1+u)*|f u|
  let W := K*ε*(1+Real.log ε⁻¹)
  have hI : IntegrableOn G (Ioi 0) := integrableOn_one_add_mul_abs_schwartz f
  have hM : Measurable (fun u : ℝ ↦ ε*rvmError (u/ε)*f u) := by
    have hR : Measurable rvmError := count_monotone.measurable.sub rvmMain_continuous.measurable
    exact (measurable_const.mul (hR.comp (measurable_id.div_const ε))).mul f.continuous.measurable
  have hBd : ∀ᵐ u ∂(volume.restrict (Ioi (0:ℝ))), ‖ε*rvmError (u/ε)*f u‖ ≤ W*G u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (K*ε*(1+Real.log ε⁻¹)*(1+u))*|f u| :=
        mul_le_mul_of_nonneg_right (scaled_rvmError_point hK hR hε hε₁ hu) (abs_nonneg _)
      _ = _ := by unfold W G; ring
  have hE := (hI.const_mul W).mono' hM.aestronglyMeasurable hBd
  refine ⟨hE, ?_⟩
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ∫ u in Ioi (0:ℝ), W*G u := norm_integral_le_of_norm_le (hI.const_mul W) hBd
    _ = _ := by rw [integral_const_mul]; unfold W G; ring

private lemma rvm_scaled_count_split {ε u : ℝ} (hε : 0 < ε) (hu : 0 < u) :
    ε*(Ncount 0 (u/ε) : ℝ) =
      (1/(2*Real.pi))*Real.log ε⁻¹*u +
        (1/(2*Real.pi))*logPrimitive (Real.log (2*Real.pi)) u +
        ε*rvmError (u/ε) := by
  unfold rvmError rvmMain logPrimitive
  rw [Real.log_div hu.ne' hε.ne', Real.log_inv]
  field_simp [hε.ne', Real.pi_ne_zero]
  ring

/-- The two leading terms of the dilated positive-ordinate Schwartz zero sum.
The remainder comes from the logarithmic error in the exact Riemann–von Mangoldt formula. -/
theorem weighted_positive_zeta_zeros_two_term_scaling_aux (F : 𝓢(ℝ, ℝ)) :
    ∃ C ≥ (0:ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Summable (fun ρ : PositiveZetaZeroSet ↦ (zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) ∧
      |ε*(∑' ρ : PositiveZetaZeroSet, (zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) -
          (1/(2*Real.pi))*Real.log ε⁻¹*(∫ u in Ioi (0:ℝ), F u) -
          (1/(2*Real.pi))*(∫ u in Ioi (0:ℝ), (Real.log u-Real.log (2*Real.pi))*F u)| ≤
        C*ε*(1+Real.log ε⁻¹) := by
  let f : 𝓢(ℝ, ℝ) := -(SchwartzMap.derivCLM ℝ ℝ F)
  let c := 2*Real.pi
  let C₀ := ∫ u in Ioi (0:ℝ), (1+u)*|f u|
  have hC₀ : 0 ≤ C₀ := by
    unfold C₀
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    positivity
  obtain ⟨K,hK,hR⟩ := rvmError_log_bound
  refine ⟨K*C₀,mul_nonneg hK hC₀,?_⟩
  intro ε hε hε₁
  have hm := schwartz_testMoment f
  obtain ⟨hs,hCount⟩ := weighted_positive_zeta_zeros_count_identity f f.continuous.measurable
    hm hε hε₁
  have hF (u : ℝ) : positiveTail f u = F u := schwartz_tail_derivative F u
  rw [show (fun ρ : PositiveZetaZeroSet ↦ (zeroMult ρ.val : ℝ)*positiveTail f (ε*ρ.val.im)) =
      (fun ρ : PositiveZetaZeroSet ↦ (zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) from funext (fun ρ ↦ by rw [hF])]
      at hs
  refine ⟨hs, ?_⟩
  simp only [hF] at hCount
  obtain ⟨hE,hEB⟩ := rvm_scaled_error_integral_bound f hK hR hε hε₁
  have hA := (integrableOn_mul_testMoment f.continuous.measurable hm).const_mul (1/c*Real.log ε⁻¹)
  have hB := (logPrimitive_mul_integrable f (Real.log c)).const_mul (1/c)
  have hAB : IntegrableOn (fun u : ℝ ↦ (1/c)*Real.log ε⁻¹*(u*f u) +
      (1/c)*(logPrimitive (Real.log c) u*f u)) (Ioi (0:ℝ)) := hA.add hB
  have hEq :
      (∫ u in Ioi (0:ℝ), ε*(Ncount 0 (u/ε) : ℝ)*f u) =
        (1/c)*Real.log ε⁻¹*(∫ u in Ioi (0:ℝ), u*f u) +
          (1/c)*(∫ u in Ioi (0:ℝ), logPrimitive (Real.log c) u*f u) +
          (∫ u in Ioi (0:ℝ), ε*rvmError (u/ε)*f u) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hA hB,
      ← integral_add hAB hE]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    rw [rvm_scaled_count_split hε hu]
    unfold c
    ring
  rw [hCount,hEq,schwartz_derivative_moment F,schwartz_log_derivative_moment F]
  have hCancel :
      (1/c)*Real.log ε⁻¹*(∫ u in Ioi (0:ℝ), F u) +
        (1/c)*(∫ u in Ioi (0:ℝ), (Real.log u-Real.log c)*F u) +
        (∫ u in Ioi (0:ℝ), ε*rvmError (u/ε)*f u) -
        (1/(2*Real.pi))*Real.log ε⁻¹*(∫ u in Ioi (0:ℝ), F u) -
        (1/(2*Real.pi))*(∫ u in Ioi (0:ℝ), (Real.log u-Real.log (2*Real.pi))*F u) =
          ∫ u in Ioi (0:ℝ), ε*rvmError (u/ε)*f u := by
    unfold c
    ring
  rw [hCancel]
  exact hEB

end MasulloAudit

open MeasureTheory

theorem solution (F : SchwartzMap ℝ ℝ) :
    ∃ C ≥ (0:ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Summable (fun ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im} ↦
        (Zeta23.zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) ∧
      |ε*(∑' ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im},
          (Zeta23.zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) -
          (1/(2*Real.pi))*Real.log ε⁻¹*(∫ u in Set.Ioi (0:ℝ), F u) -
          (1/(2*Real.pi))*(∫ u in Set.Ioi (0:ℝ), (Real.log u-Real.log (2*Real.pi))*F u)| ≤
        C*ε*(1+Real.log ε⁻¹) := by
  exact MasulloAudit.weighted_positive_zeta_zeros_two_term_scaling_aux F
