-- Prove2me | solution 1 for IncompleteProc.English.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:51:44.094989+00:00
-- url     : https://prove2.me/submissions/e590fcc2-0dfb-4f56-9284-4a74254ce9b2

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

open MeasureTheory Set Filter Topology

namespace IncProcLemma1Aux

open IncompleteProc.English

variable {Ω : Type*} [MeasurableSpace Ω]

theorem cube_meas (E : Env Ω) : MeasurableSet E.cube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem ae_cube (E : Env Ω) : ∀ᵐ C ∂E.profileLaw, C ∈ E.cube := by
  unfold Env.profileLaw
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (cube_meas E))

theorem finite (E : Env Ω) (hS : E.Standing) : IsFiniteMeasure E.profileLaw := by
  obtain ⟨_, _, _, _, _, hfi, _, ⟨δ, hδ, hfδ⟩, _⟩ := hS
  set g : ℝ → ℝ := (Icc E.clo E.chi).indicator E.f with hgdef
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ Icc E.clo E.chi
    · rw [hgdef, indicator_of_mem hx]; exact le_trans hδ.le (hfδ x hx)
    · rw [hgdef, indicator_of_notMem hx]
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_Icc).mpr hfi
  have hprod : Integrable (fun C : Fin E.n → ℝ => ∏ i, g (C i))
      (Measure.pi fun _ => volume) := Integrable.fintype_prod (fun _ => hgi)
  constructor
  rw [Env.profileLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_indicator (cube_meas E)]
  refine lt_of_le_of_lt ?_ hprod.2
  rw [volume_pi]
  apply lintegral_mono
  intro C
  by_cases hC : C ∈ E.cube
  · rw [indicator_of_mem hC]
    have hgC : ∀ i, g (C i) = E.f (C i) := fun i => indicator_of_mem (hC i (mem_univ _)) _
    show _ ≤ ‖∏ i, g (C i)‖ₑ
    rw [Real.enorm_eq_ofReal (Finset.prod_nonneg fun i _ => hg0 (C i)),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 (C i))]
    simp_rw [hgC]
    exact le_rfl
  · rw [indicator_of_notMem hC]; exact bot_le

theorem update_mem (E : Env Ω) (i : Fin E.n) {C : Fin E.n → ℝ} (hC : C ∈ E.cube) {d : ℝ}
    (hd : d ∈ Icc E.clo E.chi) : Function.update C i d ∈ E.cube := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hd
  · rw [Function.update_of_ne hj]; exact hC j (mem_univ _)

theorem bounds1 (E : Env Ω) (M : Mech E.n Ω) (hM : M.Admissible E) (i : Fin E.n)
    {C : Fin E.n → ℝ} (hC : C ∈ E.cube) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) :
    0 ≤ M.x1 (Function.update C i d) i ∧ M.x1 (Function.update C i d) i ≤ 1 := by
  obtain ⟨h1, h2⟩ := hM.1 _ (update_mem E i hC hd)
  have hx1 : M.x1 (Function.update C i d) i ≤ ∑ j, M.x1 (Function.update C i d) j :=
    Finset.single_le_sum (fun j _ => h1 j) (Finset.mem_univ i)
  exact ⟨h1 i, hx1.trans h2⟩

theorem bounds2 (E : Env Ω) (M : Mech E.n Ω) (hM : M.Admissible E) (i : Fin E.n)
    {C : Fin E.n → ℝ} (hC : C ∈ E.cube) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) (ω : Ω) :
    0 ≤ M.x2 (Function.update C i d) ω i ∧ M.x2 (Function.update C i d) ω i ≤ 1 := by
  obtain ⟨h1, h2⟩ := hM.1 _ (update_mem E i hC hd)
  obtain ⟨h3, h4⟩ := hM.2.1 _ (update_mem E i hC hd) ω
  have hx2 : M.x2 (Function.update C i d) ω i ≤ ∑ j, M.x2 (Function.update C i d) ω j :=
    Finset.single_le_sum (fun j _ => h3 j) (Finset.mem_univ i)
  exact ⟨h3 i, (hx2.trans h4).trans h2⟩

theorem X1_bounds (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) :
    0 ≤ M.X1 E i d ∧ M.X1 E i d ≤ E.profileLaw.real univ := by
  have := finite E hS
  have hae : ∀ᵐ C ∂E.profileLaw,
      0 ≤ M.x1 (Function.update C i d) i ∧ M.x1 (Function.update C i d) i ≤ 1 := by
    filter_upwards [ae_cube E] with C hC using bounds1 E M hM i hC hd
  constructor
  · exact integral_nonneg_of_ae (hae.mono fun C h => h.1)
  · calc M.X1 E i d ≤ ∫ _C, (1 : ℝ) ∂E.profileLaw :=
          integral_mono_of_nonneg (hae.mono fun C h => h.1) (integrable_const 1)
            (hae.mono fun C h => h.2)
      _ = E.profileLaw.real univ := by simp

theorem X2_bounds (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) (ω : Ω) :
    0 ≤ M.X2 E i d ω ∧ M.X2 E i d ω ≤ E.profileLaw.real univ := by
  have := finite E hS
  have hae : ∀ᵐ C ∂E.profileLaw,
      0 ≤ M.x2 (Function.update C i d) ω i ∧ M.x2 (Function.update C i d) ω i ≤ 1 := by
    filter_upwards [ae_cube E] with C hC using bounds2 E M hM i hC hd ω
  constructor
  · exact integral_nonneg_of_ae (hae.mono fun C h => h.1)
  · calc M.X2 E i d ω ≤ ∫ _C, (1 : ℝ) ∂E.profileLaw :=
          integral_mono_of_nonneg (hae.mono fun C h => h.1) (integrable_const 1)
            (hae.mono fun C h => h.2)
      _ = E.profileLaw.real univ := by simp

theorem X2_meas (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) (d : ℝ) : StronglyMeasurable (fun ω => M.X2 E i d ω) := by
  have := finite E hS
  have hj : StronglyMeasurable
      (fun p : (Fin E.n → ℝ) × Ω => M.x2 (Function.update p.1 i d) p.2 i) :=
    ((hM.2.2.2.1 i).comp ((measurable_update_left.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable
  exact hj.integral_prod_left'

end IncProcLemma1Aux

open IncompleteProc.English IncProcLemma1Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) (M : Mech E.n Ω) (hM : M.Admissible E) (hIC : M.IsIC E) :
    (∀ i, ∀ c ∈ Set.Icc E.clo E.chi,
      M.U E i c c = M.U E i E.chi E.chi +
        ∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) ∧
    ((∀ i, 0 ≤ M.U E i E.chi E.chi) → M.IsIR E) := by
  have hS' := hS
  obtain ⟨_hn, hQ, _hR, hlt, _hfm, _hfi, _hf1, _hδ, hG, _hkmono, hkd, hkcb, hkm,
    hkcm, ⟨Mk, hMk⟩⟩ := hS'
  have := hG
  have := nonempty_of_isProbabilityMeasure E.G
  set m := E.profileLaw.real univ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hK0 : 0 ≤ E.K := le_trans (hkcb (Classical.arbitrary _) E.clo ⟨le_rfl, hlt.le⟩).1
    (hkcb (Classical.arbitrary _) E.clo ⟨le_rfl, hlt.le⟩).2
  have kLip : ∀ ω, ∀ s ∈ Icc E.clo E.chi, ∀ t ∈ Icc E.clo E.chi,
      |E.k t ω - E.k s ω| ≤ E.K * |t - s| := by
    intro ω s hs t ht
    have := (convex_Icc E.clo E.chi).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => E.k x ω) (hkd ω)
      (fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (hkcb ω x hx).1]; exact (hkcb ω x hx).2)
      hs ht
    simpa [Real.norm_eq_abs] using this
  have hMk0 : 0 ≤ Mk := le_trans (abs_nonneg _) (hMk E.clo ⟨le_rfl, hlt.le⟩ (Classical.arbitrary Ω))
  have intA : ∀ i, ∀ c ∈ Icc E.clo E.chi, ∀ d ∈ Icc E.clo E.chi,
      Integrable (fun ω => E.Q * E.k c ω * M.X2 E i d ω) E.G := by
    intro i c hc d hd
    refine Integrable.of_bound (((stronglyMeasurable_const.mul (hkm c).stronglyMeasurable).mul
      (X2_meas E hS M hM i d)).aestronglyMeasurable) (E.Q * Mk * m) (ae_of_all _ fun ω => ?_)
    obtain ⟨h0, h1⟩ := X2_bounds E hS M hM i hd ω
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg h0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hMk c hc ω) hQ.le) h1 h0 (by positivity)
  have intB : ∀ i, ∀ c ∈ Icc E.clo E.chi, ∀ d ∈ Icc E.clo E.chi,
      Integrable (fun ω => E.Q * E.kc c ω * M.X2 E i d ω) E.G := by
    intro i c hc d hd
    refine Integrable.of_bound (((stronglyMeasurable_const.mul (hkcm c).stronglyMeasurable).mul
      (X2_meas E hS M hM i d)).aestronglyMeasurable) (E.Q * E.K * m) (ae_of_all _ fun ω => ?_)
    obtain ⟨h0, h1⟩ := X2_bounds E hS M hM i hd ω
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg h0,
      abs_of_nonneg (hkcb ω c hc).1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hkcb ω c hc).2 hQ.le) h1 h0 (by positivity)
  have Adiff : ∀ i, ∀ s ∈ Icc E.clo E.chi, ∀ t ∈ Icc E.clo E.chi,
      |(∫ ω, E.Q * E.k t ω * M.X2 E i s ω ∂E.G) - ∫ ω, E.Q * E.k s ω * M.X2 E i s ω ∂E.G|
        ≤ E.Q * E.K * m * |t - s| := by
    intro i s hs t ht
    rw [← integral_sub (intA i t ht s hs) (intA i s hs s hs)]
    have hb : ∀ ω, ‖E.Q * E.k t ω * M.X2 E i s ω - E.Q * E.k s ω * M.X2 E i s ω‖
        ≤ E.Q * E.K * m * |t - s| := by
      intro ω
      obtain ⟨h0, h1⟩ := X2_bounds E hS M hM i hs ω
      rw [Real.norm_eq_abs, show E.Q * E.k t ω * M.X2 E i s ω - E.Q * E.k s ω * M.X2 E i s ω
        = E.Q * (E.k t ω - E.k s ω) * M.X2 E i s ω by ring, abs_mul, abs_mul, abs_of_pos hQ,
        abs_of_nonneg h0]
      calc E.Q * |E.k t ω - E.k s ω| * M.X2 E i s ω ≤ E.Q * (E.K * |t - s|) * m :=
            mul_le_mul (mul_le_mul_of_nonneg_left (kLip ω s hs t ht) hQ.le) h1 h0
              (by positivity)
        _ = E.Q * E.K * m * |t - s| := by ring
    have := norm_integral_le_of_norm_le_const (μ := E.G) (ae_of_all _ hb)
    simpa [Real.norm_eq_abs] using this
  have key : ∀ i, ∀ s ∈ Icc E.clo E.chi, ∀ t ∈ Icc E.clo E.chi,
      M.U E i s s - M.X1 E i s * (t - s) - ((∫ ω, E.Q * E.k t ω * M.X2 E i s ω ∂E.G) -
        ∫ ω, E.Q * E.k s ω * M.X2 E i s ω ∂E.G) ≤ M.U E i t t := by
    intro i s hs t ht
    rw [show M.U E i s s - M.X1 E i s * (t - s) - ((∫ ω, E.Q * E.k t ω * M.X2 E i s ω ∂E.G) -
        ∫ ω, E.Q * E.k s ω * M.X2 E i s ω ∂E.G) = M.U E i t s by unfold Mech.U; ring]
    exact hIC i t ht s hs
  set L := m + E.Q * E.K * m with hLdef
  have hL0 : 0 ≤ L := by positivity
  have ulip : ∀ i, ∀ s ∈ Icc E.clo E.chi, ∀ t ∈ Icc E.clo E.chi,
      |M.U E i t t - M.U E i s s| ≤ L * |t - s| := by
    intro i s hs t ht
    have k1 := key i s hs t ht
    have k2 := key i t ht s hs
    have a1 := abs_le.mp (Adiff i s hs t ht)
    have a2 := abs_le.mp (Adiff i t ht s hs)
    obtain ⟨x0, x1⟩ := X1_bounds E hS M hM i hs
    obtain ⟨y0, y1⟩ := X1_bounds E hS M hM i ht
    have b1 : |M.X1 E i s * (t - s)| ≤ m * |t - s| := by
      rw [abs_mul, abs_of_nonneg x0]; exact mul_le_mul_of_nonneg_right x1 (abs_nonneg _)
    have b2 : |M.X1 E i t * (s - t)| ≤ m * |t - s| := by
      rw [abs_mul, abs_of_nonneg y0, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right y1 (abs_nonneg _)
    have b1' := abs_le.mp b1
    have b2' := abs_le.mp b2
    rw [abs_sub_comm s t] at a2
    have hL : L * |t - s| = m * |t - s| + E.Q * E.K * m * |t - s| := by rw [hLdef]; ring
    rw [abs_le, hL]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, b1'.1, b1'.2, b2'.1, b2'.2]
  have hderA : ∀ i, ∀ s ∈ Ioo E.clo E.chi,
      HasDerivAt (fun t => ∫ ω, E.Q * E.k t ω * M.X2 E i s ω ∂E.G)
        (∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G) s := by
    intro i s hs
    have hsI : s ∈ Icc E.clo E.chi := Ioo_subset_Icc_self hs
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := E.G)
      (Ioo_mem_nhds hs.1 hs.2)
      (F := fun t ω => E.Q * E.k t ω * M.X2 E i s ω)
      (F' := fun t ω => E.Q * E.kc t ω * M.X2 E i s ω)
      (bound := fun _ => E.Q * E.K * m) ?_ (intA i s hsI s hsI)
      (intB i s hsI s hsI).aestronglyMeasurable ?_ (integrable_const _) ?_).2
    · exact Eventually.of_forall fun t => ((stronglyMeasurable_const.mul
        (hkm t).stronglyMeasurable).mul (X2_meas E hS M hM i s)).aestronglyMeasurable
    · refine ae_of_all _ fun ω t ht => ?_
      have htI := Ioo_subset_Icc_self ht
      obtain ⟨h0, h1⟩ := X2_bounds E hS M hM i hsI ω
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg h0,
        abs_of_nonneg (hkcb ω t htI).1]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hkcb ω t htI).2 hQ.le) h1 h0 (by positivity)
    · refine ae_of_all _ fun ω t ht => ?_
      have hk : HasDerivAt (fun x => E.k x ω) (E.kc t ω) t :=
        (hkd ω t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      exact (hk.const_mul E.Q).mul_const (M.X2 E i s ω)
  have hderu : ∀ i, ∀ s ∈ Ioo E.clo E.chi, DifferentiableAt ℝ (fun t => M.U E i t t) s →
      deriv (fun t => M.U E i t t) s =
        -(M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G) := by
    intro i s hs hdiff
    have hsI := Ioo_subset_Icc_self hs
    have h1 : HasDerivAt (fun t => M.X1 E i s * (t - s)) (M.X1 E i s) s := by
      simpa using ((hasDerivAt_id s).sub_const s).const_mul (M.X1 E i s)
    have h2 := (hderA i s hs).sub_const (∫ ω, E.Q * E.k s ω * M.X2 E i s ω ∂E.G)
    have hv := ((hasDerivAt_const s (M.U E i s s)).sub h1).sub h2
    have hmin : IsLocalMin (fun t => M.U E i t t - (M.U E i s s - M.X1 E i s * (t - s) -
        ((∫ ω, E.Q * E.k t ω * M.X2 E i s ω ∂E.G) -
          ∫ ω, E.Q * E.k s ω * M.X2 E i s ω ∂E.G))) s := by
      refine Filter.mem_of_superset (Icc_mem_nhds hs.1 hs.2) fun t ht => ?_
      have := key i s hsI t ht
      simp only [Set.mem_setOf_eq, sub_self, mul_zero, sub_zero]
      linarith
    have := hmin.hasDerivAt_eq_zero (hdiff.hasDerivAt.sub hv)
    linarith
  have env : ∀ i, ∀ c ∈ Set.Icc E.clo E.chi,
      M.U E i c c = M.U E i E.chi E.chi +
        ∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G) := by
    intro i c hc
    have hLipOn : LipschitzOnWith (Real.toNNReal L) (fun t => M.U E i t t)
        (Icc E.clo E.chi) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro t ht s hs
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]
      exact ulip i s hs t ht
    have hsub : uIcc c E.chi ⊆ Icc E.clo E.chi := by
      rw [uIcc_of_le hc.2]; exact Icc_subset_Icc hc.1 le_rfl
    have hac : AbsolutelyContinuousOnInterval (fun t => M.U E i t t) c E.chi :=
      (hLipOn.mono hsub).absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have hcongr : ∫ s in c..E.chi, deriv (fun t => M.U E i t t) s =
        ∫ s in c..E.chi, -(M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G) := by
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ x : ℝ, x ≠ E.chi := by rw [ae_iff]; simp
      filter_upwards [hac.ae_differentiableAt, hne] with x hx hxne hxI
      rw [uIoc_of_le hc.2] at hxI
      have hxIoo : x ∈ Ioo E.clo E.chi :=
        ⟨lt_of_le_of_lt hc.1 hxI.1, lt_of_le_of_ne hxI.2 hxne⟩
      exact hderu i x hxIoo (hx (by rw [uIcc_of_le hc.2]; exact Ioc_subset_Icc_self hxI))
    rw [hcongr, intervalIntegral.integral_neg] at hftc
    linarith
  refine ⟨env, ?_⟩
  intro hchi i c hc
  rw [env i c hc]
  have : 0 ≤ ∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G) := by
    apply intervalIntegral.integral_nonneg hc.2
    intro s hs
    have hsI : s ∈ Icc E.clo E.chi := ⟨hc.1.trans hs.1, hs.2⟩
    have h1 := (X1_bounds E hS M hM i hsI).1
    have h2 : 0 ≤ ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G :=
      integral_nonneg fun ω => mul_nonneg (mul_nonneg hQ.le (hkcb ω s hsI).1)
        (X2_bounds E hS M hM i hsI ω).1
    linarith
  linarith [hchi i]
