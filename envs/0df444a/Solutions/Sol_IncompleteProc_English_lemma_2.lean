-- Prove2me | solution 1 for IncompleteProc.English.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:56:45.060195+00:00
-- url     : https://prove2.me/submissions/12183135-45c9-453b-8e49-748b3d7524e2

import Mathlib
import Definitions.Def_IncompleteProc_English_Model

open MeasureTheory Set Filter Topology

namespace IncProcLemma2Aux

open IncompleteProc.English

variable {Ω : Type*} [MeasurableSpace Ω]

theorem cStar2_bdd (E : Env Ω) (hlt : E.clo < E.chi) (ω : Ω) :
    BddAbove (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}) := by
  refine ⟨E.chi, ?_⟩
  rintro y (rfl | ⟨hy, _⟩)
  · exact hlt.le
  · exact hy.2

theorem cStar2_mem (E : Env Ω) (hlt : E.clo < E.chi) (ω : Ω) :
    E.cStar2 ω ∈ Icc E.clo E.chi := by
  refine ⟨le_csSup (cStar2_bdd E hlt ω) (mem_insert _ _), csSup_le ⟨_, mem_insert _ _⟩ ?_⟩
  rintro y (rfl | ⟨hy, _⟩)
  · exact hlt.le
  · exact hy.2

theorem cStar2_meas (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    Measurable E.cStar2 := by
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, _, _, hkm, hkcm, _⟩ := hS
  have hPsi : ∀ q, Measurable (fun ω => E.Psi2 q ω) := by
    intro q; unfold Env.Psi2; exact (hkm q).add (measurable_const.mul (hkcm q))
  apply measurable_of_Ici
  intro x
  by_cases hx1 : x ≤ E.clo
  · convert MeasurableSet.univ
    ext ω
    simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
    exact hx1.trans (cStar2_mem E hlt ω).1
  by_cases hx2 : E.chi < x
  · convert MeasurableSet.empty
    ext ω
    simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_le]
    exact (cStar2_mem E hlt ω).2.trans_lt hx2
  push Not at hx1 hx2
  have hset : E.cStar2 ⁻¹' Ici x =
      ⋂ q : ℚ, {ω | (E.clo < (q : ℝ) ∧ (q : ℝ) < x) → E.Psi2 q ω ≤ E.R} := by
    ext ω
    simp only [mem_preimage, mem_Ici, mem_iInter, mem_setOf_eq]
    have hc2 : E.cStar2 ω = sSup (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}) := rfl
    constructor
    · rintro hxc q ⟨hq1, hq2⟩
      obtain ⟨y, hyS, hqy⟩ := exists_lt_of_lt_csSup (⟨_, mem_insert _ _⟩ :
        (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}).Nonempty)
        (hc2 ▸ lt_of_lt_of_le hq2 hxc)
      rcases hyS with rfl | ⟨hyI, hyR⟩
      · exact absurd hq1 (not_lt.mpr hqy.le)
      · exact le_trans (hA.2 ω ⟨hq1.le, hqy.le.trans hyI.2⟩ hyI hqy.le) hyR
    · intro h
      by_contra hcon
      push Not at hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hx1 hcon)
      have hq := h q ⟨lt_of_le_of_lt (le_max_left _ _) hq1, hq2⟩
      have : (q : ℝ) ≤ E.cStar2 ω := le_csSup (cStar2_bdd E hlt ω)
        (Or.inr ⟨⟨(le_max_left _ _).trans hq1.le, hq2.le.trans hx2⟩, hq⟩)
      exact absurd (lt_of_le_of_lt (le_max_right _ _) hq1) (not_lt.mpr this)
  rw [hset]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : E.clo < (q : ℝ) ∧ (q : ℝ) < x
  · convert measurableSet_le (hPsi q) (measurable_const (a := E.R)) using 1
    ext ω; simp [hq]
  · convert MeasurableSet.univ using 1
    ext ω; simp [hq]

theorem kc2_meas (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    Measurable (fun ω => E.k (E.cStar2 ω) ω) := by
  have hS' := hS
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, hkd, _, hkm, _, _⟩ := hS'
  set cl : ℝ → ℝ := fun s => max E.clo (min s E.chi) with hcl
  have hcl_mem : ∀ s, cl s ∈ Icc E.clo E.chi :=
    fun s => ⟨le_max_left _ _, max_le hlt.le (min_le_right _ _)⟩
  have hcl_id : ∀ s ∈ Icc E.clo E.chi, cl s = s := fun s hs => by
    simp only [hcl, min_eq_left hs.2, max_eq_right hs.1]
  have hcont : ∀ ω, Continuous fun s => E.k (cl s) ω := by
    intro ω
    have hk : ContinuousOn (fun s => E.k s ω) (Icc E.clo E.chi) :=
      fun s hs => (hkd ω s hs).continuousWithinAt
    exact hk.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hcl_mem
  have hj : Measurable (Function.uncurry fun s ω => E.k (cl s) ω) :=
    measurable_uncurry_of_continuous_of_measurable hcont (fun s => hkm (cl s))
  have hfun : (fun ω => E.k (E.cStar2 ω) ω) =
      fun ω => Function.uncurry (fun s ω => E.k (cl s) ω) (E.cStar2 ω, ω) := by
    funext ω
    simp only [Function.uncurry_apply_pair, hcl_id _ (cStar2_mem E hlt ω)]
  rw [hfun]
  exact hj.comp ((cStar2_meas E hS hA).prodMk measurable_id)

end IncProcLemma2Aux

open IncompleteProc.English IncProcLemma2Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    ∀ c ∈ Set.Icc E.clo E.chi, E.Phi c = E.Phi E.clo + ∫ s in E.clo..c, E.phi s := by
  intro c hc
  have hS' := hS
  obtain ⟨_hn, hQ, _hR, hlt, _hfm, _hfi, _hf1, _hδ, hG, hkmono, hkd, hkcb, hkm,
    hkcm, ⟨Mk, hMk⟩⟩ := hS'
  have := hG
  have := nonempty_of_isProbabilityMeasure E.G
  have hK0 : 0 ≤ E.K := le_trans (hkcb (Classical.arbitrary _) E.clo ⟨le_rfl, hlt.le⟩).1
    (hkcb (Classical.arbitrary _) E.clo ⟨le_rfl, hlt.le⟩).2
  have hMk0 : 0 ≤ Mk := le_trans (abs_nonneg _) (hMk E.clo ⟨le_rfl, hlt.le⟩ (Classical.arbitrary Ω))
  set a : Ω → ℝ := fun ω => E.k (E.cStar2 ω) ω with hadef
  have ha_meas : Measurable a := kc2_meas E hS hA
  have ha_bd : ∀ ω, |a ω| ≤ Mk := fun ω => hMk _ (cStar2_mem E hlt ω) ω
  set F : ℝ → Ω → ℝ := fun x ω => E.Q * max 0 (a ω - E.k x ω) with hFdef
  have hPhi : ∀ x, E.Phi x = ∫ ω, F x ω ∂E.G := fun x => rfl
  have kLip : ∀ ω, ∀ s ∈ Icc E.clo E.chi, ∀ t ∈ Icc E.clo E.chi,
      |E.k t ω - E.k s ω| ≤ E.K * |t - s| := by
    intro ω s hs t ht
    have := (convex_Icc E.clo E.chi).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => E.k x ω) (hkd ω)
      (fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (hkcb ω x hx).1]; exact (hkcb ω x hx).2)
      hs ht
    simpa [Real.norm_eq_abs] using this
  have hFmeas : ∀ x, Measurable (F x) := fun x =>
    measurable_const.mul (measurable_const.max (ha_meas.sub (hkm x)))
  have hFint : ∀ x ∈ Icc E.clo E.chi, Integrable (F x) E.G := by
    intro x hx
    refine Integrable.of_bound (hFmeas x).aestronglyMeasurable (E.Q * (Mk + Mk))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hQ.le (le_max_left _ _))]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    apply max_le (by linarith)
    linarith [abs_le.mp (ha_bd ω), abs_le.mp (hMk x hx ω)]
  have FLip : ∀ ω, ∀ x ∈ Icc E.clo E.chi, ∀ y ∈ Icc E.clo E.chi,
      |F y ω - F x ω| ≤ E.Q * E.K * |y - x| := by
    intro ω x hx y hy
    simp only [hFdef]
    rw [← mul_sub, abs_mul, abs_of_pos hQ, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    calc |max 0 (a ω - E.k y ω) - max 0 (a ω - E.k x ω)|
        ≤ |(a ω - E.k y ω) - (a ω - E.k x ω)| := by
          rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
      _ = |E.k x ω - E.k y ω| := by ring_nf
      _ ≤ E.K * |x - y| := kLip ω y hy x hx
      _ = E.K * |y - x| := by rw [abs_sub_comm]
  have PhiLip : ∀ x ∈ Icc E.clo E.chi, ∀ y ∈ Icc E.clo E.chi,
      |E.Phi y - E.Phi x| ≤ E.Q * E.K * |y - x| := by
    intro x hx y hy
    rw [hPhi, hPhi, ← integral_sub (hFint y hy) (hFint x hx)]
    have := norm_integral_le_of_norm_le_const (μ := E.G)
      (ae_of_all _ fun ω => (show ‖F y ω - F x ω‖ ≤ E.Q * E.K * |y - x| by
        rw [Real.norm_eq_abs]; exact FLip ω x hx y hy))
    simpa [Real.norm_eq_abs] using this
  -- derivative of Φ at points that are not atoms of `c⋆₂`
  have hderiv : ∀ x ∈ Ioo E.clo E.chi, E.G {ω | E.cStar2 ω = x} = 0 →
      HasDerivAt E.Phi (E.phi x) x := by
    intro x hx hx0
    have hxI : x ∈ Icc E.clo E.chi := Ioo_subset_Icc_self hx
    set g : Ω → ℝ := fun ω => if E.k x ω ≤ a ω then -(E.Q * E.kc x ω) else 0 with hgdef
    have hgmeas : Measurable g :=
      Measurable.ite (measurableSet_le (hkm x) ha_meas) (measurable_const.mul (hkcm x)).neg
        measurable_const
    have hres := hasDerivAt_integral_of_dominated_loc_of_lip (μ := E.G) (F := F) (F' := g)
      (bound := fun _ => E.Q * E.K) (Ioo_mem_nhds hx.1 hx.2)
      (Eventually.of_forall fun y => (hFmeas y).aestronglyMeasurable) (hFint x hxI)
      hgmeas.aestronglyMeasurable ?_ (integrable_const _) ?_
    · have hint : ∫ ω, g ω ∂E.G = E.phi x := by
        have : g = (E.contSet x).indicator (fun ω => -(E.Q * E.kc x ω)) := by
          funext ω
          simp only [hgdef, Set.indicator, Env.contSet, mem_setOf_eq, hadef]
        rw [this, integral_indicator (show MeasurableSet (E.contSet x) from
          measurableSet_le (hkm x) ha_meas), integral_neg]
        rfl
      rw [← hint]
      exact hres.2
    · refine ae_of_all _ fun ω => ?_
      apply LipschitzOnWith.of_dist_le_mul
      intro y hy z hz
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
        abs_of_nonneg (show (0:ℝ) ≤ E.Q * E.K from mul_nonneg hQ.le hK0)]
      exact FLip ω z (Ioo_subset_Icc_self hz) y (Ioo_subset_Icc_self hy)
    · have hae : ∀ᵐ ω ∂E.G, E.cStar2 ω ≠ x := by
        rw [ae_iff]; simpa using hx0
      filter_upwards [hae] with ω hω
      have hk : HasDerivAt (fun y => E.k y ω) (E.kc x ω) x :=
        (hkd ω x hxI).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      have hc2I := cStar2_mem E hlt ω
      rcases lt_or_gt_of_ne hω with hlt2 | hgt2
      · -- c⋆₂ < x : k x > a, F vanishes near x
        have hka : a ω < E.k x ω := hkmono ω hc2I hxI hlt2
        have hev : (fun y => F y ω) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [hk.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hka)] with y hy
          simp only [hFdef, mem_preimage, mem_Ioi] at hy ⊢
          rw [max_eq_left (by linarith), mul_zero]
        have hg0 : g ω = 0 := by
          simp only [hgdef, if_neg (not_le.mpr hka)]
        rw [hg0]
        exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
      · -- x < c⋆₂ : k x < a, F = Q (a - k) near x
        have hka : E.k x ω < a ω := hkmono ω hxI hc2I hgt2
        have hev : (fun y => F y ω) =ᶠ[𝓝 x] fun y => E.Q * (a ω - E.k y ω) := by
          filter_upwards [hk.continuousAt.preimage_mem_nhds (Iio_mem_nhds hka)] with y hy
          simp only [hFdef, mem_preimage, mem_Iio] at hy ⊢
          rw [max_eq_right (by linarith)]
        have hg0 : g ω = E.Q * -E.kc x ω := by
          simp only [hgdef, if_pos hka.le]; ring
        rw [hg0]
        exact ((hk.const_sub (a ω)).const_mul E.Q).congr_of_eventuallyEq hev
  -- FTC for the Lipschitz function Φ
  have hLipOn : LipschitzOnWith (Real.toNNReal (E.Q * E.K)) E.Phi (Icc E.clo E.chi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hQ.le hK0)]
    exact PhiLip z hz y hy
  have hsub : uIcc E.clo c ⊆ Icc E.clo E.chi := by
    rw [uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2
  have hac : AbsolutelyContinuousOnInterval E.Phi E.clo c :=
    (hLipOn.mono hsub).absolutelyContinuousOnInterval
  have hftc := hac.integral_deriv_eq_sub
  have hcongr : ∫ s in E.clo..c, deriv E.Phi s = ∫ s in E.clo..c, E.phi s := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x : ℝ, x ≠ E.chi := by rw [ae_iff]; simp
    have hatoms := (Measure.countable_meas_level_set_pos (μ := E.G)
      (cStar2_meas E hS hA)).ae_notMem volume
    filter_upwards [hne, hatoms] with x hxne hxat hxI
    rw [uIoc_of_le hc.1] at hxI
    have hxIoo : x ∈ Ioo E.clo E.chi :=
      ⟨hxI.1, lt_of_le_of_ne (hxI.2.trans hc.2) hxne⟩
    have hx0 : E.G {ω | E.cStar2 ω = x} = 0 := by
      simp only [mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hxat
      exact hxat
    exact (hderiv x hxIoo hx0).deriv
  rw [hcongr] at hftc
  linarith
