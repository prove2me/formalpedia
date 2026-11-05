-- Prove2me | solution 1 for MFGLiquidation.Penalized.lemma_4_2_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:10:05.132138+00:00
-- url     : https://prove2.me/submissions/4a2cc63c-6be8-47fc-801a-09c4b671029f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
import Theorems.Thm_MFGLiquidation_Penalized_lemma_A_3
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGL2Aux
open Set intervalIntegral
open scoped Interval


lemma gb_intervalIntegrable (gb : ℝ → ℝ) (K : ℝ) (hgm : Measurable gb)
    (hpos : ∀ x, 0 < gb x) (hK : ∀ x, gb x ≤ K) (a b : ℝ) :
    IntervalIntegrable gb volume a b := by
  refine (intervalIntegrable_const (c := K)).mono_fun hgm.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have h1 := hpos x
  have h2 := hK x
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos h1, abs_of_pos (h1.trans_le h2)]
  exact h2

lemma log_sub_le (a b m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have k1 : Real.log a - Real.log b ≤ |a - b| / m := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have e : a / b - 1 = (a - b) / b := by field_simp
    calc Real.log (a / b) ≤ (a - b) / b := by linarith
      _ ≤ |a - b| / b := by gcongr; exact le_abs_self _
      _ ≤ |a - b| / m := by gcongr
  have k2 : Real.log b - Real.log a ≤ |a - b| / m := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have e : b / a - 1 = (b - a) / a := by field_simp
    calc Real.log (b / a) ≤ (b - a) / a := by linarith
      _ ≤ |a - b| / a := by gcongr; rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ |a - b| / m := by gcongr
  rw [abs_sub_le_iff]
  exact ⟨k1, k2⟩

/-- FTC for `log` of the tail integral `c(x) = ∫_x^T g`. -/
lemma key_ftc (gb : ℝ → ℝ) (T K : ℝ) (hgm : Measurable gb) (hpos : ∀ x, 0 < gb x)
    (hK : ∀ x, gb x ≤ K) (r s : ℝ) (hrs : r ≤ s) (hsT : s < T) :
    ∫ u in Icc r s, gb u / (∫ y in u..T, gb y) =
      Real.log (∫ y in r..T, gb y) - Real.log (∫ y in s..T, gb y) := by
  have hII := gb_intervalIntegrable gb K hgm hpos hK
  set c : ℝ → ℝ := fun x => ∫ y in x..T, gb y with hc
  -- c s > 0
  have hcs : 0 < c s := intervalIntegral_pos_of_pos_on (hII s T) (fun x _ => hpos x) hsT
  -- c x ≥ c s for x ≤ s
  have hmono : ∀ x, x ≤ s → c s ≤ c x := by
    intro x hx
    have : c x = (∫ y in x..s, gb y) + c s := by
      simp only [hc]
      rw [integral_add_adjacent_intervals (hII x s) (hII s T)]
    rw [this]
    have : 0 ≤ ∫ y in x..s, gb y := integral_nonneg hx (fun y _ => (hpos y).le)
    linarith
  -- c is Lipschitz
  have hK0 : 0 ≤ K := (hpos 0).le.trans (hK 0)
  have hclip : ∀ x y, |c x - c y| ≤ K * |x - y| := by
    intro x y
    have : c x - c y = ∫ t in x..y, gb t := by
      simp only [hc]
      rw [integral_interval_sub_interval_comm' (hII x T) (hII y T) (hII x y)]
      simp [integral_symm y x]
    rw [this]
    have := norm_integral_le_of_norm_le_const (a := x) (b := y) (C := K) (f := gb)
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_of_pos (hpos t)]; exact hK t)
    rw [Real.norm_eq_abs] at this
    rw [abs_sub_comm x y]; exact this
  set L : ℝ → ℝ := fun x => Real.log (c x) with hL
  have hLlip : LipschitzOnWith (Real.toNNReal (K / c s)) L (uIcc r s) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [uIcc_of_le hrs] at hx hy
    simp only [Real.dist_eq, hL]
    rw [Real.coe_toNNReal _ (div_nonneg hK0 hcs.le)]
    calc |Real.log (c x) - Real.log (c y)| ≤ |c x - c y| / c s :=
          log_sub_le _ _ _ hcs (hmono x hx.2) (hmono y hy.2)
      _ ≤ K * |x - y| / c s := by gcongr; exact hclip x y
      _ = K / c s * |x - y| := by ring
  have hAC := hLlip.absolutelyContinuousOnInterval
  have hFTC := hAC.integral_deriv_eq_sub
  -- derivative a.e.
  have hder := (hII r T).ae_hasDerivAt_integral
  have hderL : ∀ᵐ x, x ∈ Set.uIoc r s → deriv L x = -(gb x / c x) := by
    filter_upwards [hder] with x hx hxI
    have hx' : x ∈ Ioc r s := by rwa [uIoc_of_le hrs] at hxI
    have hxu : x ∈ uIcc r T := by
      rw [uIcc_of_le (hrs.trans hsT.le)]; exact ⟨hx'.1.le, hx'.2.trans hsT.le⟩
    have hTu : T ∈ uIcc r T := by
      rw [uIcc_of_le (hrs.trans hsT.le)]; exact ⟨hrs.trans hsT.le, le_rfl⟩
    have h1 := hx hxu T hTu
    have hcx : c = fun x => -(∫ y in T..x, gb y) := by
      funext z; simp only [hc]; rw [integral_symm]
    have h2 : HasDerivAt c (-gb x) x := by rw [hcx]; exact h1.neg
    have hcx0 : c x ≠ 0 := (hcs.trans_le (hmono x hx'.2)).ne'
    have h3 := h2.log hcx0
    rw [h3.deriv]; ring
  rw [integral_congr_ae hderL] at hFTC
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hrs] at hFTC
  rw [integral_Icc_eq_integral_Ioc]
  simp only [hL] at hFTC
  linarith


lemma enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

end MFGL2Aux

open MFGLiquidation.Penalized Set in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hRic : IsSingularRiccati hD A ZA)
    (hdet : ∀ (t : ℝ≥0) (ω ω' : Ω), D.η t ω = D.η t ω') :
    Assumption41 hD A := by
  classical
  obtain ⟨ω0⟩ : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := IsProbabilityMeasure.measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨cL, hcL0, hcL⟩ := hA.low_η
  obtain ⟨cH, hcH⟩ := hA.bdd_η
  set T : ℝ := (D.T : ℝ) with hTdef
  have hT : 0 < T := hD.T_pos
  -- the deterministic coefficient
  set e : ℝ → ℝ := fun x => D.η (min x.toNNReal D.T) ω0 with he
  have hem : Measurable e := by
    have hηprog := hA.prog_η D.T
    have hmap : @Measurable ℝ (Set.Iic D.T × Ω) _
        (@Prod.instMeasurableSpace _ _ _ (filtF hD D.T))
        (fun x : ℝ => ((⟨min x.toNNReal D.T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic D.T), ω0)) :=
      @Measurable.prodMk _ _ _ _ _ (filtF hD D.T) _ _
        (Measurable.subtype_mk (measurable_real_toNNReal.min measurable_const))
        (@measurable_const _ _ (filtF hD D.T) _ ω0)
    exact hηprog.measurable.comp hmap
  set gb : ℝ → ℝ := fun x => 1 / (2 * max cL (e x)) with hgb
  have hgbm : Measurable gb := by
    exact (measurable_const.mul (measurable_const.max hem)).const_div 1
  have hgbpos : ∀ x, 0 < gb x := fun x => by
    simp only [hgb]; have := le_max_left cL (e x); positivity
  have hgbK : ∀ x, gb x ≤ 1 / (2 * cL) := fun x => by
    simp only [hgb]
    apply one_div_le_one_div_of_le (by positivity)
    have := le_max_left cL (e x); linarith
  -- a.e. bounds on η
  have hηae : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) T)),
      cL ≤ D.η x.toNNReal ω0 ∧ D.η x.toNNReal ω0 ≤ cH := by
    have h := hcL.and hcH
    simp only [dtP] at h
    have h2 := Measure.ae_ae_of_ae_prod h
    filter_upwards [h2] with x hx
    obtain ⟨ω, h1, h3⟩ := hx.exists
    rw [hdet _ ω ω0] at h1 h3
    exact ⟨h1, h3.2⟩
  have hminT : ∀ x : ℝ, x ≤ T → min x.toNNReal D.T = x.toNNReal := fun x hx =>
    min_eq_left (Real.toNNReal_le_iff_le_coe.2 hx)
  have hgb_ae : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) T)),
      1 / (2 * cH) ≤ gb x ∧ gb x = 1 / (2 * D.η x.toNNReal ω0) := by
    filter_upwards [hηae, ae_restrict_mem measurableSet_Icc] with x hx hxI
    have hex : e x = D.η x.toNNReal ω0 := by simp only [he, hminT x hxI.2]
    have hmx : max cL (e x) = D.η x.toNNReal ω0 := by rw [hex]; exact max_eq_right hx.1
    refine ⟨?_, by simp only [hgb, hmx]⟩
    simp only [hgb, hmx]
    apply one_div_le_one_div_of_le (by linarith) (by linarith [hx.2])
  have hvolne : volume (Icc (0 : ℝ) T) ≠ 0 := by
    rw [Real.volume_Icc]; simp [hT]
  have : (ae (volume.restrict (Icc (0 : ℝ) T))).NeBot := ae_restrict_neBot.2 hvolne
  have hcLH : cL ≤ cH := by
    obtain ⟨x, hx⟩ := hηae.exists
    linarith [hx.1, hx.2]
  have hcH0 : 0 < cH := hcL0.trans_le hcLH
  have hII := MFGL2Aux.gb_intervalIntegrable gb (1 / (2 * cL)) hgbm hgbpos hgbK
  set c : ℝ → ℝ := fun x => ∫ y in x..T, gb y with hc
  have hc_cont : Continuous c := by
    have h1 := intervalIntegral.continuous_primitive hII T
    have : c = fun x => -(∫ y in T..x, gb y) := by
      funext z; simp only [hc]; rw [intervalIntegral.integral_symm]
    rw [this]; exact h1.neg
  have hc_low : ∀ t, 0 ≤ t → t ≤ T → (T - t) * (1 / (2 * cH)) ≤ c t := by
    intro t h0 htT
    have h1 : ∫ y in t..T, (1 / (2 * cH)) ≤ ∫ y in t..T, gb y := by
      apply intervalIntegral.integral_mono_ae_restrict htT intervalIntegrable_const (hII t T)
      have := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc h0 le_rfl) hgb_ae
      filter_upwards [this] with x hx using hx.1
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1; exact h1
  have hc_up : ∀ t, t ≤ T → c t ≤ (T - t) * (1 / (2 * cL)) := by
    intro t htT
    have h1 : ∫ y in t..T, gb y ≤ ∫ y in t..T, (1 / (2 * cL)) :=
      intervalIntegral.integral_mono_on htT (hII t T) intervalIntegrable_const
        (fun x _ => hgbK x)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1; exact h1
  -- the conditional expectation term of Lemma A.3 is deterministic
  have hcond : ∀ t : ℝ≥0, t ≤ D.T →
      (fun ω' => ∫ s in Set.Icc (t : ℝ) D.T, 1 / (2 * D.η s.toNNReal ω')) = fun _ => c t := by
    intro t ht
    funext ω'
    simp only [hdet _ ω' ω0]
    have hsub : Icc (t : ℝ) T ⊆ Icc 0 T := Icc_subset_Icc t.2 le_rfl
    have h1 : ∫ s in Set.Icc (t : ℝ) T, 1 / (2 * D.η s.toNNReal ω0) =
        ∫ s in Set.Icc (t : ℝ) T, gb s := by
      apply setIntegral_congr_ae measurableSet_Icc
      have := (ae_restrict_iff' measurableSet_Icc).1 hgb_ae
      filter_upwards [this] with x hx hxI
      exact ((hx (hsub hxI)).2).symm
    refine h1.trans ?_
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
    exact_mod_cast ht
  -- lower bound for `A` from Lemma A.3
  have hAlow : ∀ t : ℝ≥0, t < D.T → ∀ᵐ ω ∂P, 1 / c t ≤ A t ω := by
    obtain ⟨hex, -, hrest⟩ := lemma_A_3 hD hA A ZA hRic
    choose! An ZAn hAn using hex
    obtain ⟨hlb, -, hconv, -⟩ := hrest An ZAn hAn
    intro t ht
    have h1 : ∀ᵐ ω ∂P, ∀ n : ℕ, 1 ≤ n → 1 / (1 / (2 * (n : ℝ)) + c t) ≤ An n t ω := by
      rw [ae_all_iff]; intro n
      by_cases hn : 1 ≤ n
      · filter_upwards [hlb n hn t ht.le] with ω hω _
        rwa [hcond t ht.le, condExp_const ((filtF hD).le t)] at hω
      · exact ae_of_all _ (fun ω h => absurd h hn)
    have hct : 0 < c t := by
      have := hc_low t t.2 (le_of_lt (by exact_mod_cast ht))
      have h2 : 0 < (T - t) * (1 / (2 * cH)) := by
        apply mul_pos (by simp only [hTdef]; exact sub_pos.2 (by exact_mod_cast ht))
        positivity
      linarith
    filter_upwards [h1, hconv t ht] with ω h1 h2
    have h0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop two_pos
      refine (tendsto_inv_atTop_zero.comp h3).congr (fun n => ?_)
      simp [Function.comp, one_div]
    have h3 : Tendsto (fun n : ℕ => 1 / (1 / (2 * (n : ℝ)) + c t)) atTop (𝓝 (1 / c t)) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).div (h0.add_const (c t)) (by simpa using hct.ne')
      rw [zero_add] at this; exact this
    exact le_of_tendsto_of_tendsto h3 h2 (eventually_atTop.2 ⟨1, fun n hn => h1 n hn⟩)
  -- joint measurability of `A`
  set F : ℝ × Ω → ℝ := fun p => A (min p.1.toNNReal D.T) p.2 with hF
  have hFm : Measurable F := by
    have hAprog := hRic.1.1 D.T
    have hmap : @Measurable (ℝ × Ω) (Set.Iic D.T × Ω) _
        (@Prod.instMeasurableSpace _ _ _ (filtF hD D.T))
        (fun p : ℝ × Ω => ((⟨min p.1.toNNReal D.T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic D.T), p.2)) :=
      @Measurable.prodMk _ _ _ _ _ (filtF hD D.T) _ _
        (Measurable.subtype_mk ((measurable_real_toNNReal.comp measurable_fst).min
          measurable_const))
        (Measurable.mono measurable_snd le_rfl ((filtF hD).le D.T))
    exact hAprog.measurable.comp hmap
  -- Fubini: a.s., for a.e. `u ∈ [0, T)`, `A_u ≥ 1 / c(u)`
  have hG2 : ∀ᵐ ω ∂P, ∀ᵐ u ∂(volume.restrict (Ico (0 : ℝ) T)), 1 / c u ≤ F (u, ω) := by
    have hmeasS : MeasurableSet {p : ℝ × Ω | 1 / c p.1 ≤ F (p.1, p.2)} :=
      measurableSet_le ((hc_cont.measurable.comp measurable_fst).const_div 1) hFm
    refine (Measure.ae_ae_comm (p := fun u ω => 1 / c u ≤ F (u, ω)) hmeasS).1 ?_
    rw [ae_restrict_iff' measurableSet_Ico]
    refine ae_of_all _ fun u hu => ?_
    have hu' : u.toNNReal < D.T := (Real.toNNReal_lt_iff_lt_coe hu.1).2 hu.2
    filter_upwards [hAlow _ hu'] with ω hω
    simp only [hF, min_eq_left hu'.le]
    rwa [Real.coe_toNNReal _ hu.1] at hω
  -- local square integrability of `A`
  have hG1 : ∀ᵐ ω ∂P, ∀ m : ℕ,
      IntegrableOn (fun u => F (u, ω)) (Icc 0 (T - T / (m + 2))) := by
    rw [ae_all_iff]; intro m
    have hpos : 0 ≤ T - T / (m + 2) := by
      have : T / (m + 2) ≤ T := div_le_self hT.le (by linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
      linarith
    set τ : ℝ≥0 := (T - T / (m + 2)).toNNReal with hτ
    have hτR : (τ : ℝ) = T - T / (m + 2) := Real.coe_toNNReal _ hpos
    have hτT : τ < D.T := by
      rw [Real.toNNReal_lt_iff_lt_coe hpos]
      have : 0 < T / (m + 2) := by positivity
      linarith
    have hS := hRic.1.2 τ hτT
    have hle : ∀ ω, ∫⁻ u in Icc 0 (τ : ℝ), ‖F (u, ω)‖ₑ ^ 2 ≤
        (⨆ t ∈ Set.Iic τ, ‖A t ω‖ₑ ^ 2) * volume (Icc 0 (τ : ℝ)) := by
      intro ω
      rw [← setLIntegral_const]
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      have hmem : min u.toNNReal D.T ∈ Set.Iic τ := by
        apply Set.mem_Iic.2 (min_le_of_left_le _)
        exact Real.toNNReal_le_iff_le_coe.2 hu.2
      exact le_iSup₂ (f := fun t (_ : t ∈ Set.Iic τ) => ‖A t ω‖ₑ ^ 2) _ hmem
    have hint : ∫⁻ ω, ∫⁻ u in Icc 0 (τ : ℝ), ‖F (u, ω)‖ₑ ^ 2 ∂volume ∂P < ⊤ := by
      refine (lintegral_mono hle).trans_lt ?_
      rw [lintegral_mul_const' _ _ measure_Icc_lt_top.ne]
      exact ENNReal.mul_lt_top hS measure_Icc_lt_top
    have hmeas : Measurable fun ω => ∫⁻ u in Icc 0 (τ : ℝ), ‖F (u, ω)‖ₑ ^ 2 :=
      (hFm.enorm.pow_const 2).lintegral_prod_left'
    filter_upwards [ae_lt_top hmeas hint.ne] with ω hω
    rw [← hτR]
    refine ⟨(hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ u in Icc 0 (τ : ℝ), ‖F (u, ω)‖ₑ
        ≤ ∫⁻ u in Icc 0 (τ : ℝ), (1 + ‖F (u, ω)‖ₑ ^ 2) :=
          lintegral_mono fun u => MFGL2Aux.enorm_le_one_add_sq _
      _ = volume (Icc 0 (τ : ℝ)) + ∫⁻ u in Icc 0 (τ : ℝ), ‖F (u, ω)‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_Icc_lt_top, hω⟩
  -- conclusion
  refine ⟨cH / cL, ?_⟩
  filter_upwards [hG1, hG2] with ω hG1 hG2
  intro r s hr hrs hsT
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s ≤ T - T / (m + 2) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (T / (T - s))
    refine ⟨m, ?_⟩
    have hTs : 0 < T - s := sub_pos.2 hsT
    have h1 : T / (T - s) < m + 2 := by linarith
    have h2 : T < (T - s) * (m + 2) := by rwa [div_lt_iff₀ hTs, mul_comm] at h1
    have h3 : T / (m + 2) < T - s := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  have hsubrs : Icc r s ⊆ Icc 0 T := Icc_subset_Icc hr hsT.le
  have hIntF : IntegrableOn (fun u => F (u, ω)) (Icc r s) :=
    (hG1 m).mono_set (Icc_subset_Icc hr hm)
  have heq : ∀ᵐ u ∂(volume.restrict (Icc r s)),
      A u.toNNReal ω / (2 * D.η u.toNNReal ω) = F (u, ω) * gb u := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hsubrs hgb_ae
    filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with u hu huI
    rw [hu.2, hdet _ ω ω0]
    simp only [hF, hminT u (hsubrs huI).2]
    ring
  have hInt1 : IntegrableOn (fun u => A u.toNNReal ω / (2 * D.η u.toNNReal ω)) (Icc r s) := by
    have : IntegrableOn (fun u => F (u, ω) * gb u) (Icc r s) :=
      hIntF.mul_bdd hgbm.aestronglyMeasurable (c := 1 / (2 * cL))
        (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs, abs_of_pos (hgbpos u)]; exact hgbK u)
    exact this.congr (heq.mono fun u hu => hu.symm)
  have hTs : 0 < T - s := sub_pos.2 hsT
  have hms : 0 < (T - s) * (1 / (2 * cH)) := by positivity
  have hcu : ∀ u ∈ Icc r s, (T - s) * (1 / (2 * cH)) ≤ c u := by
    intro u hu
    have := hc_low u (hr.trans hu.1) (hu.2.trans hsT.le)
    have h2 : (T - s) * (1 / (2 * cH)) ≤ (T - u) * (1 / (2 * cH)) := by
      gcongr; exact hu.2
    linarith
  have hInt2 : IntegrableOn (fun u => gb u / c u) (Icc r s) := by
    refine Measure.integrableOn_of_bounded (M := (1 / (2 * cL)) / ((T - s) * (1 / (2 * cH))))
      measure_Icc_lt_top.ne (hgbm.div hc_cont.measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hcu' := hcu u hu
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hgbpos u) (hms.trans_le hcu'))]
    exact div_le_div₀ (by positivity) (hgbK u) hms hcu'
  have hmono_int : ∫ u in Icc r s, gb u / c u ≤
      ∫ u in Icc r s, A u.toNNReal ω / (2 * D.η u.toNNReal ω) := by
    apply setIntegral_mono_ae_restrict hInt2 hInt1
    have h2 := ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Ico_right hsT : Icc r s ⊆ Ico r T) (ae_restrict_of_ae_restrict_of_subset
        (Ico_subset_Ico_left hr) hG2)
    filter_upwards [heq, h2] with u hu1 hu2
    rw [hu1]
    calc gb u / c u = (1 / c u) * gb u := by ring
      _ ≤ F (u, ω) * gb u := mul_le_mul_of_nonneg_right hu2 (hgbpos u).le
  have hftc : ∫ u in Icc r s, gb u / c u = Real.log (c r) - Real.log (c s) :=
    MFGL2Aux.key_ftc gb T (1 / (2 * cL)) hgbm hgbpos hgbK r s hrs hsT
  have hcr : (T - r) * (1 / (2 * cH)) ≤ c r := hc_low r hr (hrs.trans hsT.le)
  have hTr : 0 < T - r := by linarith
  have hcr0 : 0 < c r := lt_of_lt_of_le (by positivity) hcr
  have hcs0 : 0 < c s := hms.trans_le (hcu s ⟨hrs, le_rfl⟩)
  have hcs : c s ≤ (T - s) * (1 / (2 * cL)) := hc_up s hsT.le
  calc Real.exp (-∫ u in Icc r s, A u.toNNReal ω / (2 * D.η u.toNNReal ω))
      ≤ Real.exp (-(Real.log (c r) - Real.log (c s))) := by
        apply Real.exp_le_exp.2; linarith
    _ = c s / c r := by
        rw [neg_sub, Real.exp_sub, Real.exp_log hcs0, Real.exp_log hcr0]
    _ ≤ cH / cL * ((T - s) / (T - r)) := by
        rw [div_le_iff₀ hcr0]
        have hk : cH / cL * ((T - s) / (T - r)) * ((T - r) * (1 / (2 * cH))) =
            (T - s) * (1 / (2 * cL)) := by
          field_simp
        have := mul_le_mul_of_nonneg_left hcr
          (by positivity : (0 : ℝ) ≤ cH / cL * ((T - s) / (T - r)))
        linarith
