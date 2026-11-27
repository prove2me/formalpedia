-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_restrictedExponent_bohr_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-27T03:53:53.049198+00:00
-- url     : https://prove2.me/submissions/48dc21ff-f953-49a0-9416-7f0dc4edd5e3

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

/-! ### Auxiliary lemmas for the Cesàro kernel `S U w = ∫ u in Icc 0 U, cos (u * w)`. -/

private lemma auxD2_S_eq (U w : Real) (hU : 0 ≤ U) :
    (∫ u in Set.Icc (0 : Real) U, Real.cos (u * w) ∂volume)
      = if w = 0 then U else Real.sin (U * w) / w := by
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    have h2 : ∀ u ∈ Set.Icc (0 : Real) U, Real.cos (u * (0 : Real)) = 1 := fun u _ => by simp
    rw [setIntegral_congr_fun measurableSet_Icc h2, setIntegral_const, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hU)]
    simp
  · rw [if_neg hw]
    have hderiv : ∀ u : Real, HasDerivAt (fun t => Real.sin (t * w) / w) (Real.cos (u * w)) u := by
      intro u
      have h1 : HasDerivAt (fun t => Real.sin (t * w)) (Real.cos (u * w) * w) u := by
        have hlin : HasDerivAt (fun t : Real => t * w) w u := by
          simpa using (hasDerivAt_id u).mul_const w
        have h := hlin.sin
        simpa using h
      have h2 := h1.div_const w
      rwa [mul_div_assoc, div_self hw, mul_one] at h2
    have hder : deriv (fun t => Real.sin (t * w) / w) = fun u => Real.cos (u * w) :=
      funext fun u => (hderiv u).deriv
    have hint : IntervalIntegrable (deriv (fun t => Real.sin (t * w) / w)) volume 0 U := by
      rw [hder]
      exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 U
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hU, ← hder,
      intervalIntegral.integral_deriv_eq_sub (fun u _ => (hderiv u).differentiableAt) hint]
    simp

private lemma auxD2_S_abs_le_U (U w : Real) (hU : 0 ≤ U) :
    |(∫ u in Set.Icc (0 : Real) U, Real.cos (u * w) ∂volume)| ≤ U := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : Real) U)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hint : Integrable (fun u => Real.cos (u * w)) (volume.restrict (Set.Icc (0 : Real) U)) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc |(∫ u in Set.Icc (0 : Real) U, Real.cos (u * w) ∂volume)|
      ≤ ∫ u in Set.Icc (0 : Real) U, |Real.cos (u * w)| ∂volume := by
        have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Icc (0 : Real) U))
          (fun u => Real.cos (u * w))
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∫ u in Set.Icc (0 : Real) U, (1 : Real) ∂volume :=
        integral_mono_ae hint.norm (integrable_const (1 : Real))
          (Eventually.of_forall fun u => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    _ = U := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hU)]
        simp

private lemma auxD2_S_abs_le_inv (U w : Real) (hU : 0 ≤ U) (hw : w ≠ 0) :
    |(∫ u in Set.Icc (0 : Real) U, Real.cos (u * w) ∂volume)| ≤ 1 / |w| := by
  rw [auxD2_S_eq U w hU, if_neg hw, abs_div, div_le_iff₀ (abs_pos.mpr hw),
    one_div_mul_cancel (abs_pos.mpr hw).ne']
  exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

private lemma auxD2_S_measurable (U : Real) (hU : 0 ≤ U) :
    Measurable (fun w => ∫ u in Set.Icc (0 : Real) U, Real.cos (u * w) ∂volume) := by
  have hfun : (fun w => ∫ u in Set.Icc (0 : Real) U, Real.cos (u * w) ∂volume)
      = fun w => if w = 0 then U else Real.sin (U * w) / w := by
    funext w
    exact auxD2_S_eq U w hU
  rw [hfun]
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
    ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).div measurable_id)

/-! ### The strip sets around the diagonal in `ℝ × ℝ`. -/

private def stripSet (η : Real) : Set (Real × Real) := {p | |p.1 - p.2| ≤ η}

private lemma stripSet_measurable (η : Real) : MeasurableSet (stripSet η) := by
  have hcont : Continuous (fun p : Real × Real => |p.1 - p.2|) :=
    (continuous_fst.sub continuous_snd).abs
  exact measurableSet_le hcont.measurable measurable_const

private lemma stripSet_mono {η₁ η₂ : Real} (h : η₁ ≤ η₂) : stripSet η₁ ⊆ stripSet η₂ :=
  fun _ hp => le_trans hp h

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ δ : Real, 0 < δ → δ ≤ 1 → ∀ ε : ENNReal, 0 < ε →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ENNReal.ofReal ((Pi (Set.Icc δ 1)).toReal^2) + (1/2 : ENNReal) * ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal + ε) := by
  intro hPi δ hδ hδ1 ε hε
  by_cases hεtop : ε = ⊤
  · subst hεtop
    exact ⟨0, fun W _ => by simp⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  have hLevy : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi) < ⊤ := hTriplet.2.2.2.1
  have hfin : Pi (Set.Icc δ 1) < ⊤ := by
    have hstep : ENNReal.ofReal δ * Pi (Set.Icc δ 1)
        ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi := by
      calc ENNReal.ofReal δ * Pi (Set.Icc δ 1)
          = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal δ ∂Pi := by
            rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
              (Eventually.of_forall (fun y hy => ENNReal.ofReal_le_ofReal (le_min hδ1 hy.1))))
      _ ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_set (fun y hy => lt_of_lt_of_le hδ hy.1)
    by_contra htop
    have htop' : Pi (Set.Icc δ 1) = ⊤ := top_unique (not_lt.mp htop)
    rw [htop', ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))] at hstep
    exact lt_irrefl _ (lt_of_le_of_lt hstep hLevy)
  set μ : Measure Real := Pi.restrict (Set.Icc δ 1) with hμdef
  have hμuniv : μ Set.univ = Pi (Set.Icc δ 1) := by
    rw [hμdef]
    exact Measure.restrict_apply_univ _
  haveI hfinμ : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact hfin⟩
  haveI : IsFiniteMeasure (μ.prod μ) := ⟨by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hμuniv]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hfin.ne hfin.ne)⟩
  set Λ : Real := (Pi (Set.Icc δ 1)).toReal with hΛdef
  have hΛnn : 0 ≤ Λ := ENNReal.toReal_nonneg
  set A : Real := (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal with hAdef
  have hAnn : 0 ≤ A := ENNReal.toReal_nonneg
  have hν2 : ((μ.prod μ) Set.univ).toReal = Λ ^ 2 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul, hμuniv, ← hΛdef, pow_two]
  have hAfin' : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi)
        ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal Λ ∂Pi := by
          apply lintegral_mono_ae
          apply (ae_restrict_iff' measurableSet_Icc).mpr
          apply Eventually.of_forall
          intro y hy
          apply ENNReal.ofReal_le_ofReal
          have hle : Pi {y} ≤ Pi (Set.Icc δ 1) := measure_mono (Set.singleton_subset_iff.mpr hy)
          exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin.ne hle) hfin.ne).mpr hle
    _ = ENNReal.ofReal Λ * Pi (Set.Icc δ 1) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  -- The atom-mass integral `A` is the product measure of the diagonal.
  have hdiag : (μ.prod μ) {p : Real × Real | p.1 = p.2} = ∫⁻ y, μ {y} ∂μ := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    apply lintegral_congr
    intro y
    congr 1
    ext z
    simp [eq_comm]
  have hAeq : (∫⁻ y, μ {y} ∂μ) = ENNReal.ofReal A := by
    have h1 : (∫⁻ y, μ {y} ∂μ)
        = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi := by
      rw [hμdef]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have h2 : Pi.restrict (Set.Icc δ 1) {y} = Pi {y} := by
        rw [Measure.restrict_apply (measurableSet_singleton _)]
        congr 1
        exact Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hy)
      have h3 : Pi {y} ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (Set.singleton_subset_iff.mpr hy))
      rw [h2, ENNReal.ofReal_toReal h3]
    rw [h1, hAdef, ENNReal.ofReal_toReal hAfin']
  -- Strips around the diagonal shrink to it; pick one with real measure `≤ A + ε/2`.
  have hstrip_anti : Antitone (fun n : ℕ => stripSet (1 / ((n : Real) + 1))) := by
    intro a b hab
    apply stripSet_mono
    apply one_div_le_one_div_of_le
    · have hnn : (0 : Real) ≤ (a : Real) := Nat.cast_nonneg a
      linarith
    · have h1 : (a : Real) ≤ (b : Real) := by exact_mod_cast hab
      linarith
  have hInter : ⋂ n : ℕ, stripSet (1 / ((n : Real) + 1)) = {p : Real × Real | p.1 = p.2} := by
    ext p
    simp only [Set.mem_iInter, stripSet, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hne
      have hpos : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact (not_lt.mpr (h n)) hn
    · intro h n
      rw [h, sub_self, abs_zero]
      positivity
  have hstrip_choice : ∃ n : ℕ,
      ((μ.prod μ) (stripSet (1 / ((n : Real) + 1)))).toReal ≤ A + ε.toReal / 2 := by
    by_contra hcon
    push_neg at hcon
    have hfin2 : ∀ n : ℕ, (μ.prod μ) (stripSet (1 / ((n : Real) + 1))) ≠ ⊤ :=
      fun n => measure_ne_top _ _
    have hge : ∀ n : ℕ, ENNReal.ofReal (A + ε.toReal / 2)
        ≤ (μ.prod μ) (stripSet (1 / ((n : Real) + 1))) := by
      intro n
      rw [← ENNReal.ofReal_toReal (hfin2 n)]
      exact ENNReal.ofReal_le_ofReal (hcon n).le
    have hci : ENNReal.ofReal (A + ε.toReal / 2)
        ≤ ⨅ n : ℕ, (μ.prod μ) (stripSet (1 / ((n : Real) + 1))) := le_ciInf hge
    rw [← hstrip_anti.measure_iInter (fun n => (stripSet_measurable _).nullMeasurableSet)
      ⟨0, hfin2 0⟩, hInter, hdiag, hAeq] at hci
    have hle := (ENNReal.ofReal_le_ofReal_iff (by linarith [hAnn, he.le] : (0 : Real) ≤ A)).mp hci
    linarith [he]
  obtain ⟨n, hn⟩ := hstrip_choice
  set η : Real := 1 / ((n : Real) + 1) with hηdef
  have hη : 0 < η := by
    rw [hηdef]
    positivity
  have haeIcc : ∀ᵐ y ∂μ, y ∈ Set.Icc δ 1 := ae_restrict_mem measurableSet_Icc
  have hr_meas : Measurable (fun u => (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) := by
    have hcont : Continuous (fun p : Real × Real => (1 : Real) - Real.cos (p.1 * p.2)) :=
      continuous_const.sub (Real.continuous_cos.comp (continuous_fst.mul continuous_snd))
    have hF : Measurable (fun p : Real × Real => ENNReal.ofReal (1 - Real.cos (p.1 * p.2))) :=
      (ENNReal.continuous_ofReal.comp hcont).measurable
    exact (hF.lintegral_prod_right').ennreal_toReal
  have hCint : ∀ u : Real, Integrable (fun y => Real.cos (u * y)) μ := by
    intro u
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hSint' : ∀ u : Real, Integrable (fun y => Real.sin (u * y)) μ := by
    intro u
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hR_eq : ∀ u : Real, (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal
      = Λ - ∫ y, Real.cos (u * y) ∂μ := by
    intro u
    have h1 : (∫ y, (1 : Real) - Real.cos (u * y) ∂μ) = Λ - ∫ y, Real.cos (u * y) ∂μ := by
      rw [integral_sub (integrable_const (1 : Real)) (hCint u)]
      congr 1
      rw [integral_const, measureReal_def, hμuniv, smul_eq_mul, mul_one, hΛdef]
    rw [← h1]
    exact (integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y => sub_nonneg.mpr (Real.cos_le_one _))
      (continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable).symm
  have hr_le : ∀ u : Real, (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ 2 * Λ := by
    intro u
    have hle : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
        ≤ ENNReal.ofReal 2 * Pi (Set.Icc δ 1) := by
      calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
          ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal 2 ∂Pi :=
            lintegral_mono fun y => ENNReal.ofReal_le_ofReal
              (by linarith [Real.neg_one_le_cos (u * y), Real.cos_le_one (u * y)])
      _ = ENNReal.ofReal 2 * Pi (Set.Icc δ 1) := by
            rw [lintegral_const, Measure.restrict_apply_univ]
    have h := (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hle)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)).mpr hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)] at h
  have hC_abs : ∀ u : Real, |∫ y, Real.cos (u * y) ∂μ| ≤ Λ := by
    intro u
    calc |∫ y, Real.cos (u * y) ∂μ|
        ≤ ∫ y, |Real.cos (u * y)| ∂μ := by
          have h := norm_integral_le_integral_norm (μ := μ) (fun y => Real.cos (u * y))
          simpa [Real.norm_eq_abs] using h
    _ ≤ ∫ y, (1 : Real) ∂μ :=
          integral_mono_ae (hCint u).norm (integrable_const (1 : Real))
            (Eventually.of_forall fun y => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    _ = Λ := by
          rw [integral_const, measureReal_def, hμuniv, smul_eq_mul, mul_one, hΛdef]
  have hC_meas : Measurable (fun u => ∫ y, Real.cos (u * y) ∂μ) := by
    have hfun : (fun u => ∫ y, Real.cos (u * y) ∂μ)
        = fun u => Λ - (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal := by
      funext u
      have := hR_eq u
      linarith
    rw [hfun]
    exact measurable_const.sub hr_meas
  have hS_meas : Measurable (fun u => ∫ y, Real.sin (u * y) ∂μ) := by
    have hcont : Continuous (fun u => ∫ y, Real.sin (u * y) ∂μ) := by
      refine MeasureTheory.continuous_of_dominated
        (F := fun u y => Real.sin (u * y)) (bound := fun _ : Real => (1 : Real))
        (fun u => (hSint' u).aestronglyMeasurable) ?_ (integrable_const (1 : Real)) ?_
      · intro u
        exact Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      · exact Eventually.of_forall fun y =>
          Real.continuous_sin.comp (continuous_id.mul continuous_const)
    exact hcont.measurable
  refine ⟨max 1 (Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) * 4 / ε.toReal), fun W hWge => ?_⟩
  have hW1 : (1 : Real) ≤ W := (le_max_left _ _).trans hWge
  have hW : 0 < W := zero_lt_one.trans_le hW1
  have hW' : 0 ≤ W := hW.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : Real) W)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hC_intble : Integrable (fun u => ∫ y, Real.cos (u * y) ∂μ)
      (volume.restrict (Set.Icc (0 : Real) W)) := by
    refine Integrable.of_bound hC_meas.aestronglyMeasurable Λ ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact hC_abs u
  have hC2_intble : Integrable (fun u => (∫ y, Real.cos (u * y) ∂μ) ^ 2)
      (volume.restrict (Set.Icc (0 : Real) W)) := by
    refine Integrable.of_bound (hC_meas.pow_const 2).aestronglyMeasurable (Λ ^ 2) ?_
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC_abs u) 2
  have hr2_intble : Integrable
      (fun u => ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2)
      (volume.restrict (Set.Icc (0 : Real) W)) := by
    refine Integrable.of_bound (hr_meas.pow_const 2).aestronglyMeasurable ((2 * Λ) ^ 2) ?_
    refine Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg ENNReal.toReal_nonneg]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hr_le u) 2
  have hJointC : Integrable (Function.uncurry (fun x y => Real.cos (x * y)))
      ((volume.restrict (Set.Icc (0 : Real) W)).prod μ) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_fst.mul continuous_snd)).aestronglyMeasurable
    · exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hCswap : (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume)
      = ∫ y, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * y) ∂volume) ∂μ :=
    integral_integral_swap hJointC
  have hCbound : |(∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume)| ≤ Λ / δ := by
    have hSint : Integrable (fun y => |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * y) ∂volume)|) μ := by
      refine Integrable.of_bound (auxD2_S_measurable W hW').abs.aestronglyMeasurable (1 / δ) ?_
      filter_upwards [haeIcc] with y hy
      rw [Real.norm_eq_abs, abs_abs]
      refine (auxD2_S_abs_le_inv W y hW' (ne_of_gt (lt_of_lt_of_le hδ hy.1))).trans ?_
      rw [abs_of_pos (lt_of_lt_of_le hδ hy.1)]
      exact one_div_le_one_div_of_le hδ hy.1
    calc |(∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume)|
        = |(∫ y, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * y) ∂volume) ∂μ)| := by rw [hCswap]
    _ ≤ ∫ y, |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * y) ∂volume)| ∂μ := by
          have h := norm_integral_le_integral_norm (μ := μ)
            (fun y => ∫ u in Set.Icc (0 : Real) W, Real.cos (u * y) ∂volume)
          simpa [Real.norm_eq_abs] using h
    _ ≤ ∫ y, (1 / δ : Real) ∂μ := by
          apply integral_mono_ae hSint (integrable_const (1 / δ : Real))
          filter_upwards [haeIcc] with y hy
          refine (auxD2_S_abs_le_inv W y hW' (ne_of_gt (lt_of_lt_of_le hδ hy.1))).trans ?_
          rw [abs_of_pos (lt_of_lt_of_le hδ hy.1)]
          exact one_div_le_one_div_of_le hδ hy.1
    _ = Λ / δ := by
          rw [integral_const, measureReal_def, hμuniv, smul_eq_mul, ← hΛdef]
          exact (div_eq_mul_one_div Λ δ).symm
  have hIntcosE : ∀ u : Real, Integrable (fun p : Real × Real => Real.cos (u * (p.1 - p.2))) (μ.prod μ) := by
    intro u
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul (continuous_fst.sub continuous_snd))).aestronglyMeasurable
    · exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hIntcosG : ∀ u : Real, Integrable (fun p : Real × Real => Real.cos (u * (p.1 + p.2))) (μ.prod μ) := by
    intro u
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul (continuous_fst.add continuous_snd))).aestronglyMeasurable
    · exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hE_id : ∀ u : Real, (∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))
      = (∫ y, Real.cos (u * y) ∂μ) ^ 2 + (∫ y, Real.sin (u * y) ∂μ) ^ 2 := by
    intro u
    have hstep : (∫ y, ∫ y', Real.cos (u * (y - y')) ∂μ ∂μ)
        = ∫ y, (Real.cos (u * y) * (∫ y', Real.cos (u * y') ∂μ)
            + Real.sin (u * y) * (∫ y', Real.sin (u * y') ∂μ)) ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      show (∫ y', Real.cos (u * (y - y')) ∂μ)
        = Real.cos (u * y) * (∫ y', Real.cos (u * y') ∂μ)
          + Real.sin (u * y) * (∫ y', Real.sin (u * y') ∂μ)
      rw [integral_congr_ae (Eventually.of_forall fun y' =>
        show Real.cos (u * (y - y')) = Real.cos (u * y) * Real.cos (u * y')
          + Real.sin (u * y) * Real.sin (u * y') by rw [mul_sub, Real.cos_sub])]
      rw [integral_add ((hCint u).const_mul _) ((hSint' u).const_mul _), integral_const_mul,
        integral_const_mul]
    calc (∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))
        = ∫ y, ∫ y', Real.cos (u * (y - y')) ∂μ ∂μ :=
          (integral_integral (f := fun y y' => Real.cos (u * (y - y'))) (hIntcosE u)).symm
      _ = ∫ y, (Real.cos (u * y) * (∫ y', Real.cos (u * y') ∂μ)
            + Real.sin (u * y) * (∫ y', Real.sin (u * y') ∂μ)) ∂μ := hstep
      _ = (∫ y, Real.cos (u * y) ∂μ) ^ 2 + (∫ y, Real.sin (u * y) ∂μ) ^ 2 := by
          rw [integral_add ((hCint u).mul_const _) ((hSint' u).mul_const _), integral_mul_const,
            integral_mul_const]
          ring
  have hG_id : ∀ u : Real, (∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))
      = (∫ y, Real.cos (u * y) ∂μ) ^ 2 - (∫ y, Real.sin (u * y) ∂μ) ^ 2 := by
    intro u
    have hstep : (∫ y, ∫ y', Real.cos (u * (y + y')) ∂μ ∂μ)
        = ∫ y, (Real.cos (u * y) * (∫ y', Real.cos (u * y') ∂μ)
            - Real.sin (u * y) * (∫ y', Real.sin (u * y') ∂μ)) ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      show (∫ y', Real.cos (u * (y + y')) ∂μ)
        = Real.cos (u * y) * (∫ y', Real.cos (u * y') ∂μ)
          - Real.sin (u * y) * (∫ y', Real.sin (u * y') ∂μ)
      rw [integral_congr_ae (Eventually.of_forall fun y' =>
        show Real.cos (u * (y + y')) = Real.cos (u * y) * Real.cos (u * y')
          - Real.sin (u * y) * Real.sin (u * y') by rw [mul_add, Real.cos_add])]
      rw [integral_sub ((hCint u).const_mul _) ((hSint' u).const_mul _), integral_const_mul,
        integral_const_mul]
    calc (∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))
        = ∫ y, ∫ y', Real.cos (u * (y + y')) ∂μ ∂μ :=
          (integral_integral (f := fun y y' => Real.cos (u * (y + y'))) (hIntcosG u)).symm
      _ = ∫ y, (Real.cos (u * y) * (∫ y', Real.cos (u * y') ∂μ)
            - Real.sin (u * y) * (∫ y', Real.sin (u * y') ∂μ)) ∂μ := hstep
      _ = (∫ y, Real.cos (u * y) ∂μ) ^ 2 - (∫ y, Real.sin (u * y) ∂μ) ^ 2 := by
          rw [integral_sub ((hCint u).mul_const _) ((hSint' u).mul_const _), integral_mul_const,
            integral_mul_const]
          ring
  have hE_meas : Measurable (fun u => ∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ)) := by
    have hfun : (fun u => ∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))
        = fun u => (∫ y, Real.cos (u * y) ∂μ) ^ 2 + (∫ y, Real.sin (u * y) ∂μ) ^ 2 := by
      funext u; exact hE_id u
    rw [hfun]
    exact (hC_meas.pow_const 2).add (hS_meas.pow_const 2)
  have hG_meas : Measurable (fun u => ∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ)) := by
    have hfun : (fun u => ∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))
        = fun u => (∫ y, Real.cos (u * y) ∂μ) ^ 2 - (∫ y, Real.sin (u * y) ∂μ) ^ 2 := by
      funext u; exact hG_id u
    rw [hfun]
    exact (hC_meas.pow_const 2).sub (hS_meas.pow_const 2)
  have hE_abs : ∀ u : Real, |(∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))| ≤ Λ ^ 2 := by
    intro u
    calc |(∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))|
        ≤ ∫ p, |Real.cos (u * (p.1 - p.2))| ∂(μ.prod μ) := by
          have h := norm_integral_le_integral_norm (μ := μ.prod μ)
            (fun p => Real.cos (u * (p.1 - p.2)))
          simpa [Real.norm_eq_abs] using h
    _ ≤ ∫ p, (1 : Real) ∂(μ.prod μ) :=
          integral_mono_ae (hIntcosE u).norm (integrable_const (1 : Real))
            (Eventually.of_forall fun p => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    _ = Λ ^ 2 := by
          rw [integral_const, measureReal_def, hν2, smul_eq_mul, mul_one]
  have hG_abs : ∀ u : Real, |(∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))| ≤ Λ ^ 2 := by
    intro u
    calc |(∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))|
        ≤ ∫ p, |Real.cos (u * (p.1 + p.2))| ∂(μ.prod μ) := by
          have h := norm_integral_le_integral_norm (μ := μ.prod μ)
            (fun p => Real.cos (u * (p.1 + p.2)))
          simpa [Real.norm_eq_abs] using h
    _ ≤ ∫ p, (1 : Real) ∂(μ.prod μ) :=
          integral_mono_ae (hIntcosG u).norm (integrable_const (1 : Real))
            (Eventually.of_forall fun p => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    _ = Λ ^ 2 := by
          rw [integral_const, measureReal_def, hν2, smul_eq_mul, mul_one]
  have hE_intble : Integrable (fun u => ∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))
      (volume.restrict (Set.Icc (0 : Real) W)) := by
    refine Integrable.of_bound hE_meas.aestronglyMeasurable (Λ ^ 2) ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact hE_abs u
  have hG_intble : Integrable (fun u => ∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))
      (volume.restrict (Set.Icc (0 : Real) W)) := by
    refine Integrable.of_bound hG_meas.aestronglyMeasurable (Λ ^ 2) ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact hG_abs u
  have hJointE : Integrable (Function.uncurry (fun u p => Real.cos (u * (p.1 - p.2))))
      ((volume.restrict (Set.Icc (0 : Real) W)).prod (μ.prod μ)) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_fst.mul
        ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))).aestronglyMeasurable
    · exact Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hJointG : Integrable (Function.uncurry (fun u p => Real.cos (u * (p.1 + p.2))))
      ((volume.restrict (Set.Icc (0 : Real) W)).prod (μ.prod μ)) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (Real.continuous_cos.comp (continuous_fst.mul
        ((continuous_fst.comp continuous_snd).add (continuous_snd.comp continuous_snd)))).aestronglyMeasurable
    · exact Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hEswap : (∫ u in Set.Icc (0 : Real) W, (∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ)) ∂volume)
      = ∫ p, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 - p.2)) ∂volume) ∂(μ.prod μ) :=
    integral_integral_swap hJointE
  have hGswap : (∫ u in Set.Icc (0 : Real) W, (∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ)) ∂volume)
      = ∫ p, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume) ∂(μ.prod μ) :=
    integral_integral_swap hJointG
  have hSp_int : Integrable (fun p : Real × Real =>
      ∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 - p.2)) ∂volume) (μ.prod μ) := by
    refine Integrable.of_bound ?_ W ?_
    · have hm : Measurable (fun p : Real × Real =>
          ∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 - p.2)) ∂volume) :=
        (auxD2_S_measurable W hW').comp (measurable_fst.sub measurable_snd)
      exact hm.aestronglyMeasurable
    · exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact auxD2_S_abs_le_U W _ hW'
  have hGp_int : Integrable (fun p : Real × Real =>
      ∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume) (μ.prod μ) := by
    refine Integrable.of_bound ?_ W ?_
    · have hm : Measurable (fun p : Real × Real =>
          ∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume) :=
        (auxD2_S_measurable W hW').comp (measurable_fst.add measurable_snd)
      exact hm.aestronglyMeasurable
    · exact Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact auxD2_S_abs_le_U W _ hW'
  have hEbound : (∫ p, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 - p.2)) ∂volume) ∂(μ.prod μ))
      ≤ W * ((μ.prod μ) (stripSet η)).toReal + Λ ^ 2 / η := by
    have hsplit := integral_add_compl (stripSet_measurable η) hSp_int
    rw [← hsplit]
    apply add_le_add
    · calc (∫ p in stripSet η, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 - p.2)) ∂volume) ∂(μ.prod μ))
          ≤ ∫ p in stripSet η, (W : Real) ∂(μ.prod μ) :=
            setIntegral_mono_on hSp_int.integrableOn ((integrable_const (W : Real)).integrableOn)
              (stripSet_measurable η) (fun p _ => (le_abs_self _).trans (auxD2_S_abs_le_U W _ hW'))
      _ = W * ((μ.prod μ) (stripSet η)).toReal := by
            rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
    · calc (∫ p in (stripSet η)ᶜ, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 - p.2)) ∂volume) ∂(μ.prod μ))
          ≤ ∫ p in (stripSet η)ᶜ, (1 / η : Real) ∂(μ.prod μ) := by
            apply setIntegral_mono_on hSp_int.integrableOn
              ((integrable_const (1 / η : Real)).integrableOn)
              (stripSet_measurable η).compl
            intro p hp
            have hgt : η < |p.1 - p.2| := by
              by_contra hc
              exact hp (le_of_not_gt hc)
            refine (le_abs_self _).trans ((auxD2_S_abs_le_inv W _ hW' (abs_pos.mp (hη.trans hgt))).trans ?_)
            exact one_div_le_one_div_of_le hη hgt.le
      _ = ((μ.prod μ) (stripSet η)ᶜ).toReal * (1 / η) := by
            rw [setIntegral_const, measureReal_def, smul_eq_mul]
      _ ≤ Λ ^ 2 * (1 / η) := by
            apply mul_le_mul_of_nonneg_right _ (one_div_nonneg.mpr hη.le)
            rw [← hν2]
            exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
              (measure_mono (Set.subset_univ _))
      _ = Λ ^ 2 / η := by rw [mul_one_div]
  have hGbound : |(∫ p, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume) ∂(μ.prod μ))|
      ≤ Λ ^ 2 / (2 * δ) := by
    have h1 : |(∫ p, (∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume) ∂(μ.prod μ))|
        ≤ ∫ p, |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume)| ∂(μ.prod μ) := by
      have h := norm_integral_le_integral_norm (μ := μ.prod μ)
        (fun p => ∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume)
      simpa [Real.norm_eq_abs] using h
    refine h1.trans ?_
    have h2 : (∫ p, |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume)| ∂(μ.prod μ))
        = (∫⁻ p, ENNReal.ofReal |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume)| ∂(μ.prod μ)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => abs_nonneg _)
        hGp_int.norm.aestronglyMeasurable
    rw [h2]
    have hAemeas : AEMeasurable (fun p : Real × Real =>
        ENNReal.ofReal |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (p.1 + p.2)) ∂volume)|) (μ.prod μ) :=
      (ENNReal.measurable_ofReal.comp ((auxD2_S_measurable W hW').comp
        (measurable_fst.add measurable_snd)).abs).aemeasurable
    rw [lintegral_prod _ hAemeas]
    have h3 : (∫⁻ y, ∫⁻ y', ENNReal.ofReal |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (y + y')) ∂volume)| ∂μ ∂μ)
        ≤ ∫⁻ y, ∫⁻ y', ENNReal.ofReal (1 / (2 * δ)) ∂μ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [haeIcc] with y hy
      apply lintegral_mono_ae
      filter_upwards [haeIcc] with y' hy'
      apply ENNReal.ofReal_le_ofReal
      have hsum : 0 < y + y' := by linarith [hy.1, hy'.1, hδ]
      calc |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (y + y')) ∂volume)|
          ≤ 1 / |y + y'| := auxD2_S_abs_le_inv W _ hW' (ne_of_gt hsum)
      _ = 1 / (y + y') := by rw [abs_of_pos hsum]
      _ ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by linarith [hδ]) (by linarith [hy.1, hy'.1])
    have h4 : (∫⁻ y, ∫⁻ y', ENNReal.ofReal (1 / (2 * δ)) ∂μ ∂μ)
        = ENNReal.ofReal (Λ ^ 2 / (2 * δ)) := by
      have hRHS : ENNReal.ofReal (Λ ^ 2 / (2 * δ))
          = ENNReal.ofReal (1 / (2 * δ)) * Pi (Set.Icc δ 1) * Pi (Set.Icc δ 1) := by
        rw [hΛdef, div_eq_mul_one_div, ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
        ring
      rw [hRHS]
      simp only [lintegral_const, hμuniv]
    have hx : (∫⁻ y, ∫⁻ y', ENNReal.ofReal |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (y + y')) ∂volume)| ∂μ ∂μ) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (lintegral_mono fun y => lintegral_mono fun y' =>
        ENNReal.ofReal_le_ofReal (auxD2_S_abs_le_U W _ hW'))
      simp only [lintegral_const, hμuniv]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hfin.ne
    have hy : (∫⁻ y, ∫⁻ y', ENNReal.ofReal (1 / (2 * δ)) ∂μ ∂μ) ≠ ⊤ := by
      rw [h4]
      exact ENNReal.ofReal_ne_top
    have h5 : (∫⁻ y, ∫⁻ y', ENNReal.ofReal |(∫ u in Set.Icc (0 : Real) W, Real.cos (u * (y + y')) ∂volume)| ∂μ ∂μ).toReal
        ≤ (∫⁻ y, ∫⁻ y', ENNReal.ofReal (1 / (2 * δ)) ∂μ ∂μ).toReal :=
      (ENNReal.toReal_le_toReal hx hy).mpr h3
    rwa [h4, ENNReal.toReal_ofReal (by
      apply div_nonneg (sq_nonneg Λ)
      linarith [hδ] : (0 : Real) ≤ Λ ^ 2 / (2 * δ))] at h5
  have hC2 : (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ^ 2 ∂volume)
      ≤ (1 / 2) * (W * ((μ.prod μ) (stripSet η)).toReal + Λ ^ 2 / η + Λ ^ 2 / (2 * δ)) := by
    have hpt : (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ^ 2 ∂volume)
        = (1 / 2) * ((∫ u in Set.Icc (0 : Real) W, (∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ)) ∂volume)
          + ∫ u in Set.Icc (0 : Real) W, (∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ)) ∂volume) := by
      rw [← integral_add hE_intble hG_intble]
      have hcongr : (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ^ 2 ∂volume)
          = ∫ u in Set.Icc (0 : Real) W, (1 / 2) * ((∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))
              + ∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ)) ∂volume :=
        setIntegral_congr_fun measurableSet_Icc (fun u _ => by
          show (∫ y, Real.cos (u * y) ∂μ) ^ 2
            = (1 / 2) * ((∫ p, Real.cos (u * (p.1 - p.2)) ∂(μ.prod μ))
              + ∫ p, Real.cos (u * (p.1 + p.2)) ∂(μ.prod μ))
          rw [hE_id u, hG_id u]
          ring)
      rw [hcongr, integral_const_mul]
    rw [hpt, hEswap, hGswap]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : Real) ≤ 1 / 2)
    exact add_le_add hEbound ((le_abs_self _).trans hGbound)
  have hInt_r2 : (∫ u in Set.Icc (0 : Real) W,
        ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume)
      = Λ ^ 2 * W - 2 * Λ * (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume)
        + ∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ^ 2 ∂volume := by
    set C : Real → Real := fun u => ∫ y, Real.cos (u * y) ∂μ
    have hcongr : (∫ u in Set.Icc (0 : Real) W,
          ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume)
        = ∫ u in Set.Icc (0 : Real) W, Λ ^ 2 - 2 * Λ * C u + C u ^ 2 ∂volume := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u _
      show ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2
        = Λ ^ 2 - 2 * Λ * C u + C u ^ 2
      rw [hR_eq u]
      ring
    -- Explicit pointwise summands (avoid Pi.sub matching failures).
    set f : Real → Real := fun u => Λ ^ 2 - 2 * Λ * C u
    set g : Real → Real := fun u => C u ^ 2
    have hfg : (∫ u in Set.Icc (0 : Real) W, Λ ^ 2 - 2 * Λ * C u + C u ^ 2 ∂volume)
        = ∫ u in Set.Icc (0 : Real) W, f u + g u ∂volume := rfl
    have hf : Integrable f (volume.restrict (Set.Icc (0 : Real) W)) := by
      simpa [f, C, sub_eq_add_neg, mul_assoc] using
        (integrable_const (Λ ^ 2)).add (hC_intble.const_mul (-(2 * Λ)))
    have hg : Integrable g (volume.restrict (Set.Icc (0 : Real) W)) := by
      simpa [g, C] using hC2_intble
    rw [hcongr, hfg, integral_add hf hg]
    -- Split ∫f = ∫Λ² - ∫(2Λ C)
    set f1 : Real → Real := fun _ => Λ ^ 2
    set f2 : Real → Real := fun u => 2 * Λ * C u
    have hf12 : (∫ u in Set.Icc (0 : Real) W, f u ∂volume)
        = ∫ u in Set.Icc (0 : Real) W, f1 u - f2 u ∂volume := rfl
    have hf1 : Integrable f1 (volume.restrict (Set.Icc (0 : Real) W)) := integrable_const _
    have hf2 : Integrable f2 (volume.restrict (Set.Icc (0 : Real) W)) := by
      simpa [f2, C] using hC_intble.const_mul (2 * Λ)
    rw [hf12, integral_sub hf1 hf2]
    have hf1W : ∫ u in Set.Icc (0 : Real) W, f1 u ∂volume = Λ ^ 2 * W := by
      simp only [f1]
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hW'), sub_zero, smul_eq_mul, mul_comm]
    have hf2W : ∫ u in Set.Icc (0 : Real) W, f2 u ∂volume
        = 2 * Λ * ∫ u in Set.Icc (0 : Real) W, C u ∂volume := by
      simp only [f2]
      exact integral_const_mul (2 * Λ) C
    rw [hf1W, hf2W]
  have hmid : -(2 * Λ * (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume))
      ≤ 2 * Λ * (Λ / δ) := by
    have h2 : -(∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume) ≤ Λ / δ := by
      have h := abs_le.mp hCbound
      linarith [h.1]
    calc -(2 * Λ * (∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume))
        = 2 * Λ * (-(∫ u in Set.Icc (0 : Real) W, (∫ y, Real.cos (u * y) ∂μ) ∂volume)) := by ring
    _ ≤ 2 * Λ * (Λ / δ) := mul_le_mul_of_nonneg_left h2 (by linarith [hΛnn])
  have hInt_r2_le : (∫ u in Set.Icc (0 : Real) W,
        ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume)
      ≤ Λ ^ 2 * W + 2 * Λ * (Λ / δ)
        + (1 / 2) * (W * ((μ.prod μ) (stripSet η)).toReal + Λ ^ 2 / η + Λ ^ 2 / (2 * δ)) := by
    rw [hInt_r2]
    linarith [hmid, hC2]
  have hErr : Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) / W ≤ ε.toReal / 4 := by
    by_cases hΛ0 : Λ = 0
    · have hz : Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) / W = 0 := by
        rw [hΛ0]
        norm_num
      rw [hz]
      exact div_nonneg he.le (by norm_num)
    · have hpos : 0 < Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) := by
        apply mul_pos (pow_pos (lt_of_le_of_ne hΛnn (Ne.symm hΛ0)) 2)
        apply add_pos
        · exact div_pos (by norm_num) (mul_pos (by norm_num) hδ)
        · exact one_div_pos.mpr (mul_pos (by norm_num) hη)
      rw [div_le_iff₀ hW]
      have hU0' : Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) * 4 / ε.toReal ≤ W :=
        (le_max_right _ _).trans hWge
      have he' : ε.toReal ≠ 0 := ne_of_gt he
      calc Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η))
          = (ε.toReal / 4) * (Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) * 4 / ε.toReal) := by
            have hX : (ε.toReal / 4) * (Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) * 4 / ε.toReal)
                = Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) := by
              rw [← mul_div_assoc,
                show (ε.toReal / 4) * (Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) * 4)
                    = Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) * ε.toReal by ring,
                mul_div_assoc, div_self he', mul_one]
            exact hX.symm
      _ ≤ (ε.toReal / 4) * W := mul_le_mul_of_nonneg_left hU0' (by linarith [he.le])
  have hM : (∫ u in Set.Icc (0 : Real) W,
        ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume) / W
      ≤ Λ ^ 2 + A / 2 + ε.toReal := by
    have hdiv : (∫ u in Set.Icc (0 : Real) W,
          ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume) / W
        ≤ (Λ ^ 2 * W + 2 * Λ * (Λ / δ)
          + (1 / 2) * (W * ((μ.prod μ) (stripSet η)).toReal + Λ ^ 2 / η + Λ ^ 2 / (2 * δ))) / W := by
      rw [div_le_iff₀ hW, div_mul_cancel₀ _ (ne_of_gt hW)]
      exact hInt_r2_le
    refine hdiv.trans ?_
    have hWne : W ≠ 0 := ne_of_gt hW
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hηne : η ≠ 0 := ne_of_gt hη
    have hid2 : (Λ ^ 2 * W + 2 * Λ * (Λ / δ)
          + (1 / 2) * (W * ((μ.prod μ) (stripSet η)).toReal + Λ ^ 2 / η + Λ ^ 2 / (2 * δ))) / W
        = Λ ^ 2 + (1 / 2) * ((μ.prod μ) (stripSet η)).toReal
          + (2 * Λ * (Λ / δ) + (1 / 2) * (Λ ^ 2 / η + Λ ^ 2 / (2 * δ))) / W := by
      field_simp
      ring
    rw [hid2]
    have hbr : (2 * Λ * (Λ / δ) + (1 / 2) * (Λ ^ 2 / η + Λ ^ 2 / (2 * δ))) / W ≤ ε.toReal / 4 := by
      have hid : (2 * Λ * (Λ / δ) + (1 / 2) * (Λ ^ 2 / η + Λ ^ 2 / (2 * δ))) / W
          = Λ ^ 2 * (9 / (4 * δ) + 1 / (2 * η)) / W := by
        field_simp
        ring
      rw [hid]
      exact hErr
    have hhalf : (1 / 2) * ((μ.prod μ) (stripSet η)).toReal ≤ A / 2 + ε.toReal / 4 := by
      linarith [hn]
    linarith [hbr, hhalf, he.le]
  have hnn : 0 ≤ ∫ u in Set.Icc (0 : Real) W,
      ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume :=
    integral_nonneg_of_ae (Eventually.of_forall fun u => sq_nonneg _)
  have hIntEq : ENNReal.ofReal (∫ u in Set.Icc (0 : Real) W,
        ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume)
      = ∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal
          (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hr2_intble (Eventually.of_forall fun u => sq_nonneg _)
  have hLHS : (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal
        (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2) ∂volume)
        * (ENNReal.ofReal W)⁻¹
      = ENNReal.ofReal ((∫ u in Set.Icc (0 : Real) W,
          ((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2 ∂volume) / W) := by
    rw [← hIntEq, ← ENNReal.ofReal_inv_of_pos hW, ← ENNReal.ofReal_mul hnn, div_eq_mul_inv]
  have h12 : ENNReal.ofReal (1 / 2 : Real) = (1 / 2 : ENNReal) := by
    have h2 : ENNReal.ofReal (2 : Real) = 2 := by
      rw [show (2 : Real) = ((2 : ℕ) : Real) by norm_num, ENNReal.ofReal_natCast, Nat.cast_ofNat]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2), ENNReal.ofReal_one, h2]
  have hA2 : ENNReal.ofReal (A / 2) = (1 / 2 : ENNReal) * ENNReal.ofReal A := by
    rw [show A / 2 = (1 / 2 : Real) * A by ring, ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 1 / 2), h12]
  have hRHSbound : ENNReal.ofReal (Λ ^ 2 + A / 2 + ε.toReal)
      = ENNReal.ofReal (Λ ^ 2) + (1 / 2 : ENNReal) * ENNReal.ofReal A + ε := by
    rw [ENNReal.ofReal_add (add_nonneg (sq_nonneg Λ) (by linarith [hAnn])) he.le,
      ENNReal.ofReal_add (sq_nonneg Λ) (by linarith [hAnn]),
      ENNReal.ofReal_toReal hεtop, hA2]
  show (∫⁻ u in Set.Icc (0 : Real) W, ENNReal.ofReal
      (((∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ^ 2) ∂volume)
      * (ENNReal.ofReal W)⁻¹
    ≤ ENNReal.ofReal ((Pi (Set.Icc δ 1)).toReal ^ 2) + (1 / 2 : ENNReal)
      * ENNReal.ofReal (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal + ε
  rw [hLHS]
  exact (ENNReal.ofReal_le_ofReal hM).trans hRHSbound.le
