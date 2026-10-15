-- Prove2me | solution 1 for HunterPDE.Sobolev.morrey
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T21:40:23.211173+00:00
-- url     : https://prove2.me/submissions/1b9625cc-d3c7-403f-9e0c-bb1cca198907

import Theorems.Thm_HunterPDE_Sobolev_morrey_increment
import Theorems.Thm_MeasureTheory_enorm_const_le_of_ae_sub_le
import Theorems.Thm_HunterPDE_Sobolev_gradient_eLpNorm_le_sobolevNorm
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_zero_ae_eq
import Definitions.Def_HunterPDE_Shared_HolderSeminorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

open MeasureTheory HunterPDE.Sobolev

theorem solution {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
        HunterPDE.Shared.holderSeminorm (1 - (n : ℝ) / p) Set.univ f ≤
            (C : ENNReal) * eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume ∧
          ∀ x, ENNReal.ofReal |f x| ≤
            (C : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
  classical
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hα : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hnp)
  obtain ⟨A, hA⟩ := morrey_increment hnp
  let v : ENNReal := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hv0 : v ≠ 0 := (Metric.measure_ball_pos volume _ zero_lt_one).ne'
  have hvt : v ≠ ⊤ := measure_ball_lt_top.ne
  let B : NNReal := (v ^ (1 / p))⁻¹.toNNReal
  have hB : (B : ENNReal) = (v ^ (1 / p))⁻¹ := by
    exact ENNReal.coe_toNNReal (by simp [ENNReal.inv_eq_top, ENNReal.rpow_eq_zero_iff, hv0, hvt])
  refine ⟨max A (A * n + B), ?_⟩
  intro f hf hfc
  have htest : IsTestFunction Set.univ f := ⟨hf, hfc, Set.subset_univ _⟩
  have hLp : eLpNorm f (ENNReal.ofReal p) volume ≤
      sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by
    have hl : LocallyIntegrableOn f Set.univ :=
      (hf.continuous.locallyIntegrable).locallyIntegrableOn Set.univ
    have hzpartial (φ : EuclideanSpace ℝ (Fin n) → ℝ) :
        iteratedPartial (fun _ : Fin n => 0) φ = φ := by
      simp only [iteratedPartial, Function.iterate_zero, id_eq]
      induction List.finRange n with
      | nil => rfl
      | cons i l ih => simpa only [List.foldr_cons, id_eq] using ih
    have hzero : HasWeakDeriv Set.univ (fun _ => 0) f f := by
      refine ⟨hl, hl, ?_⟩
      intro φ _
      simp [hzpartial]
    have hchosen : HasWeakDeriv Set.univ (fun _ => 0) f
        (weakDeriv Set.univ (fun _ => 0) f) := by
      unfold weakDeriv
      rw [dif_pos (show ∃ g, HasWeakDeriv Set.univ (fun _ => 0) f g from ⟨f, hzero⟩)]
      exact Exists.choose_spec _
    have hz := hchosen.zero_ae_eq isOpen_univ
    have hmem : (fun _ : Fin n => 0) ∈ multiIndices n 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨fun _ => (0 : Fin 2), Finset.mem_univ _, rfl⟩, by simp⟩
    rw [sobolevNorm, if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    have hsum := Finset.single_le_sum (s := multiIndices n 1)
      (f := fun α => eLpNorm (weakDeriv Set.univ α f) (ENNReal.ofReal p)
        (volume.restrict Set.univ) ^ p) (fun _ _ => bot_le) hmem
    have hroot := ENNReal.rpow_le_rpow hsum (by positivity : 0 ≤ 1 / p)
    simpa only [Measure.restrict_univ, eLpNorm_congr_ae (by simpa using hz),
      ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using hroot
  have hinc := hA f (hf.of_le (by simp)) hfc
  constructor
  · apply le_trans ?_ (mul_le_mul_left (show (A : ENNReal) ≤
      ((max A (A * n + B) : NNReal) : ENNReal) from by exact_mod_cast le_max_left A (A * n + B)) _)
    unfold HunterPDE.Shared.holderSeminorm
    refine iSup_le fun x => iSup_le fun _ => iSup_le fun y => iSup_le fun _ => iSup_le fun hxy => ?_
    have hd : 0 < ‖x - y‖ ^ (1 - (n : ℝ) / p) := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    rw [ENNReal.ofReal_div_of_pos hd]
    exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top).mpr (hinc x y)
  · intro x
    by_cases hn : n = 0
    · subst n
      have heq : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
      have hv : (volume : Measure (EuclideanSpace ℝ (Fin 0))) Set.univ = 1 := by
        rw [volume_euclideanSpace_eq_dirac]
        simp
      have hnorm : eLpNorm f (ENNReal.ofReal p) volume = ENNReal.ofReal |f x| := by
        rw [heq, eLpNorm_const' _ hpne ENNReal.ofReal_ne_top, hv]
        simp [Real.enorm_eq_ofReal_abs]
      have hconst : (1 : NNReal) ≤ max A (A * (0 : NNReal) + B) := by
        have hvb : v = 1 := by
          have hb : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ := by
            ext y
            simp [Subsingleton.elim y 0]
          simpa [v, hb] using hv
        have hb : B = 1 := by simp [B, hvb]
        simp [hb]
      exact (hnorm.symm ▸ hLp).trans (by simpa using mul_le_mul_left (show (1 : ENNReal) ≤ ((max A (A * (0 : NNReal) + B) : NNReal) : ENNReal) from by exact_mod_cast hconst) (sobolevNorm 1 (ENNReal.ofReal p) Set.univ f))
    · have hp1 : 1 ≤ p := le_trans (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)) hnp.le
      have he1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp1
      have hvx : (volume.restrict (Metric.ball x 1)) Set.univ = v := by
        simpa [v] using Measure.addHaar_ball_center volume x 1
      have hosci : ∀ᵐ y ∂volume.restrict (Metric.ball x 1),
          ‖f x - f y‖ₑ ≤ (A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume := by
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        have hdist : ‖x - y‖ ≤ 1 := by simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_ball.mp hy).le
        have hr : ‖x-y‖ ^ (1 - (n : ℝ) / p) ≤ 1 := Real.rpow_le_one (norm_nonneg _) hdist hα.le
        simpa [Real.enorm_eq_ofReal_abs] using (hinc x y).trans (by simpa using mul_le_mul_right (ENNReal.ofReal_le_one.mpr hr) ((A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume))
      have hpoint := MeasureTheory.enorm_const_le_of_ae_sub_le
        (volume.restrict (Metric.ball x 1)) he1 ENNReal.ofReal_ne_top
        (by simpa [hvx] using hv0) (by simpa [hvx] using hvt) f
        hf.continuous.aestronglyMeasurable (f x) _ hosci
      rw [hvx, ENNReal.toReal_ofReal hp0.le, ← hB, Real.enorm_eq_ofReal_abs] at hpoint
      have hgrad := gradient_eLpNorm_le_sobolevNorm hp1 f htest
      calc
        ENNReal.ofReal |f x| ≤ (A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume +
          (B : ENNReal) * eLpNorm f (ENNReal.ofReal p) (volume.restrict (Metric.ball x 1)) := hpoint
        _ ≤ (A : ENNReal) * ((n : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f) +
          (B : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f :=
            add_le_add (mul_le_mul_right hgrad _) (mul_le_mul_right ((eLpNorm_mono_measure f Measure.restrict_le_self).trans hLp) _)
        _ = ((A * n + B : NNReal) : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by simp [add_mul, mul_assoc]
        _ ≤ _ := mul_le_mul_left (by exact_mod_cast (le_max_right A (A * n + B))) _
