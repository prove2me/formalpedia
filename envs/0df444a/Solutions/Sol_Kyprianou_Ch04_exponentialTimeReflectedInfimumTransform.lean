-- Prove2me | solution 1 for Kyprianou.Ch04.exponentialTimeReflectedInfimumTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:34.92565+00:00
-- url     : https://prove2.me/submissions/8525d8df-e8ca-4ca9-8a2b-f7c187928f98

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_spectrallyNegativePsi_zero
import Theorems.Thm_Kyprianou_Ch04_independentExpClockEndpointSupJointLaw
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (expTime : Omega → NNReal)
    (heMeasurable : Measurable expTime)
    (heLaw : ∀ t : NNReal,
      (P {omega : Omega | t < expTime omega}).toReal =
        Real.exp (-q * (t : Real)))
    (heIndep :
      Indep
        (MeasurableSpace.comap expTime inferInstance)
        (MeasurableSpace.comap
          (fun omega : Omega => fun t : NNReal => L.X t omega)
          inferInstance) P) :
    ∃ phi : Real,
      0 < phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi) ∧
      (∀ beta : Real, 0 ≤ beta →
        (if beta = phi then
          (∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) ''
                Set.Iic (expTime omega)) - L.X (expTime omega) omega)) ∂P) =
            q / (phi * deriv L.ψ phi)
         else
          (∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) ''
                Set.Iic (expTime omega)) - L.X (expTime omega) omega)) ∂P) =
            (q / phi) * ((beta - phi) / (L.ψ beta - q)))) := by
  letI : IsProbabilityMeasure P := L.isProbability
  obtain ⟨phi, hphi, hr, hmax⟩ :=
    Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L hNotNegativeSubordinator q hq.le
  have hp := lt_of_le_of_ne hphi (by
    rintro rfl
    exact hq.ne' (hr.symm.trans (Kyprianou.Ch03.spectrallyNegativePsi_zero P F L)))
  obtain ⟨m, hm, hderiv, hAll⟩ :=
    avram_ws01e_bt_new_original_clock_descending_mgf_all_beta L q hq phi hp hr
  refine ⟨phi, hp, hr, hmax, ?_⟩
  intro beta hb
  obtain ⟨hd, hs, hj⟩ :=
    independentExpClockEndpointSupJointLaw P F L q hq expTime heMeasurable heLaw heIndep
  have hmeas := levy_exponential_real_clock_extrema_drawdown_measurable L
  have hJ : IdentDistrib _ _ P (P.prod (expMeasure q)) :=
    ⟨(hd.prodMk hs).aemeasurable,
      by simpa only [Pi.neg_apply, neg_sub] using
        (hmeas.snd.neg.prodMk hmeas.fst.fst).aemeasurable, hj⟩
  by_cases hz : beta = 0
  · subst beta
    simp [Ne.symm hp.ne', Kyprianou.Ch03.spectrallyNegativePsi_zero P F L]
    field_simp
  · have hpos := lt_of_le_of_ne hb (Ne.symm hz)
    let g : ℝ × ℝ → ℝ := fun z => Real.exp (beta * z.1)
    have hg : Measurable g := by fun_prop
    have hT := (hJ.comp hg).integral_eq
    have hM := hAll beta hpos
    unfold mgf at hM
    simp only [Function.comp_apply, g] at hT
    simp only [neg_sub] at hM
    have hE := hT.trans hM
    have harg : (fun x : Omega => Real.exp (beta *
        (L.X (expTime x) x - sSup ((fun s : NNReal => L.X s x) '' Set.Iic (expTime x))))) =
      (fun x : Omega => Real.exp (-beta *
        (sSup ((fun s : NNReal => L.X s x) '' Set.Iic (expTime x)) - L.X (expTime x) x))) := by
      funext x
      congr 1
      ring
    rw [harg] at hE
    by_cases h : beta = phi
    · rw [if_pos h, hderiv.deriv]
      rwa [if_pos h] at hE
    · rw [if_neg h]
      rw [if_neg h] at hE
      rw [show beta - phi = -(phi - beta) by ring,
        show L.ψ beta - q = -(q - L.ψ beta) by ring, neg_div_neg_eq]
      exact hE
