-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorOccupationIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:26:37.090132+00:00
-- url     : https://prove2.me/submissions/ab61fb49-86cf-420e-ab7d-cabf38172685

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (R f : Real → Real) (d T : Real) (hd : 0 < d) (hT : 0 ≤ T)
    (hLip : LipschitzWith (Real.toNNReal d) R) (hf : Measurable f)
    (hder : ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      deriv R t = if R t - f t = 0 then d else 0) :
    ENNReal.ofReal (R T - R 0) =
      ENNReal.ofReal d * (∫⁻ t in Icc (0 : Real) T,
        (if R t - f t = 0 then (1 : ENNReal) else 0) ∂volume) := by
  classical
  let g : Real → Real := fun t => if R t - f t = 0 then d else 0
  let mu := volume.restrict (Icc (0 : Real) T)
  have hSet : MeasurableSet {t : Real | R t - f t = 0} :=
    measurableSet_eq_fun (hLip.continuous.measurable.sub hf) measurable_const
  have hg : Measurable g := Measurable.ite hSet measurable_const measurable_const
  have hi : Integrable g mu := by
    have hc : Integrable (fun _ : Real => d) mu := integrableOn_const measure_Icc_lt_top.ne
    apply hc.mono' hg.aestronglyMeasurable
    filter_upwards with t
    dsimp [g]; split_ifs <;> simp [abs_of_nonneg hd.le, hd.le]
  have hnn : ∀ᵐ t ∂mu, 0 ≤ g t := by
    filter_upwards with t
    dsimp [g]; split_ifs <;> simp [hd.le]
  have hder' : deriv R =ᵐ[mu] g :=
    ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hder
  have hAC : AbsolutelyContinuousOnInterval R 0 T :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have he := hAC.integral_deriv_eq_sub
  rw [intervalIntegral.integral_of_le hT, restrict_Ioc_eq_restrict_Icc,
    integral_congr_ae hder'] at he
  rw [← he, ofReal_integral_eq_lintegral_ofReal hi hnn]
  have hInd : Measurable (fun t : Real => if R t - f t = 0 then (1 : ENNReal) else 0) :=
    Measurable.ite hSet measurable_const measurable_const
  rw [← lintegral_const_mul _ hInd]
  apply lintegral_congr
  intro t
  dsimp [g]; split_ifs <;> simp
