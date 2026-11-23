-- Prove2me | solution 1 for Kyprianou.Ch01.independentProductPMFSumLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:28:54.976711+00:00
-- url     : https://prove2.me/submissions/bec236b2-e5e8-4acd-b1e8-51da2c31c4bb

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_measurableProductPMFSumLaw
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (f g : Ω → ℕ)
    (hf : AEMeasurable f Q) (hg : AEMeasurable g Q)
    (p q : PMF ℕ)
    (hp : ∀ n : ℕ, Q {ω | f ω = n} = p n)
    (hq : ∀ n : ℕ, Q {ω | g ω = n} = q n)
    (k : ℕ) :
    (Q.prod Q) {z : Ω × Ω | f z.1 + g z.2 = k} =
      ((p.bind (fun n => q.map (fun m => n + m))) k) := by
  let F : Ω → ℕ := hf.mk f
  let G : Ω → ℕ := hg.mk g
  have hF : (fun z : Ω × Ω => f z.1) =ᵐ[Q.prod Q]
      (fun z : Ω × Ω => F z.1) := by
    simpa only [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := Q) (ν := Q)).ae_eq_comp
        (hf.ae_eq_mk)
  have hG : (fun z : Ω × Ω => g z.2) =ᵐ[Q.prod Q]
      (fun z : Ω × Ω => G z.2) := by
    simpa only [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := Q) (ν := Q)).ae_eq_comp
        (hg.ae_eq_mk)
  have hProd : (Q.prod Q) {z : Ω × Ω | f z.1 + g z.2 = k} =
      (Q.prod Q) {z : Ω × Ω | F z.1 + G z.2 = k} := by
    apply measure_congr
    filter_upwards [hF, hG] with z hfz hgz
    change (f z.1 + g z.2 = k) = (F z.1 + G z.2 = k)
    rw [hfz, hgz]
  have hpF (n : ℕ) : Q {ω | F ω = n} = p n := by
    calc
      Q {ω | F ω = n} = Q {ω | f ω = n} := by
        apply measure_congr
        filter_upwards [hf.ae_eq_mk] with ω hw
        change (F ω = n) = (f ω = n)
        rw [hw]
      _ = p n := hp n
  have hqG (n : ℕ) : Q {ω | G ω = n} = q n := by
    calc
      Q {ω | G ω = n} = Q {ω | g ω = n} := by
        apply measure_congr
        filter_upwards [hg.ae_eq_mk] with ω hw
        change (G ω = n) = (g ω = n)
        rw [hw]
      _ = q n := hq n
  rw [hProd]
  exact Kyprianou.Ch01.measurableProductPMFSumLaw
    Q F G hf.measurable_mk hg.measurable_mk p q hpF hqG k
