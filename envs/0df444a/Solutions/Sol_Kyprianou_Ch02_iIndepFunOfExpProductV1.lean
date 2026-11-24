-- Prove2me | solution 1 for Kyprianou.Ch02.iIndepFunOfExpProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:11:19.397708+00:00
-- url     : https://prove2.me/submissions/3c15dbe3-2dfb-49dc-be38-2fa670a522d4

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (D : Fin n → Ω → ℝ) (hm : ∀ k, AEMeasurable (D k) P)
    (hf : ∀ θ : Fin n → ℝ, (∫ ω, ∏ k : Fin n, Complex.exp ((θ k : ℂ) *
      (D k ω : ℂ) * Complex.I) ∂P) = ∏ k : Fin n, charFun (P.map (D k)) (θ k)) :
    iIndepFun D P := by
  apply (iIndepFun_iff_charFun_pi hm).2
  intro t
  rw [← hf (fun k => t k), charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with ω
  rw [← Complex.exp_sum]
  congr 1
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm, Finset.sum_mul]
  rw [Finset.mul_sum]
