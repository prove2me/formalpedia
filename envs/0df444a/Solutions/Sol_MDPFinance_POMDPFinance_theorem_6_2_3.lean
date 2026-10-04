-- Prove2me | solution 1 for MDPFinance.POMDPFinance.theorem_6_2_3
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:14:20.88333+00:00
-- url     : https://prove2.me/submissions/0bb70645-54b5-4f31-a5c5-37955de28e72

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_MeanVariance

open MeasureTheory ProbabilityTheory MDPFinance.POMDPFinance

namespace POMVCex

def z2 : Fin 1 → ℝ := fun _ => 2
def z0 : Fin 1 → ℝ := fun _ => 0

noncomputable def lam0 : Measure (Fin 1 → ℝ) :=
  (1 / 2 : ENNReal) • Measure.dirac z2 + (1 / 2 : ENNReal) • Measure.dirac z0

theorem lam0_univ : lam0 Set.univ = 1 := by
  simp [lam0, ENNReal.inv_two_add_inv_two]

instance : IsProbabilityMeasure lam0 := ⟨lam0_univ⟩

theorem int_lam0 (f : (Fin 1 → ℝ) → ℝ) : ∫ z, f z ∂lam0 = 1 / 2 * f z2 + 1 / 2 * f z0 := by
  unfold lam0
  rw [integral_add_measure (Integrable.smul_measure (integrable_dirac (by simp)) (by simp))
      (Integrable.smul_measure (integrable_dirac (by simp)) (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp

noncomputable def M0 : FilterMarket Unit 1 where
  lam := lam0
  hlam_sigmaFinite := inferInstance
  qR := fun _ _ => 1
  hqR_meas := measurable_const
  hqR_nonneg := fun _ _ => zero_le_one
  hqR_prob := fun _ => by simp
  hqR_supp := fun _ => by
    simp only [ENNReal.ofReal_one]
    rw [show (fun _ : Fin 1 → ℝ => (1 : ENNReal)) = 1 from rfl, withDensity_one]
    unfold lam0
    rw [ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_iff (by measurability)]; intro j; simp [z2]; norm_num
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_iff (by measurability)]; intro j; simp [z0]
  QY := Kernel.const _ (Measure.dirac ())
  isMarkovQY := inferInstance
  Q0 := Measure.dirac ()
  isProbQ0 := inferInstance

theorem law_eq (y : Unit) : M0.law y = lam0 := by
  simp [FilterMarket.law, M0]

noncomputable def Fd0 : FilterOp M0 where
  Phi := fun _ _ => Measure.dirac ()
  hPhi_prob := fun _ _ _ => inferInstance
  hPhi_meas := measurable_const
  hPhi := fun ρ z h0 htop C hC => by
    simp only [M0, ENNReal.ofReal_one, one_mul, Kernel.const_apply, lintegral_const] at h0 htop ⊢
    rw [ENNReal.mul_div_cancel_right h0.ne' htop.ne]

noncomputable def Mv0 : MeanVarianceMarket M0 where
  i := fun _ => 0
  hi_pos := fun _ => by norm_num
  hmom1 := ⟨∫⁻ z, ‖z‖ₑ ∂lam0, by
      unfold lam0
      simp [lintegral_add_measure, ENNReal.mul_lt_top, enorm_lt_top],
    fun y => by rw [law_eq]⟩
  hmom2 := fun y => by
    rw [law_eq]
    unfold lam0
    simp [lintegral_add_measure, ENNReal.mul_lt_top, enorm_lt_top]
  hmean := ⟨0, Or.inl fun y => by rw [law_eq, int_lam0]; simp [z2, z0]⟩
  hcov := fun y => by
    have e : (Matrix.of fun j k : Fin 1 =>
        ∫ z, (z j - ∫ w, w j ∂(M0.law y)) * (z k - ∫ w, w k ∂(M0.law y)) ∂(M0.law y)) =
        Matrix.diagonal (fun _ => (1 : ℝ)) := by
      ext j k
      fin_cases j; fin_cases k
      simp only [law_eq, int_lam0]
      simp [z2, z0]
      norm_num
    rw [e]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => one_pos)

end POMVCex

open POMVCex in
theorem solution : ¬ (∀ {EY : Type} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mv : MeanVarianceMarket M) (N : ℕ) (x0 μ : ℝ)
    (hμ : x0 * S0 Mv.i N < μ),
    (let fs : ℕ → ℝ × Measure EY → Fin d → ℝ := fun n xρ =>
        ((μ - dRem M Fd N M.Q0 * x0 * S0 Mv.i N) / (1 - dRem M Fd N M.Q0) *
              (S0 Mv.i n / S0 Mv.i N) - xρ.1) •
          (CRem M Fd (N - n - 1) xρ.2)⁻¹.mulVec (lRem M Fd (N - n - 1) xρ.2)
      let pistar := ofMarkov M Fd Mv.i x0 fs
      EXN M Fd Mv.i pistar N x0 = (μ : EReal) ∧
        IsMVFeasible M Fd Mv.i N x0 μ pistar ∧
        VarPi M Fd Mv.i pistar N x0 =
          ((dRem M Fd N M.Q0 / (1 - dRem M Fd N M.Q0) * (μ - x0 * S0 Mv.i N) ^ 2 : ℝ) : EReal) ∧
        VarMV M Fd Mv.i N x0 μ =
          ((dRem M Fd N M.Q0 / (1 - dRem M Fd N M.Q0) * (μ - x0 * S0 Mv.i N) ^ 2 : ℝ) : EReal) ∧
        VarPi M Fd Mv.i pistar N x0 = VarMV M Fd Mv.i N x0 μ)) := by
  intro h
  have H := (h M0 Fd0 Mv0 0 0 1 (by simp [S0])).1
  simp only [EXN, Vpi, id] at H
  norm_num at H

#print axioms solution
