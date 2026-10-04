-- Prove2me | solution 1 for MDPFinance.Contracting.lemma_7_1_4
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:23:46.95714+00:00
-- url     : https://prove2.me/submissions/f48736bb-a638-4965-9492-95c10ef6261c

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory MDPFinance.Contracting

namespace L714Cex

noncomputable def μ0 : Measure ℤ :=
  Measure.sum fun k : ℕ => ((2 : ENNReal)⁻¹ ^ (k + 1)) • Measure.dirac (-((k : ℤ) + 1))

theorem μ0_univ : μ0 Set.univ = 1 := by
  unfold μ0
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [show (fun k : ℕ => (2 : ENNReal)⁻¹ ^ (k + 1)) = fun k => 2⁻¹ * 2⁻¹ ^ k by
    funext k; rw [pow_succ, mul_comm]]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

noncomputable def Qf (p : ℤ × Unit) : Measure ℤ :=
  if p.1 = 0 then μ0 else Measure.dirac |p.1|

instance (p : ℤ × Unit) : IsProbabilityMeasure (Qf p) := by
  unfold Qf
  split_ifs
  · exact ⟨μ0_univ⟩
  · infer_instance

noncomputable def rr (p : ℤ × Unit) : ℝ :=
  if p.1 < 0 then -(4 : ℝ) ^ p.1.natAbs else (4 : ℝ) ^ p.1.natAbs - (if p.1 = 0 then 1 else 0)

noncomputable def M0 : MarkovDecisionModel ℤ Unit where
  D := Set.univ
  hD_meas := MeasurableSet.univ
  hD_graph := ⟨fun _ => (), measurable_const, fun _ => Set.mem_univ _⟩
  Q := ⟨Qf, Measurable.of_discrete⟩
  isMarkovQ := ⟨fun p => (inferInstance : IsProbabilityMeasure (Qf p))⟩
  r := rr
  hr_meas := Measurable.of_discrete
  β := 1
  hβ0 := one_pos
  hβ1 := le_rfl

theorem Q_apply (p : ℤ × Unit) : M0.Q p = Qf p := rfl

theorem eI_dirac (y : ℤ) (w : ℤ → EReal) : erealIntegral (Measure.dirac y) w = w y := by
  unfold erealIntegral
  rw [lintegral_dirac, lintegral_dirac]
  generalize w y = z
  induction z using EReal.rec with
  | bot => simp
  | top => simp
  | coe t =>
    rw [← EReal.coe_neg]
    have h1 : (((t : EReal) ⊔ 0).toENNReal : EReal) = ((max t 0 : ℝ) : EReal) := by
      rcases le_total t 0 with h | h
      · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
      · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
        simp [EReal.coe_ennreal_ofReal, h]
    have h2 : ((((-t : ℝ) : EReal) ⊔ 0).toENNReal : EReal) = ((max (-t) 0 : ℝ) : EReal) := by
      rcases le_total (-t) 0 with h | h
      · rw [sup_eq_right.mpr (by exact_mod_cast h), max_eq_right h]; simp
      · rw [sup_eq_left.mpr (by exact_mod_cast h), max_eq_left h]
        simp [EReal.coe_ennreal_ofReal, h]
    rw [h1, h2, ← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    rcases le_total t 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

theorem lint_μ0 (f : ℤ → ENNReal) :
    ∫⁻ z, f z ∂μ0 = ∑' k : ℕ, (2 : ENNReal)⁻¹ ^ (k + 1) * f (-((k : ℤ) + 1)) := by
  unfold μ0
  rw [lintegral_sum_measure]
  congr 1
  funext k
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

def π0 : ℕ → ℤ → Unit := fun _ _ => ()

theorem J1 (y : ℤ) : Jnpi M0 M0.r π0 1 y = (rr (y, ()) : EReal) := by
  show (rr (y, ()) : EReal) + ((1 : ℝ) : EReal) * erealIntegral (M0.Q (y, ())) (fun _ => 0) = _
  unfold erealIntegral
  simp

theorem J2_neg (k : ℕ) : Jnpi M0 M0.r π0 2 (-((k : ℤ) + 1)) = 0 := by
  show (rr (-((k : ℤ) + 1), ()) : EReal) + ((1 : ℝ) : EReal) *
    erealIntegral (M0.Q (-((k : ℤ) + 1), ())) (Jnpi M0 M0.r π0 1) = 0
  have hq : M0.Q (-((k : ℤ) + 1), ()) = Measure.dirac ((k : ℤ) + 1) := by
    rw [Q_apply]; unfold Qf
    rw [if_neg (by omega)]
    congr 1
  rw [hq, eI_dirac, J1]
  have h1 : rr (-((k : ℤ) + 1), ()) = -(4 : ℝ) ^ (k + 1) := by
    unfold rr
    rw [if_pos (by simp; omega)]
    congr 2
  have h2 : rr ((k : ℤ) + 1, ()) = (4 : ℝ) ^ (k + 1) := by
    unfold rr
    rw [if_neg (by omega), if_neg (by omega), sub_zero]
    congr 1
  rw [h1, h2, EReal.coe_one, one_mul, ← EReal.coe_add]
  simp

theorem J2_zero : Jnpi M0 M0.r π0 2 0 = ⊥ := by
  show (rr (0, ()) : EReal) + ((1 : ℝ) : EReal) * erealIntegral (M0.Q (0, ()))
    (Jnpi M0 M0.r π0 1) = ⊥
  have hq : M0.Q (0, ()) = μ0 := by rw [Q_apply]; unfold Qf; simp
  rw [hq]
  have hneg : ∫⁻ z, ((-Jnpi M0 M0.r π0 1 z) ⊔ 0).toENNReal ∂μ0 = ⊤ := by
    rw [lint_μ0]
    refine top_unique (le_trans (le_of_eq (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm)
      (ENNReal.tsum_le_tsum fun k => ?_))
    rw [J1]
    have h1 : rr (-((k : ℤ) + 1), ()) = -(4 : ℝ) ^ (k + 1) := by
      unfold rr
      rw [if_pos (by simp; omega)]
      congr 2
    rw [h1, ← EReal.coe_neg, neg_neg]
    rw [sup_eq_left.mpr (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 4 ^ (k + 1)))]
    rw [EReal.real_coe_toENNReal, ENNReal.ofReal_pow (by norm_num), ← mul_pow]
    have : (2 : ENNReal)⁻¹ * ENNReal.ofReal 4 = 2 := by
      rw [show ENNReal.ofReal 4 = 2 * 2 by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num)]; simp]
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    rw [this]
    exact one_le_pow₀ (by norm_num)
  unfold erealIntegral
  rw [hneg]
  simp [EReal.coe_mul_bot_of_pos]

theorem J3_zero : Jnpi M0 M0.r π0 3 0 = 0 := by
  show (rr (0, ()) : EReal) + ((1 : ℝ) : EReal) * erealIntegral (M0.Q (0, ()))
    (Jnpi M0 M0.r π0 2) = 0
  have hq : M0.Q (0, ()) = μ0 := by rw [Q_apply]; unfold Qf; simp
  rw [hq]
  unfold erealIntegral
  rw [lint_μ0, lint_μ0]
  simp only [J2_neg]
  simp [rr]

end L714Cex

open L714Cex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A)
    (π : ℕ → E → A) (hπ : IsPolicyOf M π) (n m : ℕ) (hnm : m ≤ n) (x : E),
    Jnpi M M.r π n x ≤ Jnpi M M.r π m x + (Tcirc M)^[m] (delta M) x ∧
      Jn M M.r n x ≤ Jn M M.r m x + (Tcirc M)^[m] (delta M) x) := by
  intro h
  have H := (h M0 π0 (fun _ => ⟨measurable_const, fun _ => Set.mem_univ _⟩) 3 2 (by norm_num) 0).1
  rw [J3_zero, J2_zero, EReal.bot_add] at H
  exact absurd H (by simp)

#print axioms solution
