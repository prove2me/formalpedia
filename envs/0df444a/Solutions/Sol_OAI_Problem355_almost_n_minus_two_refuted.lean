-- Prove2me | solution 1 for OAI.Problem355.almost_n_minus_two_refuted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T01:03:48.064509+00:00
-- url     : https://prove2.me/submissions/d34957eb-7354-4d0c-a87b-0f6dc5b05a6d

import Mathlib
import Definitions.Def_HeilbronnTriangle
import Definitions.Def_OAIQWHT000
import Theorems.Thm_OAI_Problem355_heilbronn_power_lower_bound

section
-- module Solutions.OAIQW_Problem355.PowerGap
attribute [-instance] _root_.OAI.Problem355.AffineTripleOrbit.affineTupleMulAction _root_.OAI.Problem355.AffineTripleOrbit.linearTupleMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

theorem eventually_mul_rpow_lt_rpow {n : ℕ → ℕ}
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ j in Filter.atTop,
      C * Real.rpow (n j : ℝ) a < Real.rpow (n j : ℝ) b := by
  simp only [Real.rpow_eq_pow]
  have hnR : Filter.Tendsto (fun j => (n j : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hp := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp hnR
  filter_upwards [hp.eventually (Filter.eventually_gt_atTop C),
    hn.eventually (Filter.eventually_ge_atTop 1)] with j hj hjn
  have hpos : 0 < (n j : ℝ) := by exact_mod_cast (show 0 < n j by omega)
  have hpowpos : 0 < Real.rpow (n j : ℝ) a := Real.rpow_pos_of_pos hpos a
  calc
    C * Real.rpow (n j : ℝ) a <
        Real.rpow (n j : ℝ) (b - a) * Real.rpow (n j : ℝ) a :=
      mul_lt_mul_of_pos_right hj hpowpos
    _ = Real.rpow (n j : ℝ) b := by
      simpa only [Real.rpow_eq_pow, sub_add_cancel] using (Real.rpow_add hpos (b - a) a).symm

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.Refutation
attribute [-instance] _root_.OAI.Problem355.AffineTripleOrbit.affineTupleMulAction _root_.OAI.Problem355.AffineTripleOrbit.linearTupleMulAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Problem355

theorem not_eventualAlmostUpperBound_of_sequence
    {c epsilon : ℝ} (he : epsilon < c)
    {n : ℕ → ℕ} {P : ℕ → Finset Point}
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    (hP : ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
      triangleAreasAtLeast (P j) (Real.rpow (n j : ℝ) (-2 + c))) :
    ¬ eventualAlmostUpperBound epsilon := by
  rintro ⟨C, hC, n0, hupper⟩
  have hgap := eventually_mul_rpow_lt_rpow hn
    (show (-2 + epsilon : ℝ) < -2 + c by linarith) C
  obtain ⟨j, hjgap, hjn⟩ :=
    (hgap.and (hn.eventually (Filter.eventually_ge_atTop n0))).exists
  obtain ⟨hn3, hcard, hsquare, hlower⟩ := hP j
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, harea⟩ :=
    hupper (n j) hjn hn3 (P j) hcard hsquare
  exact (not_lt_of_ge ((hlower p hp q hq r hr hpq hpr hqr).trans harea)) hjgap

end Problem355

end OAI
end

section
-- module Solutions.OAIQW_Problem355.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355

theorem almost_n_minus_two_refuted_oai :
    0 < heilbronnExponent / 2 ∧ ¬ eventualAlmostUpperBound (heilbronnExponent / 2) := by
  obtain ⟨hc, n, P, hn, hP⟩ := heilbronn_power_lower_bound
  exact ⟨by positivity,
    not_eventualAlmostUpperBound_of_sequence (by linarith) hn hP⟩

end Problem355

end

end OAI
end

theorem solution : type_of% @OAI.Problem355.almost_n_minus_two_refuted_oai := @OAI.Problem355.almost_n_minus_two_refuted_oai
