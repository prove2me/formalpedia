-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T09:27:23.67438+00:00
-- url     : https://prove2.me/submissions/382bbcf1-8ebd-4d44-842d-44205bbf1d10

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cesaro_sublevel_density_restricted
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

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
    ∀ K : Real, ∀ ρ : ENNReal, 0 < ρ →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U → (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ) := by
  intro hPi K ρ hρ
  -- Finiteness of the full exponent integral, from the triplet's Lévy
  -- integrability field: 1 - cos (u * y) ≤ max 2 |u| * min 1 y on (0, ∞).
  have hfin : ∀ u : Real, (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi) ≠ ⊤ := by
    intro u
    obtain ⟨-, -, -, hmin, -⟩ := hTriplet
    have hC2 : (2 : Real) ≤ max 2 |u| := le_max_left _ _
    have hCu : |u| ≤ max 2 |u| := le_max_right _ _
    have hCnn : (0 : Real) ≤ max 2 |u| := le_trans (by norm_num) hC2
    have hpt : ∀ y ∈ Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y))
        ≤ ENNReal.ofReal (max 2 |u|) * ENNReal.ofReal (min 1 y) := by
      intro y hy
      have hy0 : (0 : Real) < y := hy
      have hbound : 1 - Real.cos (u * y) ≤ max 2 |u| * min 1 y := by
        have hcos : 1 - Real.cos (u * y) ≤ |u| * y := by
          have hLip := Real.lipschitzWith_cos.dist_le_mul (u * y) 0
          simp only [Real.cos_zero, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at hLip
          calc 1 - Real.cos (u * y) ≤ |Real.cos (u * y) - 1| :=
              (le_abs_self _).trans_eq (abs_sub_comm 1 (Real.cos (u * y)))
          _ ≤ |u * y| := hLip
          _ = |u| * y := by rw [abs_mul, abs_of_pos hy0]
        by_cases hy1 : y ≤ 1
        · rw [min_eq_right hy1]
          exact hcos.trans (mul_le_mul_of_nonneg_right hCu hy0.le)
        · push_neg at hy1
          rw [min_eq_left hy1.le, mul_one]
          have h2 : 1 - Real.cos (u * y) ≤ 2 := by
            have hcc := Real.cos_le_one (u * y)
            have hcc2 := Real.neg_one_le_cos (u * y)
            linarith
          exact h2.trans hC2
      exact (ENNReal.ofReal_le_ofReal hbound).trans_eq (ENNReal.ofReal_mul hCnn)
    have h1 : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
        ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (max 2 |u|) * ENNReal.ofReal (min 1 y) ∂Pi := by
      refine MeasureTheory.lintegral_mono_ae ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      exact Filter.Eventually.of_forall hpt
    have h2 : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (max 2 |u|) * ENNReal.ofReal (min 1 y) ∂Pi)
        = ENNReal.ofReal (max 2 |u|) * ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
      MeasureTheory.lintegral_const_mul _
        (ENNReal.measurable_ofReal.comp (continuous_const.min continuous_id).measurable)
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt hmin)) (h1.trans_eq h2)
  obtain ⟨δ, hδpos, -, U0, hU0⟩ :=
    Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density_restricted
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi K ρ hρ
  refine ⟨U0, fun U hU => ?_⟩
  have hchild := hU0 U hU
  refine le_trans ?_ hchild
  refine mul_le_mul ?_ le_rfl bot_le bot_le
  refine lintegral_mono fun u => ?_
  by_cases h : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K
  · have hle : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi)
        ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi :=
      MeasureTheory.lintegral_mono_set (fun y hy => hδpos.trans_le hy.1)
    have hrK : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K :=
      (ENNReal.toReal_mono (hfin u) hle).trans h
    rw [if_pos h, if_pos hrK]
  · rw [if_neg h, ENNReal.ofReal_zero]
    exact bot_le
