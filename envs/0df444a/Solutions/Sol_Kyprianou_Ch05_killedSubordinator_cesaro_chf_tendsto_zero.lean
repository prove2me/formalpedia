-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_cesaro_chf_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T04:20:00.500341+00:00
-- url     : https://prove2.me/submissions/327581b3-00ae-422d-9d5d-d880fa47c541
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cesaro_sublevel_density
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
    ∀ t : NNReal, 0 < t → ∀ ε : ENNReal, 0 < ε →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U → (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal))) * (ENNReal.ofReal U)⁻¹ ≤ ε) := by
  intro hPi t ht ε hε
  by_cases hεtop : ε = ⊤
  · subst hεtop
    exact ⟨0, fun U _ => le_top⟩
  have htR : (0 : Real) < (t : Real) := by exact_mod_cast ht
  have hε2lt : ε / 2 < ⊤ := lt_of_le_of_lt ENNReal.half_le_self (lt_top_iff_ne_top.mpr hεtop)
  have hε2top : ε / 2 ≠ ⊤ := ne_of_lt hε2lt
  have hδ : (0 : Real) < (ε / 2).toReal :=
    ENNReal.toReal_pos (ENNReal.half_pos hε.ne').ne' hε2top
  have hlim : Tendsto (fun K : Real => Real.exp (-(2 * (t : Real) * K))) atTop (nhds 0) := by
    have h1 : Tendsto (fun K : Real => K * (2 * (t : Real))) atTop atTop :=
      Tendsto.atTop_mul_const (by linarith : (0 : Real) < 2 * (t : Real)) tendsto_id
    have h1' : Tendsto (fun K : Real => 2 * (t : Real) * K) atTop atTop :=
      h1.congr (fun K => mul_comm _ _)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1'
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hδ))
  set K : Real := max K0 0 with hKdef
  have hKexp : Real.exp (-(2 * (t : Real) * K)) < (ε / 2).toReal := hK0 K (le_max_left K0 0)
  have hc : ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) ≤ ε / 2 := by
    have h1 : Real.exp (-2 * (t : Real) * K) ≤ (ε / 2).toReal := by
      have hrw : -(2 * (t : Real) * K) = -2 * (t : Real) * K := by ring
      rw [hrw] at hKexp
      exact le_of_lt hKexp
    calc ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) ≤ ENNReal.ofReal ((ε / 2).toReal) := ENNReal.ofReal_le_ofReal h1
    _ = ε / 2 := ENNReal.ofReal_toReal hε2top
  obtain ⟨U0, hU0⟩ := Kyprianou.Ch05.killedSubordinator_cesaro_sublevel_density
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi K (ε / 2)
    (ENNReal.half_pos hε.ne')
  have hpt : ∀ u : Real, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)) ≤ ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) + ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) := by
    intro u
    by_cases h : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K
    · rw [if_pos h]
      have hnn : (0 : Real) ≤ (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal := ENNReal.toReal_nonneg
      have hexp : Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ≤ 1 := by
        have h2 : Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) ≤ Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          have h1 : -2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal = -(2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal) := by ring
          rw [h1]
          exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) htR.le) hnn)
        rwa [Real.exp_zero] at h2
      calc ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hexp
      _ ≤ ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) + ENNReal.ofReal 1 := le_add_self
    · rw [if_neg h]
      simp only [ENNReal.ofReal_zero, add_zero]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hKR : K ≤ (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal := (not_le.mp h).le
      exact mul_le_mul_of_nonpos_left hKR (by linarith [htR.le] : -2 * (t : Real) ≤ 0)
  refine ⟨max U0 1, fun U hU => ?_⟩
  have hUge : U0 ≤ U := (le_max_left U0 1).trans hU
  have hU1 : (1 : Real) ≤ U := (le_max_right U0 1).trans hU
  have hUpos : (0 : Real) < U := lt_of_lt_of_le one_pos hU1
  have hchild := hU0 U hUge
  have hInt : (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)))
      ≤ ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) * ENNReal.ofReal U + (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0)) := by
    calc (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)))
        ≤ ∫⁻ u in Set.Icc (0 : Real) U, (ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) + ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0)) := lintegral_mono hpt
    _ = (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)))
          + ∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0) :=
        lintegral_add_left measurable_const _
    _ = ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) * ENNReal.ofReal U + (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0)) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  calc (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal))) * (ENNReal.ofReal U)⁻¹
      ≤ (ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) * ENNReal.ofReal U + (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0)))
          * (ENNReal.ofReal U)⁻¹ := mul_le_mul hInt le_rfl bot_le bot_le
  _ = ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) * ENNReal.ofReal U * (ENNReal.ofReal U)⁻¹
        + (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal ≤ K then (1 : Real) else 0)) * (ENNReal.ofReal U)⁻¹ := add_mul _ _ _
  _ ≤ ε / 2 + ε / 2 := by
      apply add_le_add _ hchild
      have hne : ENNReal.ofReal U ≠ 0 := (ENNReal.ofReal_pos.mpr hUpos).ne'
      have hnet : ENNReal.ofReal U ≠ ⊤ := ENNReal.ofReal_ne_top
      calc ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) * ENNReal.ofReal U * (ENNReal.ofReal U)⁻¹
          = ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) * (ENNReal.ofReal U * (ENNReal.ofReal U)⁻¹) := mul_assoc _ _ _
      _ = ENNReal.ofReal (Real.exp (-2 * (t : Real) * K)) := by rw [ENNReal.mul_inv_cancel hne hnet, mul_one]
      _ ≤ ε / 2 := hc
  _ = ε := ENNReal.add_halves ε
