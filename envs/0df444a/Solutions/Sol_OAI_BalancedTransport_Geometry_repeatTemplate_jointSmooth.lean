-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.repeatTemplate_jointSmooth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:51:18.418976+00:00
-- url     : https://prove2.me/submissions/12c7ae14-ec9b-4550-8f8c-b91b508f3f1c

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology NNReal
open Filter Set
theorem h45_rep_eq {v : Velocity} (hc : TimeCollars v) {t : ℝ} {n : ℤ}
    (ht : t - n ∈ Ioo (-1 / 4 : ℝ) (5 / 4)) (x : Space) :
    repeatTemplate v t x = v (t - n) x := by
  unfold repeatTemplate
  rw [tsum_eq_single n]
  intro m hm
  obtain ⟨h1, h2⟩ := ht
  rcases lt_or_gt_of_ne hm with h | h
  · have h3 : (m:ℝ) ≤ n - 1 := by
      have := Int.le_sub_one_of_lt h
      exact_mod_cast this
    rw [hc (t - m) (Or.inr (by linarith))]; rfl
  · have h3 : (n:ℝ) + 1 ≤ m := by
      have := Int.add_one_le_of_lt h
      exact_mod_cast this
    rw [hc (t - m) (Or.inl (by linarith))]; rfl

theorem solution {v : Velocity} (hv : JointSmooth v) (hc : TimeCollars v) :
    JointSmooth (repeatTemplate v) := by
  unfold JointSmooth
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t0, x0⟩
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => Function.uncurry v (p.1 - (⌊t0⌋ : ℝ), p.2)) :=
    hv.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  apply hsm.contDiffAt.congr_of_eventuallyEq
  have hU : {p : ℝ × Space | t0 - 1/4 < p.1 ∧ p.1 < t0 + 1/4} ∈ 𝓝 (t0, x0) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
    · simp only [Set.mem_setOf_eq]; constructor <;> linarith
  filter_upwards [hU] with p hp
  obtain ⟨p1, p2⟩ := p
  simp only [Function.uncurry_apply_pair]
  apply h45_rep_eq hc
  have := Int.floor_le t0
  have := Int.lt_floor_add_one t0
  simp only [Set.mem_setOf_eq] at hp
  constructor <;> linarith [hp.1, hp.2]

