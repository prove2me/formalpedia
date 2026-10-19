-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.loadingSupport_ball
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:01:01.424746+00:00
-- url     : https://prove2.me/submissions/f3b2d0a6-59d1-48dc-8728-7180f0b83b64

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ComputableInitial.lean:L82-L95
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.loadingSupport_ball. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.ComputableInitial ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Recorder Coding BalancedTransport.Geometry
open scoped Classical

lemma fixedLabel_bound (i : Fin 3) : |fixedLabel i| ≤ (4 : ℝ) := by
  fin_cases i <;> norm_num [fixedLabel]

lemma loadingSupport_ball {z : Space} {C : ℕ} (hz : ∀i, |z i| ≤ C) :
    loadingSupport z 1 ⊆ Metric.closedBall (0 : Space) (C+6 : ℕ) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hh := (mem_closedEnlargement _ _ _ x).mp hx i
  have h₀ := (abs_le.mp (fixedLabel_bound i))
  have hz' := abs_le.mp (hz i)
  have hlo : -(C : ℝ)-4 ≤ min (fixedLabel i) (z i) := le_min (by linarith) (by linarith)
  have hhi : max (fixedLabel i) (z i) ≤ (C : ℝ)+4 := max_le (by linarith) (by linarith)
  push_cast
  constructor <;> linarith [hh.1,hh.2]

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Recorder Coding BalancedTransport.Geometry
open scoped Classical


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.loadingSupport_ball := @_root_.OAI.BalancedTransport.Effectivity.loadingSupport_ball
