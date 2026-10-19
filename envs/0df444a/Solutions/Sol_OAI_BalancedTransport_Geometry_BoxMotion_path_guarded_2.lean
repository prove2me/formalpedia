-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.BoxMotion.path_guarded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:47:45.164118+00:00
-- url     : https://prove2.me/submissions/61e0eae1-aea3-45e7-84ef-807377b08b66

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MotionField.lean:L141-L158
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.BoxMotion.path_guarded. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Motion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma positive_start (m : BoxMotion A B safe η) : A.Positive := by
  have hh := m.positive 0
  rwa [m.start_width 0 le_rfl] at hh

end BalancedTransport.Geometry.BoxMotion
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MotionField ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mem_solid {A : BoxLayout ι} {i : ι} {x : Space} : x ∈ A.solid i ↔
    ∀ k, A.center i k - A.width i k ≤ x k ∧ x k ≤ A.center i k + A.width i k := by
  simp only [solid, mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
  exact forall_and.symm

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma fieldScale_pos (m : BoxMotion A B safe η) (i : ι) (t : ℝ) (k : Fin 3) :
    0 < m.fieldScale i t k := div_pos (m.positive _ _ _) (m.positive_start _ _)

lemma lowerEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i - m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  field_simp [(m.positive_start i k).ne']
  ring

omit [Fintype ι] in
lemma reference_mem {i : ι} {x : Space} (hx : x ∈ A.solid i) :
    x - A.center i ∈ Icc (-A.width i) (A.width i) := by
  rw [BoxLayout.mem_solid] at hx
  constructor <;> intro k <;> dsimp <;> linarith [(hx k).1, (hx k).2]

lemma path_guarded (m : BoxMotion A B safe η) {i : ι} (hi : i ∈ safe)
    {x : Space} (hx : x ∈ A.solid i) (t : ℝ) : m.path i x t ∉ observer := by
  intro hobs
  have hob : m.path i x t 0 < 2 := (Set.mem_pi.mp hobs 0 (Set.mem_univ _)).2
  have hg := m.guard (2 * t - 1 / 2) i hi
  have hz := (reference_mem hx).1 0
  have hp := m.fieldScale_pos i t 0
  have hmul := mul_le_mul_of_nonneg_left hz hp.le
  change m.fieldScale i t 0 * (-A.width i 0) ≤
    m.fieldScale i t 0 * (x - A.center i) 0 at hmul
  have hlow : m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 ≤ m.path i x t 0 := by
    have he := congrFun (m.lowerEndpoint_eq i t) 0
    change m.fieldCenter i t 0 + m.fieldScale i t 0 * (-A.width i 0) =
      m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 at he
    change _ ≤ m.fieldCenter i t 0 + m.fieldScale i t 0 * (x - A.center i) 0
    rw [← he]
    linarith
  exact (lt_of_lt_of_le hg hlow).not_gt hob

end BalancedTransport.Geometry.BoxMotion
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry OAI.BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.BoxMotion.path_guarded := @_root_.OAI.BalancedTransport.Geometry.BoxMotion.path_guarded
