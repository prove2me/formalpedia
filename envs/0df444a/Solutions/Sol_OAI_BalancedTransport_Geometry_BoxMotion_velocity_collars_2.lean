-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.BoxMotion.velocity_collars
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:49:29.252467+00:00
-- url     : https://prove2.me/submissions/8c331fec-c3df-4e74-bc97-9d2f821edddd

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MotionField.lean:L181-L202
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.BoxMotion.velocity_collars. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem movingBoxVelocity_zero {a b : Space} {c d : ℝ → Space} {η t : ℝ}
    (hc : deriv c t = 0) (hd : ∀ i, deriv (fun s => d s i) t = 0) :
    movingBoxVelocity a b c d η t = 0 := by
  have hl : logarithmicRate d t = 0 := by ext i; simp [logarithmicRate, hd]
  simp [movingBoxVelocity, hc, hl]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompactFamilies ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

lemma familyVelocity_zero {a b : ι → Space} {c d : ι → ℝ → Space} {η t : ℝ}
    (hc : ∀ i, deriv (c i) t = 0) (hd : ∀ i j, deriv (fun s => d i s j) t = 0) :
    familyVelocity a b c d η t = 0 := by
  ext x j
  simp [familyVelocity, movingBoxVelocity_zero (hc _) (hd _)]

end BalancedTransport.Geometry
end

end OAI

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

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma fieldCenter_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldCenter i t = A.center i := by
  unfold fieldCenter
  rw [m.start_center _ (by linarith)]

lemma fieldScale_before (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : t ≤ 1 / 4) :
    m.fieldScale i t = 1 := by
  ext k
  change m.width (2 * t - 1 / 2) i k / A.width i k = 1
  rw [m.start_width _ (by linarith), div_self (m.positive_start i k).ne']

lemma fieldCenter_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldCenter i t = B.center i := by
  unfold fieldCenter
  rw [m.end_center _ (by linarith)]

lemma fieldScale_after (m : BoxMotion A B safe η) (i : ι) {t : ℝ} (ht : 3 / 4 ≤ t) :
    m.fieldScale i t = fun k => B.width i k / A.width i k := by
  unfold fieldScale
  rw [m.end_width _ (by linarith)]

lemma velocity_collars (m : BoxMotion A B safe η) : TimeCollars m.velocity := by
  intro t ht
  apply familyVelocity_zero
  · intro i
    rcases ht with ht | ht
    · have he : m.fieldCenter i =ᶠ[𝓝 t] fun _ => A.center i := by
        filter_upwards [Iio_mem_nhds ht] with s hs using m.fieldCenter_before i hs.le
      rw [he.deriv_eq, deriv_const]
    · have he : m.fieldCenter i =ᶠ[𝓝 t] fun _ => B.center i := by
        filter_upwards [Ioi_mem_nhds ht] with s hs using m.fieldCenter_after i hs.le
      rw [he.deriv_eq, deriv_const]
  · intro i k
    rcases ht with ht | ht
    · have he : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        rw [m.fieldScale_before i hs.le]
        rfl
      rw [he.deriv_eq, deriv_const]
    · have he : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => B.width i k / A.width i k := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        rw [m.fieldScale_after i hs.le]
      rw [he.deriv_eq, deriv_const]

end BalancedTransport.Geometry.BoxMotion
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry OAI.BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.BoxMotion.velocity_collars := @_root_.OAI.BalancedTransport.Geometry.BoxMotion.velocity_collars
