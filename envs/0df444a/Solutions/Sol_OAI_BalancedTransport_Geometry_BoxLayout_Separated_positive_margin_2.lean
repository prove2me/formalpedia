-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.BoxLayout.Separated.positive_margin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:20:46.017444+00:00
-- url     : https://prove2.me/submissions/328c1ba9-0690-43d5-b89d-050355e4b2ea

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Routing.lean:L38-L56
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.BoxLayout.Separated.positive_margin. The node keeps its source
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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Routing ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

lemma finite_positive_lower_bound {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ f i := by
  classical
  have hh : ∀ s : Finset α, ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨r, hr, h⟩ := ih
      refine ⟨min r (f a), lt_min hr (hf a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  simpa using hh Finset.univ

lemma BoxLayout.Separated.positive_margin {A : BoxLayout ι}
    (h : A.Separated 0) : ∃ η : ℝ, 0 < η ∧ A.Separated η := by
  classical
  let J := {p : ι × ι // p.1 ≠ p.2}
  have hs (p : J) : ∃ k, 0 < |A.center p.1.1 k - A.center p.1.2 k| -
      (A.width p.1.1 k + A.width p.1.2 k) := by
    obtain ⟨k, hk⟩ := h _ _ p.2
    exact ⟨k, by linarith⟩
  choose κ hκ using hs
  obtain ⟨δ, hδ, hm⟩ := finite_positive_lower_bound
    (fun p : J => |A.center p.1.1 (κ p) - A.center p.1.2 (κ p)| -
      (A.width p.1.1 (κ p) + A.width p.1.2 (κ p))) hκ
  refine ⟨δ / 8, by positivity, ?_⟩
  intro i j hij
  let p : J := ⟨(i, j), hij⟩
  refine ⟨κ p, ?_⟩
  have hh := hm p
  dsimp [p] at hh ⊢
  linarith

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.BoxLayout.Separated.positive_margin := @_root_.OAI.BalancedTransport.Geometry.BoxLayout.Separated.positive_margin
