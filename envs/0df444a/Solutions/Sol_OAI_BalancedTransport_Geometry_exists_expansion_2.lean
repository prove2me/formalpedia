-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.exists_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:23:07.754691+00:00
-- url     : https://prove2.me/submissions/2aa87aed-4416-4f3a-af77-cb130d465922

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Routing.lean:L77-L102
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.exists_expansion. The node keeps its source
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

lemma finite_upper_bound {α : Type*} [Finite α] (f : α → ℝ) :
    ∃ R : ℝ, ∀ i, f i < R := by
  obtain ⟨R, hR⟩ := (Set.finite_range f).bddAbove
  exact ⟨R + 1, fun i => (hR (mem_range_self i)).trans_lt (lt_add_one _)⟩

omit [Fintype ι] in
lemma centerSeparated_of_norm {a : ι → Space} {D : ℝ}
    (hD : 0 ≤ D) (ha : ∀ i j, i ≠ j → D < ‖a i - a j‖) : CenterSeparated a D := by
  intro i j hij
  by_contra! h
  have hh : ‖a i - a j‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr (by
    intro k
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h k)
  exact (ha i j hij).not_ge hh

lemma exists_expansion {a b : ι → Space} (ha : Function.Injective a)
    (hb : Function.Injective b) {D R : ℝ} (hD : 0 ≤ D) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ R + 2 ≤ Λ ∧
      CenterSeparated (fun i k => Λ * a i k) D ∧
      CenterSeparated (fun i k => Λ * b i k) D := by
  obtain ⟨La, hLa⟩ := finite_upper_bound (fun p : ι × ι => D / ‖a p.1 - a p.2‖)
  obtain ⟨Lb, hLb⟩ := finite_upper_bound (fun p : ι × ι => D / ‖b p.1 - b p.2‖)
  let Λ := max 1 (max (R + 2) (max La Lb))
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛR : R + 2 ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hΛa : La ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hΛb : Lb ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hh (c : ι → Space) (hc : Function.Injective c)
      (hLc : ∀ i j, D / ‖c i - c j‖ < Λ) :
      CenterSeparated (fun i k => Λ * c i k) D := by
    apply centerSeparated_of_norm hD
    intro i j hij
    have hpos : 0 < ‖c i - c j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hc.ne hij))
    have he : (fun k => Λ * c i k) - (fun k => Λ * c j k) = Λ • (c i - c j) := by
      ext k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Λ)]
    exact (div_lt_iff₀ hpos).mp (hLc i j)
  exact ⟨Λ, hΛ, hΛR, hh a ha (fun i j => (hLa (i,j)).trans_le hΛa),
    hh b hb (fun i j => (hLb (i,j)).trans_le hΛb)⟩

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.exists_expansion := @_root_.OAI.BalancedTransport.Geometry.exists_expansion
