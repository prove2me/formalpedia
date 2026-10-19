-- Prove2me | solution 1 for OAI.KervaireRegular.trivial_of_boundary_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:53:36.054995+00:00
-- url     : https://prove2.me/submissions/c242b3d7-3056-489e-bbe2-0e3ce0afd883

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MixingOperators.lean:L269-L302
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRegular.trivial_of_boundary_inequalities. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Theorems.Thm_OAI_KervaireRegular_groupPhase_eq_zero_iff
import Theorems.Thm_OAI_KervaireSpectral_tendsto_vectorPhase_rotation

-- ---- from OAI.GroupTheory.Kervaire.SpectralMeasures ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem phase_nonneg (z : ℂ) : 0 ≤ phase z := Int.fract_nonneg _

theorem vectorPhase_nonneg (U : Operator H) [IsStarNormal U] (ξ : H) :
    0 ≤ vectorPhase U ξ := integral_nonneg fun _ => phase_nonneg _

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseFaithfulness ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

/-- The nonnegative cut convention gives precisely the right-hand continuity
used at the distinguished boundary. -/
theorem tendsto_groupPhase_rotation (a : A) {x : ℕ → ℝ}
    (hx : Filter.Tendsto x Filter.atTop (nhds 0)) (hx0 : ∀ n, 0 ≤ x n) :
    Filter.Tendsto (fun n => groupPhase (scalarRotation (x n)) (scalarRotation_unitary _) a)
      Filter.atTop (nhds (groupPhase 1 (one_mem _) a)) := by
  simpa only [groupPhase, one_smul] using
    tendsto_vectorPhase_rotation (leftOperator a) (leftOperator_unitary a) (delta 1) hx hx0
end KervaireRegular

namespace KervaireSpectral
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.MixingOperators ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireMixing

section
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end KervaireMixing
namespace KervaireCycle
variable {D E B : Type*} [Monoid B]
end KervaireCycle
namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]
end KervaireMatrix

namespace KervaireRegular
open KervaireSpectral KervaireTraceCalculus MeasureTheory
variable {A : Type*} [Group A]

/-- The final right-cut limiting argument in the planar component theorem. -/
lemma trivial_of_boundary_inequalities {Z : Type*} [Fintype Z] [Nonempty Z]
    (z₀ : Z) (c : Z → A)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      groupPhase (scalarRotation (((Fintype.card Z : ℝ)-1)*ε)) (scalarRotation_unitary _) (c z₀)
        + ((Fintype.card Z : ℝ)-1)*(1-ε) ≤ (Fintype.card Z : ℝ)-1) :
    c z₀ = 1 := by
  let x : ℕ → ℝ := fun n ↦ 1 / (n+2)
  have hx : Filter.Tendsto x Filter.atTop (nhds 0) := by
    simpa only [x,Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hx0 (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hx1 (n : ℕ) : x n < 1 := by dsimp [x]; rw [div_lt_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hcard : (0 : ℝ) ≤ (Fintype.card Z : ℝ)-1 := by
    have hc := Fintype.card_pos (α := Z)
    have : (1 : ℝ) ≤ Fintype.card Z := by exact_mod_cast hc
    linarith
  have ht := tendsto_groupPhase_rotation (c z₀)
    (by simpa using hx.const_mul ((Fintype.card Z : ℝ)-1))
    (fun n ↦ mul_nonneg hcard (hx0 n).le)
  have hl : groupPhase 1 (one_mem _) (c z₀) ≤ 0 := by
    apply le_of_tendsto_of_tendsto' ht
      (show Filter.Tendsto (fun n ↦ ((Fintype.card Z : ℝ)-1)*x n) Filter.atTop (nhds 0) by
        simpa using hx.const_mul ((Fintype.card Z : ℝ)-1))
    intro n
    have hn := h (x n) (hx0 n) (hx1 n)
    linarith
  apply (groupPhase_eq_zero_iff _).mp
  exact le_antisymm hl (by
    let _ := isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨(1 : ℂ),one_mem _⟩ (leftOperator_unitary (c z₀)))
    unfold groupPhase
    exact vectorPhase_nonneg _ _)
end KervaireRegular

namespace KervaireCycle
open KervaireSpectral
variable {D B : Type*} [CommMonoid B]
end KervaireCycle

namespace KervaireBoundary
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

end KervaireBoundary

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRegular
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open KervaireSpectral KervaireTraceCalculus MeasureTheory


theorem solution : type_of% @_root_.OAI.KervaireRegular.trivial_of_boundary_inequalities := @_root_.OAI.KervaireRegular.trivial_of_boundary_inequalities
