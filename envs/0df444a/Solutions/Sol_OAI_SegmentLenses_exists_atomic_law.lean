-- Prove2me | solution 1 for OAI.SegmentLenses.exists_atomic_law
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:43:54.71628+00:00
-- url     : https://prove2.me/submissions/a0293ffe-d627-4944-8527-f4005fa876cf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/GateRecovery.lean:L289-L317
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.exists_atomic_law. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery
import Theorems.Thm_OAI_SegmentLenses_mem_atomicBody_of_norm_le_one

-- ---- from OAI.Analysis.SegmentLenses.AtomicBalls ----
namespace OAI

/-!
# Atomic polar descriptions of finite unit balls
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section FiniteBodies
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end FiniteBodies

section FinitePolar
variable {V : Type*} [decidableEqV : DecidableEq V] [segmentSystemV : SegmentSystem V]

end FinitePolar

section EuclideanNormalization
variable {ι : Type*} [Fintype ι]

theorem norm_normalized_le (q : EuclideanSpace ℝ ι) : ‖‖q‖⁻¹ • q‖ ≤ 1 := by
  by_cases hq : ‖q‖ = 0
  · simp [hq]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg q)),
      inv_mul_cancel₀ hq]

end EuclideanNormalization

section AtomicSeparation
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end AtomicSeparation

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.LawRecovery ----
namespace OAI

/-!
# Exact finite-law recovery and coefficient representations
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

section LawRecovery
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem coefficientAtoms_energy (K : Finset V) (c : LocalCoefficients K)
    (ω : Option (LocalFamily K)) : (coefficientAtoms K c ω).energy ≤ 1 := by
  cases ω with
  | none => simp [coefficientAtoms]
  | some F =>
      change (representation F.val (‖c F‖⁻¹ • c F)).energy ≤ 1
      rw [representation_energy]
      nlinarith [norm_normalized_le (c F), norm_nonneg (‖c F‖⁻¹ • c F)]

theorem coefficientLaw_mean (K : Finset V) (c : LocalCoefficients K)
    (hc : coefficientBudget K c ≤ 1) :
    (coefficientLaw K c hc).expect (fun ω => (coefficientAtoms K c ω).value) = localValue K c := by
  simp only [FiniteLaw.expect, coefficientLaw, Fintype.sum_option, coefficientAtoms,
    Option.elim_none, Option.elim_some, representation_value, map_zero, smul_zero, zero_add]
  change (∑ F, ‖c F‖ • familyValue F.val (‖c F‖⁻¹ • c F)) = ∑ F, familyValue F.val (c F)
  apply Finset.sum_congr rfl
  intro F hF
  rw [← map_smul, smul_smul]
  by_cases hz : ‖c F‖ = 0
  · have hc0 : c F = 0 := norm_eq_zero.mp hz
    simp [hc0]
  · rw [mul_inv_cancel₀ hz, one_smul]

end LawRecovery

namespace FiniteLaw
variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end FiniteLaw

section RepresentationGates
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

end RepresentationGates

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.GateRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Gate coefficients, cone recovery, and energy budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section ProjectionAlgebra
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

namespace SegmentFamily

end SegmentFamily

namespace Representation

end Representation
end ProjectionAlgebra

section GateTails
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace SegmentFamily

end SegmentFamily
end GateTails

section GateRecovery
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

namespace SegmentFamily

end SegmentFamily
end GateRecovery

section ScaledLaws
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace Representation

end Representation

theorem exists_atomic_law {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) {R : ℝ} (hR : 0 < R) (hn : ‖z‖ ≤ R) :
    ∃ μ : FiniteLaw (Option (LocalFamily K)),
      ∃ A : Option (LocalFamily K) → Representation V,
        (∀ ω, (A ω).energy ≤ R ^ 2) ∧
        (∀ ω S, S ∈ (A ω).family.sets → S ⊆ K) ∧
        μ.expect (fun ω => (A ω).value) = z := by
  classical
  have hzh : head K (R⁻¹ • z) = R⁻¹ • z := by
    change headLinear K (R⁻¹ • z) = _
    rw [map_smul, headLinear_apply, hz]
  have hzn : ‖R⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR.le)]
    exact (inv_mul_le_iff₀ hR).mpr (by simpa using hn)
  obtain ⟨c, hc, hcz⟩ := mem_atomicBody_of_norm_le_one hK (R⁻¹ • z) hzh hzn
  let μ := coefficientLaw K c hc
  let A := fun ω => (coefficientAtoms K c ω).scale R
  refine ⟨μ, A, ?_, ?_, ?_⟩
  · intro ω
    change ((coefficientAtoms K c ω).scale R).energy ≤ R ^ 2
    rw [Representation.scale_energy]
    exact mul_le_of_le_one_right (sq_nonneg R) (coefficientAtoms_energy K c ω)
  · intro ω S hS
    cases ω with
    | none => exact False.elim (Finset.notMem_empty _ hS)
    | some F => exact F.property S hS
  · change μ.expect (fun ω => ((coefficientAtoms K c ω).scale R).value) = z
    simp only [Representation.scale_value]
    rw [μ.expect_smul, coefficientLaw_mean, hcz, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

end ScaledLaws

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem solution {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) {R : ℝ} (hR : 0 < R) (hn : ‖z‖ ≤ R) :
    ∃ μ : FiniteLaw (Option (LocalFamily K)),
      ∃ A : Option (LocalFamily K) → Representation V,
        (∀ ω, (A ω).energy ≤ R ^ 2) ∧
        (∀ ω S, S ∈ (A ω).family.sets → S ⊆ K) ∧
        μ.expect (fun ω => (A ω).value) = z := by
  first
    | exact OAI.SegmentLenses.exists_atomic_law hK z hz hR hn
    | exact OAI.SegmentLenses.exists_atomic_law
    | (apply OAI.SegmentLenses.exists_atomic_law <;> assumption)
    | (intros; apply OAI.SegmentLenses.exists_atomic_law <;> assumption)
