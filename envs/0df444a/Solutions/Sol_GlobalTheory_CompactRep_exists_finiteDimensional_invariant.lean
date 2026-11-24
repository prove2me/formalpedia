-- Prove2me | solution 1 for GlobalTheory.CompactRep.exists_finiteDimensional_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:17.783856+00:00
-- url     : https://prove2.me/submissions/a65169c7-7e6d-4ac9-b6d1-0a3956476d20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
import Theorems.Thm_GlobalTheory_CompactRep_continuous_rankOne_self
import Theorems.Thm_GlobalTheory_CompactRep_isCompactOperator_rankOne_self
import Theorems.Thm_GlobalTheory_CompactRep_isCompactOperator_integral
import Theorems.Thm_GlobalTheory_CompactRep_isSymmetric_integral_rankOne
import Theorems.Thm_GlobalTheory_CompactRep_integral_rankOne_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
namespace GlobalTheory.CompactRep
theorem _root_.solution :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
      [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (π : K →* (H →L[ℂ] H)), (∀ k x, ‖π k x‖ = ‖x‖) →
      (∀ x, Continuous fun k => π k x) →
      ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S := by
  intro K _ _ _ _ _ _ H _ _ _ _ π hnorm hcont
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ : ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧
      μ.IsOpenPosMeasure := by
    refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance, inferInstance⟩
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hw : Continuous fun k => π k v := hcont v
  have hFc : Continuous fun k => rankOne ℂ (π k v) (π k v) := continuous_rankOne_self.comp hw
  have hFi : Integrable (fun k => rankOne ℂ (π k v) (π k v)) μ :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTc : IsCompactOperator (∫ k, rankOne ℂ (π k v) (π k v) ∂μ : H →L[ℂ] H) :=
    isCompactOperator_integral hFi (fun k => isCompactOperator_rankOne_self _)
  have hTs := isSymmetric_integral_rankOne hFi
  have hpos : 0 < ∫ k, ‖⟪v, π k v⟫_ℂ‖ ^ 2 ∂μ := by
    have hc : Continuous fun k => ‖⟪v, π k v⟫_ℂ‖ ^ 2 :=
      ((continuous_const.inner hw).norm).pow 2
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_
    simp [hv]
  have hT0 := integral_rankOne_ne_zero hFi v hpos
  set T : H →L[ℂ] H := ∫ k, rankOne ℂ (π k v) (π k v) ∂μ with hT
  obtain ⟨c, hc, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hno)
  have hinner : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨(π g).toLinearMap, hnorm g⟩ x y
  have hcomm : ∀ g x, T (π g x) = π g (T x) := by
    intro g x
    have hix : Integrable (fun k => rankOne ℂ (π k v) (π k v) x) μ :=
      (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
    have hsh := integral_mul_left_eq_self (μ := μ)
      (fun k => rankOne ℂ (π k v) (π k v) (π g x)) g
    rw [hT, ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi,
      ← ContinuousLinearMap.integral_comp_comm (π g) hix, ← hsh]
    congr 1
    funext k
    have hm : ∀ a b : K, ∀ y, π (a * b) y = π a (π b y) := fun a b y => by rw [map_mul]; rfl
    simp only [rankOne_apply, hm, hinner, map_smul]
  refine ⟨Module.End.eigenspace (T : Module.End ℂ H) c, Module.End.hasEigenvalue_iff.mp hc,
    ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0, ?_⟩
  intro k x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change T (π k x) = c • π k x
  change T x = c • x at hx
  rw [hcomm, hx, map_smul]
end GlobalTheory.CompactRep
