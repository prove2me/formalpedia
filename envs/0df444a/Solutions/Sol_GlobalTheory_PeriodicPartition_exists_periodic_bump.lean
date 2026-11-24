-- Prove2me | solution 1 for GlobalTheory.PeriodicPartition.exists_periodic_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:30.469026+00:00
-- url     : https://prove2.me/submissions/e645ffc6-07e2-44ba-a02a-2f9134f261f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Theorems.Thm_GlobalTheory_PeriodicPartition_locallyFinite_support_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicPartition
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory.PeriodicPartition
theorem _root_.solution (Λ : Submodule ℤ E) [DiscreteTopology Λ] {U : Set E}
    (hU : IsOpen U) (hper : ∀ (l : Λ) z, z ∈ U → z + l ∈ U) {x : E} (hx : x ∈ U) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ (l : Λ) z, ψ (z + l) = ψ z) ∧ tsupport ψ ⊆ U ∧
      (∀ z, 0 ≤ ψ z) ∧ 0 < ψ x := by
  obtain ⟨φ, hφU, hφc, hφs, hφr, hφx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hx)
  have h0 : ∀ z, 0 ≤ φ z := fun z => (hφr ⟨z, rfl⟩).1
  have hlf := locallyFinite_support_translate Λ φ hφc
  refine ⟨fun z => ∑ᶠ l : Λ, φ (z + l), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : Λ) (z : E) => φ (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  · intro l z
    show ∑ᶠ m : Λ, φ (z + l + m) = ∑ᶠ m : Λ, φ (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : Λ => φ (z + m))]
    simp [add_assoc]
  · have h1 : Function.support (fun z => ∑ᶠ l : Λ, φ (z + l)) ⊆
        ⋃ l : Λ, Function.support fun z : E => φ (z + l) := by
      intro z hz
      by_contra hn
      simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
      exact hz (by simp [hn])
    refine (closure_mono h1).trans ?_
    rw [hlf.closure_iUnion]
    refine Set.iUnion_subset fun l => ?_
    have h2 : closure (Function.support fun z : E => φ (z + l)) ⊆
        (fun z : E => z + l) ⁻¹' tsupport φ :=
      closure_minimal (fun z hz => subset_tsupport _ hz)
        ((isClosed_tsupport φ).preimage (by fun_prop))
    intro z hz
    have := hper (-l) _ (hφU (h2 hz))
    simpa using this
  · exact fun z => finsum_nonneg fun l => h0 _
  · have h1 := single_le_finsum (f := fun l : Λ => φ (x + l)) 0 (hlf.point_finite x)
      (fun l => h0 _)
    simp only [ZeroMemClass.coe_zero, add_zero, hφx] at h1
    exact lt_of_lt_of_le one_pos h1
end GlobalTheory.PeriodicPartition
