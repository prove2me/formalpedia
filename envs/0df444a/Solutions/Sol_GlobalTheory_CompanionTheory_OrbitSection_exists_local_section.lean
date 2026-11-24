-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OrbitSection.exists_local_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:26:46.68194+00:00
-- url     : https://prove2.me/submissions/c9127229-4933-42b6-91bb-141ee79045d3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_vecMul_shear
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_shear_self
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_coe_orbitSection
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_continuousOn_orbitSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OrbitSection
namespace GlobalTheory.CompanionTheory.OrbitSection
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  intro k _ _ _ _ n ζ hζ
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hζ
  have hj' : ζ j ≠ 0 := hj
  refine ⟨{ξ | ξ j ≠ 0}, isOpen_ne.preimage (continuous_apply j), hj', orbitSection j ζ,
    continuousOn_orbitSection j ζ hj', ?_, fun ξ hξ => ?_⟩
  · apply Units.ext
    rw [coe_orbitSection j ζ ζ hj' hj', shear_self]
    rfl
  · rw [coe_orbitSection j ζ ξ hj' hξ, vecMul_shear j ζ ξ hj']
end GlobalTheory.CompanionTheory.OrbitSection
