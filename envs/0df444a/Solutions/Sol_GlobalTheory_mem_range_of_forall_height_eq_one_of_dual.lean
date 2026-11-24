-- Prove2me | solution 1 for GlobalTheory.mem_range_of_forall_height_eq_one_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:07.488793+00:00
-- url     : https://prove2.me/submissions/aadb9c68-b104-4b2e-87e7-c919483bb7fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_dvd_of_forall_height_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]
namespace GlobalTheory
theorem _root_.solution
    (hM : ∀ {a : A}, a ≠ 0 → ∀ {m : M}, (∀ φ : Module.Dual A M, a ∣ φ m) → ∃ m', a • m' = m)
    (f : M →ₗ[A] V) (hf : Function.Injective f) [Module.IsTorsionFree A V] {v : V} {a : A}
    (ha : a ≠ 0) (hav : a • v ∈ LinearMap.range f)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → a ∈ p →
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f) :
    v ∈ LinearMap.range f := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨m', hm'⟩ := hM ha (m := m) fun φ => dvd_of_forall_height_eq_one ha fun p _ hp hap => by
    obtain ⟨s, hs, n, hn⟩ := h p hp hap
    refine ⟨s, hs, φ n, ?_⟩
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul]
    congr 1
    apply hf
    rw [map_smul, map_smul, hm, hn, smul_comm]
  refine ⟨m', smul_right_injective V ha ?_⟩
  simp only
  rw [← map_smul, hm', hm]
end GlobalTheory
