-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalSplit.exists_idempotent_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:21:18.591799+00:00
-- url     : https://prove2.me/submissions/00a17c66-3d00-4767-8718-96b8e52959ff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplitting
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_ker_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalSplit_exists_section

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalSplit
namespace GlobalTheory.CompanionTheory.LocalSplit
theorem _root_.solution (A Q P : Type) [CommRing A] [IsLocalRing A]
    [AddCommGroup Q] [Module A Q] [AddCommGroup P] [Module A P] [Module.Finite A Q]
    [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) :
    ∃ r : P →ₗ[A] Q, (r ∘ₗ d ∘ₗ r ∘ₗ d = r ∘ₗ d) ∧ Module.Free A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.Finite A (LinearMap.ker (r ∘ₗ d)) ∧
      Module.finrank A (LinearMap.ker (r ∘ₗ d)) =
        Module.finrank (IsLocalRing.ResidueField A)
          (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) := by
  obtain ⟨s, f, t, ht, hs⟩ := exists_section d
  have hpf : ∀ y, t (d (f y)) = y := fun y => LinearMap.congr_fun ht y
  have hfinj : Function.Injective f := fun x y hxy => by
    rw [← hpf x, ← hpf y, hxy]
  have hker : LinearMap.ker ((f ∘ₗ t) ∘ₗ d) = LinearMap.ker (t ∘ₗ d) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h => hfinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  obtain ⟨h1, h2, h3⟩ := ker_facts s f (t ∘ₗ d) ht
  refine ⟨f ∘ₗ t, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [hpf]
  · rw [hker]; exact h1
  · rw [hker]; exact h2
  · rw [hker]; omega
end GlobalTheory.CompanionTheory.LocalSplit
