-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EigenLift.exists_eigenvector_of_surjective_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:15.408917+00:00
-- url     : https://prove2.me/submissions/418f8d3e-f3c4-4110-9e02-0afb43280176

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EigenvectorLiftOfSurjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EigenLift
namespace GlobalTheory.CompanionTheory.EigenLift
theorem _root_.solution
    (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W')
    (hf : Function.Surjective f) (hfT : f ∘ₗ T = S ∘ₗ f)
    (c : ℂ) (w' : W') (hw' : w' ≠ 0) (hS : S w' = c • w') :
    ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  by_contra hne
  push_neg at hne
  haveI : FiniteDimensional ℂ W' := Module.Finite.of_surjective (R := ℂ) f hf
  set A : W →ₗ[ℂ] W := T - c • LinearMap.id with hA
  set B : W' →ₗ[ℂ] W' := S - c • LinearMap.id with hB
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra h0
    apply hne w h0
    simpa [hA, sub_eq_zero] using hw
  have hsurjT : Function.Surjective A := LinearMap.injective_iff_surjective.1 hinj
  have hcomm : ∀ z, f (A z) = B (f z) := by
    intro z
    have h1 := LinearMap.congr_fun hfT z
    simp only [LinearMap.comp_apply] at h1
    simp [hA, hB, map_sub, map_smul, h1]
  have hsurjS : Function.Surjective B := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hsurjT x
    exact ⟨f z, (hcomm z).symm⟩
  have hinjS := LinearMap.injective_iff_surjective.2 hsurjS
  apply hw'
  apply hinjS
  simp [hB, hS]
end GlobalTheory.CompanionTheory.EigenLift
