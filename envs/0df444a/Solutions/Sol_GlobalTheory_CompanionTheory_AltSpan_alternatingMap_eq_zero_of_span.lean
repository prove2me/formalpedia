-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AltSpan.alternatingMap_eq_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:24.686498+00:00
-- url     : https://prove2.me/submissions/164ea8ed-8ec4-4450-9597-fea5f80123a4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AltSpan
namespace GlobalTheory.CompanionTheory.AltSpan
theorem _root_.solution :
    ∀ {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℝ M]
      {β : Type} (b : β → P), Submodule.span ℝ (Set.range b) = ⊤ →
      ∀ {m : ℕ} (f : P [⋀^Fin m]→ₗ[ℝ] M), (∀ I : Fin m → β, f (b ∘ I) = 0) → f = 0 := by
  intro P _ _ M _ _ β b hb m f hf
  classical
  have key : ∀ (S : Finset (Fin m)) (v : Fin m → P), (∀ i ∉ S, v i ∈ Set.range b) → f v = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro v hv
      choose I hI using fun i => hv i (by simp)
      have hvI : v = b ∘ I := funext fun i => (hI i).symm
      rw [hvI]
      exact hf I
    · intro j S _ ih v hv
      have hlin : f.toMultilinearMap.toLinearMap v j = 0 := by
        apply LinearMap.ext_on_range hb
        intro c
        simp only [MultilinearMap.toLinearMap_apply, LinearMap.zero_apply, AlternatingMap.coe_multilinearMap]
        apply ih
        intro i hi
        by_cases hij : i = j
        · rw [hij]
          simp
        · rw [Function.update_of_ne hij]
          exact hv i (by simp [hij, hi])
      have h1 := LinearMap.congr_fun hlin (v j)
      simpa [MultilinearMap.toLinearMap_apply] using h1
  ext v
  simpa using key Finset.univ v (by simp)
end GlobalTheory.CompanionTheory.AltSpan
