-- Prove2me | solution 1 for GlobalTheory.T.twisted_jacquet_exact_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:04:09.193538+00:00
-- url     : https://prove2.me/submissions/bcebf243-b2aa-4e43-b4e1-32fbe049e59f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedJacquetExactSmooth
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_MirabolicDerivatives_TwistedKernels_TwKerLeComapOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedJacquetExactSmoothStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PRep_TwExact_twMap_range_eq_ker


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.BZMir
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ → ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) → (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧ IsCompact (L : Set G)) → ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g → LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | exact GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | (intros; apply GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker <;> assumption)
end _root_.GlobalTheory.T
