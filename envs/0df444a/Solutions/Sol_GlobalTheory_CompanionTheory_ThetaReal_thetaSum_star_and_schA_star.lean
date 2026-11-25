-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:21.88292+00:00
-- url     : https://prove2.me/submissions/78d8727c-6c0c-47c2-9ed5-3193c18c8384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ThetaSumStarAndSchAStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaReal
namespace GlobalTheory.CompanionTheory.ThetaReal
theorem _root_.solution (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (star Φ) = conj (thetaSum F Φ) ∧ (Φ ∈ schA F κ → star Φ ∈ schA F κ) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold thetaSum
    rw [← RCLike.star_def, tsum_star]
    rfl
  · classical
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      refine Submodule.subset_span ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, star g,
        ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩, ?_⟩
      funext x
      simp [pureA]
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.CompanionTheory.ThetaReal
