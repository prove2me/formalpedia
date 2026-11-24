-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Invsum.invariance_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:26.169435+00:00
-- url     : https://prove2.me/submissions/1f994f47-53cf-40ca-98a7-0ba9914386ff

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Invsum
namespace GlobalTheory.CompanionTheory.Invsum
theorem _root_.solution {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M]
    [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] {β γ : Type} [Fintype β] (b : β → P)
    (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ) (E : γ → Module.End ℂ M)
    (hanti : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hinv : ∀ k (Y : Fin q → P), E k (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (k : γ) (J : Fin q → β) :
    ∑ s, ∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) = -E k (ω (b ∘ J)) := by
  have step : ∀ s, ω (Function.update (b ∘ J) s (D k ((b ∘ J) s))) =
      -∑ i, (c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i)) := by
    intro s
    have e : D k ((b ∘ J) s) = ∑ i, c i (J s) k • b i := hD k (J s)
    have h1 : ω (Function.update (b ∘ J) s (∑ i, c i (J s) k • b i)) =
        ∑ i, ω (Function.update (b ∘ J) s (c i (J s) k • b i)) :=
      ω.toMultilinearMap.map_update_sum Finset.univ s (fun i => c i (J s) k • b i) (b ∘ J)
    rw [e, h1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : ω (Function.update (b ∘ J) s (c i (J s) k • b i)) =
        c i (J s) k • ω (Function.update (b ∘ J) s (b i)) :=
      ω.map_update_smul (b ∘ J) s (c i (J s) k) (b i)
    have h3 : ((c (J s) i k : ℝ) : ℂ) • ω (Function.update (b ∘ J) s (b i)) =
        c (J s) i k • ω (Function.update (b ∘ J) s (b i)) :=
      algebraMap_smul ℂ (c (J s) i k) (ω (Function.update (b ∘ J) s (b i)))
    rw [h2, h3, hanti (J s) i k, neg_smul]
  rw [hinv k (b ∘ J), Finset.sum_congr rfl fun s _ => step s, Finset.sum_neg_distrib, neg_neg]
end GlobalTheory.CompanionTheory.Invsum
