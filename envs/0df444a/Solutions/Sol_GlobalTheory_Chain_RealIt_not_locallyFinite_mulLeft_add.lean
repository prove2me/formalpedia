-- Prove2me | solution 1 for GlobalTheory.Chain.RealIt.not_locallyFinite_mulLeft_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:09.15405+00:00
-- url     : https://prove2.me/submissions/39fc8c6f-65ff-4dae-b0cf-3b07f50456a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotLocallyFiniteQuadraticMulAddDegreeNonraising
import Theorems.Thm_GlobalTheory_Chain_RealIt_totalDegree_mulLeft_add
import Theorems.Thm_GlobalTheory_Chain_RealIt_exists_totalDegree_le_of_finiteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open MvPolynomial
namespace GlobalTheory.Chain.RealIt
theorem _root_.solution :
    ∀ (σ : Type) [Finite σ] (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)),
      Q ≠ 0 → Q.IsHomogeneous 2 → (∀ P, (L P).totalDegree ≤ P.totalDegree) →
      ∀ φ : MvPolynomial σ ℂ, φ ≠ 0 → ∀ F : Submodule ℂ (MvPolynomial σ ℂ),
        FiniteDimensional ℂ F → ¬ ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ∈ F := by
  intro σ _ Q L hQ hh hL φ hφ F hF hall
  obtain ⟨N, hN⟩ := exists_totalDegree_le_of_finiteDimensional F hF
  have key : ∀ n : ℕ, ((LinearMap.mulLeft ℂ Q + L) ^ n) φ ≠ 0 ∧
      (((LinearMap.mulLeft ℂ Q + L) ^ n) φ).totalDegree = φ.totalDegree + 2 * n := by
    intro n
    induction n with
    | zero => simpa using hφ
    | succ n ih =>
      have h := totalDegree_mulLeft_add Q L hQ hh hL _ ih.1
      rw [pow_succ', Module.End.mul_apply]
      refine ⟨fun h0 => ?_, by rw [h, ih.2]; ring⟩
      rw [h0, totalDegree_zero] at h
      omega
  have h1 := hN _ (hall (N + 1))
  rw [(key (N + 1)).2] at h1
  omega
end GlobalTheory.Chain.RealIt
