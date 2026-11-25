-- Prove2me | solution 1 for GlobalTheory.SkewDense.exists_dual_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:11:28.72808+00:00
-- url     : https://prove2.me/submissions/18148083-463b-4d6c-8d7a-9640b8d6a1e7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.SkewDense
namespace GlobalTheory.SkewDense
theorem _root_.solution (E : Type) [Field E] [NumberField E] [DecidableEq (E →+* ℂ)] :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → E) (a : (E →+* ℂ) → κ → ℂ),
      ∀ g₀ g : E →+* ℂ, ∑ k, a g₀ k * g (b k) = if g = g₀ then 1 else 0 := by
  classical
  let B := NumberField.canonicalEmbedding.latticeBasis E
  let b : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → E := fun k => NumberField.integralBasis E k
  have hB : ∀ k, B k = fun σ => σ (b k) := fun k => by
    funext σ; rw [NumberField.canonicalEmbedding.latticeBasis_apply, NumberField.canonicalEmbedding.apply_at]
  have H1 : ∀ σ₀ : E →+* ℂ, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℂ,
      ∀ σ, ∑ k, a k * σ (b k) = if σ = σ₀ then 1 else 0 := by
    intro σ₀
    refine ⟨B.repr (Pi.single σ₀ 1), fun σ => ?_⟩
    have := congrFun (B.sum_repr (Pi.single σ₀ 1)) σ
    simpa [Finset.sum_apply, hB, Pi.single_apply] using this
  choose a ha using H1
  exact ⟨_, inferInstance, b, a, ha⟩
end GlobalTheory.SkewDense
