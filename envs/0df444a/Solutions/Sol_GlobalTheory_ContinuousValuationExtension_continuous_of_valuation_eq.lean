-- Prove2me | solution 1 for GlobalTheory.ContinuousValuationExtension.continuous_of_valuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:27.839333+00:00
-- url     : https://prove2.me/submissions/282ca096-c8de-4c73-9b9c-5f04f4514144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsContinuousExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GlobalTheory GlobalTheory.ContinuousValuationExtension
namespace GlobalTheory.ContinuousValuationExtension
theorem _root_.solution {A B Γ : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (g : A →+* B)
    (hs : Function.Surjective (Valued.v : A → Γ))
    (hg : ∀ x : A, (Valued.v (g x) : Γ) = Valued.v x) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero A Γ).tendsto_iff (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _

  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, ha]
    intro h0
    apply γ.ne_zero
    apply MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
    rw [h0, map_zero]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff, ha] at hx
  show (Valued.v : Valuation B Γ).restrict (g x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx
end GlobalTheory.ContinuousValuationExtension
