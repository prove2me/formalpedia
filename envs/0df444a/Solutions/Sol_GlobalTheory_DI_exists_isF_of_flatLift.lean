-- Prove2me | solution 1 for GlobalTheory.DI.exists_isF_of_flatLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:26.794207+00:00
-- url     : https://prove2.me/submissions/5d401652-bbe3-4d6e-8077-65e21498d835

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobLiftPsiNatCastMul
import Theorems.Thm_GlobalTheory_DI_frobLiftPhi_apply
import Theorems.Thm_GlobalTheory_DI_frobLiftPhi_mul

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
open MvPolynomial
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)
variable {p π F}
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → ∃ f, IsF p π F f := by
  intro K Kt _ _ p _ _ π F hL hF
  have univ : ∀ (M : Type) [AddCommGroup M] [Module K M] (D' : K →+ M),
      (∀ a b, D' (a * b) = a • D' b + b • D' a) →
      ∃ g : Ω[K⁄ℤ] →+ M, (∀ a, g (KaehlerDifferential.D ℤ K a) = D' a) ∧
        ∀ (c : K) (v : Ω[K⁄ℤ]), g (c • v) = c • g v := by
    intro M _ _ D' hD'
    let Dv : Derivation ℤ K M := Derivation.mk' D'.toIntLinearMap hD'
    exact ⟨Dv.liftKaehlerDifferential.toAddMonoidHom,
      fun a => Dv.liftKaehlerDifferential_comp_D a,
      fun c v => Dv.liftKaehlerDifferential.map_smul c v⟩
  have hmul : ∀ a b : K, frobLiftPhi hL hF (a * b) =
      frobenius K p a • frobLiftPhi hL hF b + frobenius K p b • frobLiftPhi hL hF a := by
    intro a b
    rw [frobenius_def p a, frobenius_def p b]
    exact frobLiftPhi_mul hL hF a b
  obtain ⟨g, hg, hsm⟩ :=
    @univ (Ω[K⁄ℤ]) _ (Module.compHom _ (frobenius K p)) (frobLiftPhi hL hF) hmul
  refine ⟨g, ?_, ?_⟩
  · intro c v
    have h0 : g (c • v) = frobenius K p c • g v := hsm c v
    rw [frobenius_def p c] at h0
    exact h0
  · intro z w hzw
    have := hg (π z)
    rw [frobLiftPhi_apply, frobLiftPsi_spec hL hF hzw] at this
    exact this
end GlobalTheory.DI
