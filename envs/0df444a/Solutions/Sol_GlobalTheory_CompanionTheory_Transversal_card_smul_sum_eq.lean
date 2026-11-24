-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Transversal.card_smul_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:32.990604+00:00
-- url     : https://prove2.me/submissions/d3d4e6e6-e517-4a15-8c51-b4b76dcf3e01

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSumsProportionalCard
import Theorems.Thm_GlobalTheory_CompanionTheory_Transversal_sum_add_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Transversal
namespace GlobalTheory.CompanionTheory.Transversal
theorem _root_.solution {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M] [Module ℂ M]
    {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A) {T T' : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hTA' : ∀ t ∈ T', t ∈ A) (hT' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H')
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_comm, Finset.sum_congr rfl
      (fun t' ht' => sum_add_eq_sum hTA hT F hF (hTA' t' ht')), Finset.sum_const]
  have h2 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T.card • ∑ t ∈ T', F t := by
    have : ∀ t ∈ T, ∑ t' ∈ T', F (t + t') = ∑ t' ∈ T', F t' := fun t ht => by
      rw [← sum_add_eq_sum hTA' hT' F hF' (hTA t ht)]
      exact Finset.sum_congr rfl (fun t' _ => by rw [add_comm])
    rw [Finset.sum_congr rfl this, Finset.sum_const]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← h1, h2]
end GlobalTheory.CompanionTheory.Transversal
