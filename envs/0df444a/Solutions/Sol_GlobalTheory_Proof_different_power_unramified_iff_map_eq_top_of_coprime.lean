-- Prove2me | solution 1 for GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:08.897611+00:00
-- url     : https://prove2.me/submissions/d7e5af25-5a4f-4535-b4e7-da38c818922e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DifferentPowerUnramifiedIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.different_power_unramified_iff
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
namespace GlobalTheory.Proof.different_power_unramified_iff
theorem _root_.solution {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) (P : Ideal R) (hP : P.IsMaximal)
    (h : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map f = ⊤) (Q : Ideal R) (hQ : Q ≠ ⊥)
    (hPQ : P ⊔ Q = ⊤) : Q.map f = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal _ hne
  have hQ' : Q ≤ M.comap f := Ideal.map_le_iff_le_comap.mp hQM
  have hprime : (M.comap f).IsPrime := Ideal.comap_isPrime f M
  have hbot : M.comap f ≠ ⊥ := fun h => hQ (eq_bot_iff.mpr (h ▸ hQ'))
  have hmax : (M.comap f).IsMaximal := hprime.isMaximal hbot
  by_cases hPeq : M.comap f = P
  · apply hP.ne_top
    rw [← hPQ]
    exact (sup_eq_left.mpr (hPeq ▸ hQ')).symm
  · apply hM.ne_top
    rw [eq_top_iff, ← h _ hmax hPeq]
    exact Ideal.map_comap_le
end GlobalTheory.Proof.different_power_unramified_iff
