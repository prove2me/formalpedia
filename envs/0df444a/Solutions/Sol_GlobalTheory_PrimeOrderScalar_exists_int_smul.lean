-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.exists_int_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:38:33.357491+00:00
-- url     : https://prove2.me/submissions/5ffa7676-415c-4b1b-b563-4abee1ac0dd0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution (hT : T.Prime) (hM : Nat.card M = T) (s : S) :
    ∃ k : ℤ, ∀ m : M, s • m = k • m := by
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : IsAddCyclic M := isAddCyclic_of_prime_card hM
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := M)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg (s • g))
  refine ⟨k, fun m => ?_⟩
  obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg m)
  rw [smul_comm s j g, ← hk, smul_comm k j g]
end GlobalTheory.PrimeOrderScalar
