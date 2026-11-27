-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.not_isUnit_of_kills
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:33.176053+00:00
-- url     : https://prove2.me/submissions/d9aa0a67-a012-43cd-b9bb-a80e8ac89fe0

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
theorem _root_.solution (hT : T.Prime) (hM : Nat.card M = T) {u : S}
    (hu : ∀ m : M, u • m = 0) : ¬ IsUnit u := by
  intro h
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; exact hT.ne_zero)
  haveI : Nontrivial M :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact hT.one_lt)
  obtain ⟨a, ha⟩ := exists_ne (0 : M)
  exact ha ((h.smul_eq_zero).mp (hu a))
end GlobalTheory.PrimeOrderScalar
