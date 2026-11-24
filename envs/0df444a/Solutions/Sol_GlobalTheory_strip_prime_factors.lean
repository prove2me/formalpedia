-- Prove2me | solution 1 for GlobalTheory.strip_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:28.758039+00:00
-- url     : https://prove2.me/submissions/adbc3429-70b4-44ac-957c-99e71811ac4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStripFinitelyManyPrimeFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    (π : Fin n → R) (J : Finset (Fin n)) (x : R) (hx : x ≠ 0) :
    ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧
      ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  induction J using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, x, by simp, by simp⟩
  | @insert j J hj ih =>
    obtain ⟨m, y, hxy, hy⟩ := ih
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using hxy)
    by_cases hp : Prime (π j)
    · obtain ⟨y', hy', hnd⟩ :=
        (FiniteMultiplicity.of_not_isUnit hp.not_unit hy0).exists_eq_pow_mul_and_not_dvd
      refine ⟨Function.update m j (multiplicity (π j) y), y', ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self]
        have hJ : ∏ i ∈ J, π i ^ Function.update m j (multiplicity (π j) y) i
            = ∏ i ∈ J, π i ^ m i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
        rw [hJ, hxy]
        conv_lhs => rw [hy']
        ring
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hnd hdvd
        · exact hy i hi hpi (hdvd.trans (Dvd.intro_left _ hy'.symm))
    · refine ⟨Function.update m j 0, y, ?_, ?_⟩
      · rw [Finset.prod_insert hj, Function.update_self, pow_zero, one_mul]
        rw [hxy]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
      · intro i hi hpi hdvd
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hp hpi
        · exact hy i hi hpi hdvd
end GlobalTheory
