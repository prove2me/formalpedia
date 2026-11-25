-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_ltSeries_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:31.367889+00:00
-- url     : https://prove2.me/submissions/83bb6c14-d166-4f15-b120-5b5de59ab55d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
namespace GroundTheory.Arith.Toric
theorem _root_.solution (hinj : Function.Injective (algebraMap R A))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ l' : LTSeries (PrimeSpectrum A), l'.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R A) l'.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal A)
      (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, PrimeSpectrum.ext hQx⟩
  | snoc p x hx ih =>
    obtain ⟨l', hlen, hlast⟩ := ih
    have hle : l'.last.asIdeal.comap (algebraMap R A) ≤ x.asIdeal := by
      have := congrArg PrimeSpectrum.asIdeal hlast
      rw [PrimeSpectrum.comap_asIdeal] at this
      rw [this]
      exact le_of_lt hx
    obtain ⟨Q, hQle, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal l'.last.asIdeal hle
    have hlt : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle fun h => ?_
      have h1 : PrimeSpectrum.comap (algebraMap R A) l'.last = x := by
        rw [h]; exact PrimeSpectrum.ext hQx
      exact (ne_of_lt hx) (hlast.symm.trans h1)
    exact ⟨l'.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], PrimeSpectrum.ext (by simpa using hQx)⟩
end GroundTheory.Arith.Toric
