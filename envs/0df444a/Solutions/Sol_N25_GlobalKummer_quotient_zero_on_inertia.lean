-- Prove2me | solution 1 for N25.GlobalKummer.quotient_zero_on_inertia
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:13.297202+00:00
-- url     : https://prove2.me/submissions/4a77f650-e039-40f7-a8f1-1b9d991f282b

import Definitions.Def_N25_GlobalKummerQuotient
import Theorems.Thm_N25_kummer_unramified
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

/-- The actual quotient cocycle is zero on inertia at every allowed good prime. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : ℓ ≠ 5) (hℓ71 : ℓ ≠ 71)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    quotientDivisionCocycle hPhi K2 P Q hQ σ = 0 := by
  have hc : divisionCocycle hPhi P Q hQ σ = 0 := by
    apply Subtype.ext
    exact kummer_unramified hPhi (P : J) Q P.property hQ hℓ5 hℓ71 A hA σ hσ
  change K2.q (divisionCocycle hPhi P Q hQ σ) = 0
  rw [hc]
  exact K2.q.map_zero

end N25.GlobalKummer
