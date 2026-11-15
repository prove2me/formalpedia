-- Prove2me | solution 1 for MazurCampaign.no_prime_ge_twenty_three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T03:02:12.601916+00:00
-- url     : https://prove2.me/submissions/e403d8a7-12b2-45c2-a465-767756d7bba0

import Theorems.Thm_MazurP23_exists_point_of_rationalTorsion
import Theorems.Thm_PrimeLocal_local_package_componentFree
import Theorems.Thm_MazurP23_hasGaloisStableCofixedLine_of_fixed_point
import Theorems.Thm_MazurP23_not_hasGaloisStableCofixedLine_of_localData
import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ p : ℕ, p.Prime → 23 ≤ p →
      ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ p := by
  intro p hp hp23 x hx
  obtain ⟨P, hP⟩ := MazurP23.exists_point_of_rationalTorsion E x hx
  obtain ⟨W, Q, hΔ, hQfix, hQord, htwoΔ, htwoc₄, hthreeΔ, hthreec₄,
    htwoQ, hthreeQ, hloc, hpat⟩ :=
    PrimeLocal.local_package_componentFree E hp hp23 P hP
  exact MazurP23.not_hasGaloisStableCofixedLine_of_localData
    W hΔ hp (by omega) htwoΔ htwoc₄ hthreeΔ hthreec₄ hloc hpat
    (MazurP23.hasGaloisStableCofixedLine_of_fixed_point
      W hΔ hp (by omega) htwoΔ htwoc₄ hthreeΔ hthreec₄ hloc hpat
      Q hQfix hQord htwoQ hthreeQ)
