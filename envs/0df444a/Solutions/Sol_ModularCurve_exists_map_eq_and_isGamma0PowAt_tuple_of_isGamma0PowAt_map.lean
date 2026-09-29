-- Prove2me | solution 1 for ModularCurve.exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5fe1e483-16aa-5367-a387-80ab31871783

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map

set_option autoImplicit false

universe u

open Polynomial

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀) (M' : ℕ) (hM' : IsUnit ((M' : ℕ) : R₀))
    (hh' : ↥M'.primeFactors → Polynomial K)
    (H' : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt (W₀.map (algebraMap R₀ K)) (p : ℕ) (M'.factorization (p : ℕ)) (hh' p)) :
    ∃ hh₀ : ↥M'.primeFactors → Polynomial R₀,
      (fun p => (hh₀ p).map (algebraMap R₀ K)) = hh' ∧
      ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) (hh₀ p) := by
  classical
  have hp : ∀ p : ↥M'.primeFactors, IsUnit (((p : ℕ) : ℕ) : R₀) := fun p =>
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_of_mem_primeFactors p.2)) hM'
  have H : ∀ p : ↥M'.primeFactors, ∃ h₀ : Polynomial R₀, h₀.map (algebraMap R₀ K) = hh' p ∧
      ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) h₀ := fun p =>
    ModularCurve.exists_map_eq_and_isGamma0PowAt_of_isGamma0PowAt_map W₀ (p : ℕ) (M'.factorization (p : ℕ)) (hp p)
      (hh' p) (H' p)
  exact ⟨fun p => (H p).choose, funext fun p => (H p).choose_spec.1, fun p => (H p).choose_spec.2⟩

end S_ModularCurve_exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map
end P2MW
export P2MW.S_ModularCurve_exists_map_eq_and_isGamma0PowAt_tuple_of_isGamma0PowAt_map (solution)
