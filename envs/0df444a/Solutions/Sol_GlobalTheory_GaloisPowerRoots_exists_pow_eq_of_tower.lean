-- Prove2me | solution 1 for GlobalTheory.GaloisPowerRoots.exists_pow_eq_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:15.989517+00:00
-- url     : https://prove2.me/submissions/1b845eeb-8011-44be-9fbb-d071cfd1d186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_pow_eq_of_isGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots
namespace GlobalTheory.GaloisPowerRoots
theorem _root_.solution {R : Type*} (K L E F : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (hn : IsUnit (Module.finrank K L : R))
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [FiniteDimensional K E]
    [Field F] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [IsGalois K F] (ρ : E)
    (hρ : ρ ^ Module.finrank K L = algebraMap K E (algebraMap R K π)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  let M := IntermediateField.normalClosure K E F
  letI : Algebra L M := ((algebraMap E M).comp (algebraMap L E)).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K E M, IsScalarTower.algebraMap_apply K L E]; rfl
  refine exists_pow_eq_of_isGalois K L M hH hπ hn (algebraMap E M ρ) ?_
  rw [← map_pow, hρ, ← IsScalarTower.algebraMap_apply]
end GlobalTheory.GaloisPowerRoots
