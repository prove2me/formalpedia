-- Prove2me | solution 1 for GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:24:47.396185+00:00
-- url     : https://prove2.me/submissions/5b6b5885-b4d5-4813-b53a-34386376ea21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_pow_eq_of_tower

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
theorem _root_.solution {R : Type} (K : Type u_1) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hn : IsUnit (Module.finrank K L : R)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  let F := SeparableClosure L
  haveI : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K L F
  haveI : IsSepClosure K F := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois K F := inferInstance
  haveI : NeZero ((Module.finrank K L : ℕ) : F) := ⟨by
    simpa using ((hn.map (algebraMap R K)).map (algebraMap K F)).ne_zero⟩
  obtain ⟨ρ, hρ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K F (algebraMap R K π))
    (Module.finrank K L)
  let E := IntermediateField.adjoin L {ρ}
  haveI : FiniteDimensional L E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ρ)
  haveI : FiniteDimensional K E := Module.Finite.trans L E
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_pow_eq_of_tower K L E F hH hπ hn
    ⟨ρ, IntermediateField.mem_adjoin_simple_self L ρ⟩ (Subtype.ext hρ)
end GlobalTheory.GaloisPowerRoots
