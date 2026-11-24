-- Prove2me | solution 1 for GlobalTheory.ConormalDer.formallySmooth_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:47.334819+00:00
-- url     : https://prove2.me/submissions/9ea21c11-91ab-4bba-bca5-2d413fac12ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationExtendingCotangentForm
import Theorems.Thm_GlobalTheory_ConormalDer_formallySmooth_of_charZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.ConormalDer
namespace GlobalTheory.ConormalDer
theorem _root_.solution (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (hu : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) :
    Algebra.FormallySmooth R (ResidueField B) := by
  let K := FractionRing R
  have hu' : ∀ c : nonZeroDivisors R, IsUnit (algebraMap R B c) := fun c =>
    hu c (nonZeroDivisors.ne_zero c.2)
  letI : Algebra K B := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hu').toAlgebra
  haveI : IsScalarTower R K B := IsScalarTower.of_algebraMap_eq fun c =>
    (IsLocalization.lift_eq hu' c).symm
  haveI : IsScalarTower R K (ResidueField B) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K B (ResidueField B), ← IsScalarTower.algebraMap_apply R K B,
      ← IsScalarTower.algebraMap_apply]
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R
  haveI : Algebra.FormallySmooth K (ResidueField B) := formallySmooth_of_charZero K _
  haveI : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  exact .comp R K (ResidueField B)
end GlobalTheory.ConormalDer
