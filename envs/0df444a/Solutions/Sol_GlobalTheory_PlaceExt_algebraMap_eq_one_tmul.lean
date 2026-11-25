-- Prove2me | solution 1 for GlobalTheory.PlaceExt.algebraMap_eq_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:28:14.222353+00:00
-- url     : https://prove2.me/submissions/81f8284f-c44b-4daf-ba74-34e2ced1a168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
variable {F F' : Type} [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F']
  [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
variable {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain R'] [IsDiscreteValuationRing R']
  [IsLocalHom (algebraMap R R')] [IsFractionRing R F] [IsFractionRing R' F']
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
namespace GlobalTheory.PlaceExt
theorem _root_.solution (r : R) :
    algebraMap R' (F' ⊗[F] L) (algebraMap R R' r) = (1 : F') ⊗ₜ[F] algebraMap R L r := by
  rw [Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R F F', IsScalarTower.algebraMap_apply R F L,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := L),
    TensorProduct.smul_tmul]
end GlobalTheory.PlaceExt
