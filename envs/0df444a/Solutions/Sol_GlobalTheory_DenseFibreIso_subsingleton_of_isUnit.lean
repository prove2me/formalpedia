-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.subsingleton_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:08.57919+00:00
-- url     : https://prove2.me/submissions/3b89759f-993f-446c-b856-75620ec88d50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseFibreIso
variable {A : Type} [CommRing A]
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution {N : Type} [AddCommGroup N] [Module A N] {a : A}
    (h : ∀ n : N, a • n = 0) (S : Type) [CommRing S] [Algebra A S]
    (hu : IsUnit (algebraMap A S a)) : Subsingleton (S ⊗[A] N) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z with
  | zero => rfl
  | add y z hy hz => rw [hy, hz, add_zero]
  | tmul c n =>
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    have e : c = a • (c * u) := by rw [Algebra.smul_def, mul_comm, _root_.mul_assoc, hu, _root_.mul_one]
    rw [e, TensorProduct.smul_tmul, h, TensorProduct.tmul_zero]
end GlobalTheory.DenseFibreIso
