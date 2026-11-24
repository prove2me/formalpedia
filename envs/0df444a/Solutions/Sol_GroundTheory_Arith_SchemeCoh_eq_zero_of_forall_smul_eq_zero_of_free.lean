-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.eq_zero_of_forall_smul_eq_zero_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:11.250384+00:00
-- url     : https://prove2.me/submissions/3b6f82f2-99eb-4392-b6fc-2b09623aef63

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal CategoryTheory Abelian
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {a : R} (h : ∀ m : M, a • m = 0) : a = 0 := by
  let b := Module.Free.chooseBasis R M
  obtain ⟨i⟩ := b.index_nonempty
  have := congrArg b.repr (h (b i))
  rw [map_smul, b.repr_self, map_zero, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.single_eq_zero] at this
  exact this
end GroundTheory.Arith.SchemeCoh
