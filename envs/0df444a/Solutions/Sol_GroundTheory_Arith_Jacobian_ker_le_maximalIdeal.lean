-- Prove2me | solution 1 for GroundTheory.Arith.Jacobian.ker_le_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:30.903069+00:00
-- url     : https://prove2.me/submissions/f1861f69-54d7-4ffc-8eb5-b94ad82d8ead

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Jacobian
open IsLocalRing TensorProduct
universe u
noncomputable section
variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]
variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S]
include hsurj
namespace GroundTheory.Arith.Jacobian
theorem _root_.solution : RingHom.ker (algebraMap P S) ≤ maximalIdeal P := by
  intro x hx
  rw [← comap_maximalIdeal_eq hsurj, Ideal.mem_comap, RingHom.mem_ker.1 hx]
  exact zero_mem _
end GroundTheory.Arith.Jacobian
