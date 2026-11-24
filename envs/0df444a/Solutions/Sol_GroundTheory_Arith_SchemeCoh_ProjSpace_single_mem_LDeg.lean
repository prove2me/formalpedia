-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.single_mem_LDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:45.189797+00:00
-- url     : https://prove2.me/submissions/067c3e80-7427-4221-82e7-ca0746ef462b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent

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
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {s : Set (Fin (n + 1))} {k : ℤ} {m : Fin (n + 1) → ℤ} (hm : Allowed s k m)
    (c : A) : AddMonoidAlgebra.single m c ∈ LDeg A s k := by
  classical
  intro m' h
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h
  split_ifs at h with he
  · exact he ▸ hm
  · exact (h rfl).elim
end GroundTheory.Arith.SchemeCoh.ProjSpace
