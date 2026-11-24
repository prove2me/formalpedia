-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.isUnit_algebraMap_xprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:35.567735+00:00
-- url     : https://prove2.me/submissions/c047b40f-fb76-4197-8a98-bcdcdcdd044e

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
theorem _root_.solution {p q : ℕ} {i : Fin p → Fin (n + 1)} {i' : Fin q → Fin (n + 1)}
    (h : Set.range i ⊆ Set.range i') :
    IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i'))
      (xprod i)) := by
  rw [show xprod (A := A) i = ∏ a, X (i a) from rfl, map_prod]
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => ?_
  obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
  refine isUnit_of_dvd_unit ?_ (IsLocalization.Away.algebraMap_isUnit (xprod (A := A) i'))
  rw [← hb]
  exact map_dvd _ (Finset.dvd_prod_of_mem (fun c => X (i' c)) (Finset.mem_univ b))
end GroundTheory.Arith.SchemeCoh.ProjSpace
