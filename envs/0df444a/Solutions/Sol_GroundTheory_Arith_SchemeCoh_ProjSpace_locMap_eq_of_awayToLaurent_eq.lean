-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.locMap_eq_of_awayToLaurent_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:40.27667+00:00
-- url     : https://prove2.me/submissions/a6eb82a4-cbbf-4d84-a506-3aaf40cc40d1

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_algebraMap
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_injective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_isUnit_algebraMap_xprod
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_locMap_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



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
theorem _root_.solution {p q : ℕ} {i : Fin p → Fin (n + 1)}
    {i' : Fin q → Fin (n + 1)} (h : Set.range i ⊆ Set.range i')
    {z : Localization.Away (xprod (A := A) i)} {z' : Localization.Away (xprod (A := A) i')}
    (hzz : awayToLaurent i z = awayToLaurent i' z') (x : ProjectiveSpectrum (grading A n))
    (hx : xprod i ∉ x.asHomogeneousIdeal) (hx' : xprod i' ∉ x.asHomogeneousIdeal) :
    ProjTwist.locMap x hx z = ProjTwist.locMap x hx' z' := by
  let can : Localization.Away (xprod (A := A) i) →+* Localization.Away (xprod (A := A) i') :=
    IsLocalization.Away.lift (xprod i) (isUnit_algebraMap_xprod h)
  have hcan : can.comp (algebraMap _ _) = algebraMap _ _ := IsLocalization.lift_comp _
  have h1 : (awayToLaurent i').comp can = awayToLaurent i := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (xprod (A := A) i))
    rw [RingHom.comp_assoc, hcan]
    ext a
    · simp [awayToLaurent_algebraMap]
    · simp [awayToLaurent_algebraMap]
  have h2 : can z = z' := awayToLaurent_injective i' (by rw [← hzz, ← h1]; rfl)
  rw [← h2]
  exact (ProjTwist.locMap_comp can hcan x hx' hx z).symm
end GroundTheory.Arith.SchemeCoh.ProjSpace
