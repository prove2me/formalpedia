-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.res_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:45.520481+00:00
-- url     : https://prove2.me/submissions/2c51f427-b1cb-41d5-884e-021643393beb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_val_theta
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_LDeg_mono
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_locMap_eq_of_awayToLaurent_eq
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
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


attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
namespace GroundTheory.Arith.SchemeCoh.ProjSpace
theorem _root_.solution {p q : ℕ} {i : Fin (p + 1) → Fin (n + 1)} {i' : Fin (q + 1) → Fin (n + 1)}
    (h : Set.range i ⊆ Set.range i') (hle : inter (cover A n) i' ≤ inter (cover A n) i) (k : ℤ)
    (ℓ : LDeg A (Set.range i) k) :
    res (twistAb A n k) hle (theta i k ℓ) = theta i' k ⟨ℓ.1, LDeg_mono h k ℓ.2⟩ := by
  apply ProjTwist.ext
  funext x
  change ProjTwist.val (theta i k ℓ) ⟨x.1, hle x.2⟩ = _
  rw [val_theta, val_theta]
  apply locMap_eq_of_awayToLaurent_eq h
  rw [← awayDegEquiv_apply, ← awayDegEquiv_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
end GroundTheory.Arith.SchemeCoh.ProjSpace
