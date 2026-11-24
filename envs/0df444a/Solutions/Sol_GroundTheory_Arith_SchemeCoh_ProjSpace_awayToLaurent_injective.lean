-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.awayToLaurent_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:49.871804+00:00
-- url     : https://prove2.me/submissions/39c6a078-60d7-4857-a47a-51cc417e5cca

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_toLaurent_injective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_mk
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
theorem _root_.solution {p : ℕ} (i : Fin p → Fin (n + 1)) :
    Function.Injective (awayToLaurent (A := A) i) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  induction z using Localization.induction_on with
  | H x =>
    obtain ⟨a, ⟨s, N, rfl⟩⟩ := x
    change awayToLaurent i (Localization.mk a (ProjTwist.fpow (xprod i) N)) = 0 at hz
    rw [awayToLaurent_mk] at hz
    have ha : toLaurent A n a = 0 := by
      have := congrArg (· * AddMonoidAlgebra.single (N • mult i) (1 : A)) hz
      simp only [zero_mul, mul_assoc] at this
      rwa [AddMonoidAlgebra.single_mul_single, neg_add_cancel, mul_one, ← AddMonoidAlgebra.one_def,
        mul_one] at this
    rw [← map_zero (toLaurent A n)] at ha
    rw [toLaurent_injective ha]
    exact Localization.mk_zero _
end GroundTheory.Arith.SchemeCoh.ProjSpace
