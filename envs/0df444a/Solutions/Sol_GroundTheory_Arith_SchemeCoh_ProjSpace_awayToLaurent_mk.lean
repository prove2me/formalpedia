-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjSpace.awayToLaurent_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:26.326479+00:00
-- url     : https://prove2.me/submissions/5cfa3dc8-9695-43bd-bcd3-e392df2bf142

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_algebraMap
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
theorem _root_.solution {p : ℕ} (i : Fin p → Fin (n + 1)) (a : MvPolynomial (Fin (n + 1)) A) (N : ℕ) :
    awayToLaurent i (Localization.mk a (ProjTwist.fpow (xprod i) N)) =
      toLaurent A n a * AddMonoidAlgebra.single (-(N • mult i)) 1 := by
  have h1 : (Localization.mk a (ProjTwist.fpow (xprod i) N) : Localization.Away (xprod (A := A) i)) *
      algebraMap (MvPolynomial (Fin (n + 1)) A) _ (xprod i ^ N) =
      algebraMap (MvPolynomial (Fin (n + 1)) A) (Localization.Away (xprod (A := A) i)) a := by
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [mul_comm]⟩
  have h2 := congrArg (awayToLaurent i) h1
  rw [map_mul, awayToLaurent_algebraMap, awayToLaurent_algebraMap, map_pow, toLaurent_xprod,
    AddMonoidAlgebra.single_pow, one_pow] at h2
  rw [← h2, mul_assoc, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul,
    ← AddMonoidAlgebra.one_def, mul_one]
end GroundTheory.Arith.SchemeCoh.ProjSpace
