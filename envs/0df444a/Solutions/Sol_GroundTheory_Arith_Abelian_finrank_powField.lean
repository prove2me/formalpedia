-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.finrank_powField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:28.677177+00:00
-- url     : https://prove2.me/submissions/7fa15a0e-f748-4fde-9a18-8827a9e9aeae

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_relfinrank_adjoin_genX_pow
import Theorems.Thm_GroundTheory_Arith_Abelian_relfinrank_powField
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_adjoin_genX
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : Module.finrank (powField E p) E.toAffine.FunctionField = p := by
  have hx : F⟮genX E ^ p⟯ ≤ F⟮genX E⟯ :=
    adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self F _) p)
  have hle : F⟮genX E ^ p⟯ ≤ powField E p := adjoin_simple_le_iff.mpr (subset_adjoin F _ (by simp))
  have t1 := relfinrank_mul_relfinrank hx (le_top : F⟮genX E⟯ ≤ ⊤)
  have t2 := relfinrank_mul_relfinrank hle (le_top : powField E p ≤ ⊤)
  rw [relfinrank_adjoin_genX_pow, relfinrank_top_right, finrank_adjoin_genX] at t1
  rw [relfinrank_powField, ← t1, relfinrank_top_right] at t2
  omega
end GroundTheory.Arith.Abelian
