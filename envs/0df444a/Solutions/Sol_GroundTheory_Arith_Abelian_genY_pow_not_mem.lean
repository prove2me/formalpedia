-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.genY_pow_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:09.145223+00:00
-- url     : https://prove2.me/submissions/01f97317-5b55-4f14-bac1-e1a83467f833

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_mem_frobImage
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_not_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : genY E ^ p ∉ F⟮genX E ^ p⟯ := by
  intro h
  have hle : F⟮genX E ^ p⟯ ≤ frobImage E p F⟮genX E⟯ := by
    rw [adjoin_le_iff]
    rintro w rfl
    exact (mem_frobImage E p).mpr ⟨genX E, mem_adjoin_simple_self F _, rfl⟩
  obtain ⟨g, hg, hgy⟩ := (mem_frobImage E p).mp (hle h)
  have : g = genY E := frobenius_inj E.toAffine.FunctionField p hgy
  exact genY_not_mem E (this ▸ hg)
end GroundTheory.Arith.Abelian
