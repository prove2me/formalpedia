-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.relfinrank_adjoin_genX_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:10.215657+00:00
-- url     : https://prove2.me/submissions/8605beb6-fca2-4786-8240-a47589b84e16

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_fieldRange_ratEmb
import Theorems.Thm_GroundTheory_Arith_Abelian_map_top_eq_fieldRange
import Theorems.Thm_GroundTheory_Arith_Abelian_ratEmb_X


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
theorem _root_.solution :
    relfinrank F⟮genX E ^ p⟯ F⟮genX E⟯ = p := by
  have hE0 : F⟮genX E ^ p⟯ = (F⟮(RatFunc.X : RatFunc F) ^ p⟯).map (ratEmb E) := by
    rw [adjoin_map, Set.image_singleton, map_pow, ratEmb_X]
  have hE1 : F⟮genX E⟯ = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E) := by
    rw [map_top_eq_fieldRange, fieldRange_ratEmb]
  have hX : (RatFunc.X : RatFunc F) ^ p = algebraMap F[X] (RatFunc F) (X ^ p) := by
    rw [map_pow, RatFunc.algebraMap_X]
  rw [hE0, hE1, relfinrank_map_map, relfinrank_top_right, RatFunc.finrank_eq_max_natDegree, hX,
    RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_X_pow, natDegree_one, max_eq_left
    (Nat.zero_le _)]
end GroundTheory.Arith.Abelian
