-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.card_nsmul_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:36.726002+00:00
-- url     : https://prove2.me/submissions/f9a7aaed-452f-4b2d-a9ea-f9383746ae8d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Theorems.Thm_GroundTheory_Arith_Abelian_card_torsionBy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (hℓF : (ℓ : F) ≠ 0) (k : ℕ) :
    Nat.card {P : W.toAffine.Point // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2 := by
  rw [← card_torsionBy W (n := ℓ ^ k) (by push_cast; exact pow_ne_zero _ hℓF)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => torsionBy.nsmul_iff.symm)
end GroundTheory.Arith.Abelian
