-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.galTateRep_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:38.726427+00:00
-- url     : https://prove2.me/submissions/6bafb419-68cf-44d6-80fe-73d70133aa82

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Theorems.Thm_GroundTheory_Arith_Abelian_tateModule_basis

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
universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution [IsSepClosed L] [W.IsElliptic] (hℓK : (ℓ : K) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W.baseChange L).toAffine.Point)) :=
  tateModule_basis (W.baseChange L) ℓ (by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hℓK)
end GroundTheory.Arith.Abelian
