-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.continuous_galTateRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:36.133249+00:00
-- url     : https://prove2.me/submissions/07d54b93-9b4b-4f92-bf79-98480465fa4d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Theorems.Thm_GroundTheory_Arith_Abelian_continuous_tateRep

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
theorem _root_.solution [Algebra.IsIntegral K L] :
    Continuous (fun p : Gal(L/K) × TateModule ℓ (W.baseChange L).toAffine.Point =>
      galTateRep K L W ℓ p.1 p.2) :=
  continuous_tateRep _ fun P =>
    isOpen_stabilizer_point W (GroundTheory.ProfCoh.stabilizer (galPointsZ K L W).ρ P) P fun _ h => h
end GroundTheory.Arith.Abelian
