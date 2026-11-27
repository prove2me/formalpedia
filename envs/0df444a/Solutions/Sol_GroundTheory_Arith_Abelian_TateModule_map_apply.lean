-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.TateModule.map_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:18.436563+00:00
-- url     : https://prove2.me/submissions/a4527596-0fc1-4303-a68c-357771e8044b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule

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
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
namespace GroundTheory.Arith.Abelian
namespace TateModule
theorem _root_.solution (f : A →+ A) (t : TateModule ℓ A) (k : ℕ) :
    ((TateModule.map f t : TateModule ℓ A) : ℕ → A) k = f ((t : ℕ → A) k) :=
  rfl
end TateModule
end GroundTheory.Arith.Abelian
