-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.tateRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:22.12991+00:00
-- url     : https://prove2.me/submissions/cc5f9964-e96e-47f0-9454-773d85ecdec9

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
theorem _root_.solution {G : Type*} [Monoid G] (φ : G →* AddMonoid.End A) (g : G)
    (t : TateModule ℓ A) (k : ℕ) :
    ((tateRep φ g t : TateModule ℓ A) : ℕ → A) k = φ g ((t : ℕ → A) k) :=
  rfl
end GroundTheory.Arith.Abelian
