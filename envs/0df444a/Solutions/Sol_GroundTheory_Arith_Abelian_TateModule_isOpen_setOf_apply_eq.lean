-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.TateModule.isOpen_setOf_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:37.471876+00:00
-- url     : https://prove2.me/submissions/af9f8105-f507-460f-8adb-0eebf581e058

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
variable {ℓ : ℕ} {A : Type*} [AddCommGroup A]
namespace GroundTheory.Arith.Abelian
namespace TateModule
theorem _root_.solution (k : ℕ) (a : A) :
    IsOpen {t : TateModule ℓ A | (t : ℕ → A) k = a} := by
  letI : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hc : Continuous (fun f : ℕ → A => f k) := continuous_apply k
  exact isOpen_induced (hc.isOpen_preimage {a} (isOpen_discrete {a}))
end TateModule
end GroundTheory.Arith.Abelian
