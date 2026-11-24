-- Prove2me | solution 1 for GlobalTheory.FullFlag.free_baseChange_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:02.69085+00:00
-- url     : https://prove2.me/submissions/000ee484-ca17-4e97-8f1f-22bebf5b465b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution {L S T : Type*} [AddCommGroup L] [Module R L] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) [Module.Free S (S ⊗[R] L)] :
    Module.Free T (T ⊗[R] L) := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun r => (φ.commutes r).symm
  exact Module.Free.of_equiv (AlgebraTensorModule.cancelBaseChange R S T T L)
end GlobalTheory.FullFlag
