-- Prove2me | solution 1 for GlobalTheory.mk_addMonoidHom_le_of_surjective_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:38.956834+00:00
-- url     : https://prove2.me/submissions/ae06f545-3f31-4b87-8c25-421a3469a902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A A' X Y : Type} [AddCommGroup A]
    [AddCommGroup A'] [AddCommGroup X] [AddCommGroup Y] (f : A →+ A') (hf : Surjective f)
    (ι : X →+ Y) (hι : Injective ι) : #(A' →+ X) ≤ #(A →+ Y) := by
  refine mk_le_of_injective (f := fun g => (ι.comp g).comp f) ?_
  intro g h hgh
  ext x
  obtain ⟨a, rfl⟩ := hf x
  exact hι (DFunLike.congr_fun hgh a)
end GlobalTheory
