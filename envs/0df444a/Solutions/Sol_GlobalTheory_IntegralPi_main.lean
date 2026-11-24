-- Prove2me | solution 1 for GlobalTheory.IntegralPi.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:49.553029+00:00
-- url     : https://prove2.me/submissions/a6593360-5464-420c-9e84-e5fa390fd556

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Theorems.Thm_GlobalTheory_IntegralPi_isIntegral_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralPi
open Polynomial
namespace GlobalTheory.IntegralPi
theorem _root_.solution : ∀ {O : Type} [inst : CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [inst_2 : (i : ι) → CommRing (R i)] [inst_3 : (i : ι) → Algebra O (R i)] (x : (i : ι) → R i),
    (∀ (i : ι), IsIntegral O (x i)) → IsIntegral O x :=
  fun x hx => isIntegral_pi x hx
end GlobalTheory.IntegralPi
