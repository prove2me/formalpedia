-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.absNorm_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:08.234346+00:00
-- url     : https://prove2.me/submissions/3a5131b2-672c-4302-b34b-ae7bcd49f711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {p : ℕ} (φ : 𝓞 K →+* ZMod p) : Ideal.absNorm (RingHom.ker φ) = p := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective φ)).toEquiv,
    Nat.card_zmod]
end GlobalTheory.QuadraticZeta
