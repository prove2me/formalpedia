-- Prove2me | solution 1 for GlobalTheory.ConjugateAlgebraLemmas.conjAlg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:26.626215+00:00
-- url     : https://prove2.me/submissions/e353a7fd-25fa-4d14-a60b-cb318816941e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjAlgApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateAlgebraLemmas
open Matrix
namespace GlobalTheory.ConjugateAlgebraLemmas
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    conjAlg g M = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) := rfl
end GlobalTheory.ConjugateAlgebraLemmas
