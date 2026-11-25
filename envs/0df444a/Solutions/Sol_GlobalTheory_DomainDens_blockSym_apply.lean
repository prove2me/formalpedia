-- Prove2me | solution 1 for GlobalTheory.DomainDens.blockSym_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:02.980188+00:00
-- url     : https://prove2.me/submissions/b74bc866-5fc4-4d78-87d7-a3cf189c657c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_BlockSymApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.DomainDens
namespace GlobalTheory.DomainDens
theorem _root_.solution {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)
    (i j : Fin p) : blockSym h τ i j =
      ∑ b : Fin q, X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b)) := rfl
end GlobalTheory.DomainDens
