-- Prove2me | solution 1 for GlobalTheory.InertZeta.RowSpan.sum_smem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:47:51.066535+00:00
-- url     : https://prove2.me/submissions/9e179ad5-8d48-4701-9a06-3eddedd9d45b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
import Theorems.Thm_GlobalTheory_InertZeta_RowSpan_smem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
namespace GlobalTheory.InertZeta.RowSpan
theorem _root_.solution {n : ℕ} {ι : Type} [Fintype ι] {S : Submodule (intL L) (Fin n → L)} {x : ι → L}
    {w : ι → Fin n → L} (hx : ∀ i, x i ∈ intL L) (hw : ∀ i, w i ∈ S) : ∑ i, x i • w i ∈ S :=
  Submodule.sum_mem _ fun i _ => smem (hx i) (hw i)
end GlobalTheory.InertZeta.RowSpan
