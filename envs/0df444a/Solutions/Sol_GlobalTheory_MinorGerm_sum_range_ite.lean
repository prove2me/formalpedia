-- Prove2me | solution 1 for GlobalTheory.MinorGerm.sum_range_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:30.152995+00:00
-- url     : https://prove2.me/submissions/dda01a7b-ead2-4b8e-89f5-435a191b7f5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
namespace GlobalTheory.MinorGerm
theorem _root_.solution {M : Type} [AddCommMonoid M] {k : ℕ} (hk : k ≤ N) (F : ℕ → M) :
    ∑ ρ ∈ Finset.range N, (if ρ < k then F ρ else 0) = ∑ ρ ∈ Finset.range k, F ρ := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_range]
  omega
end GlobalTheory.MinorGerm
