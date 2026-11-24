-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.existsUnique_of_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:13.636948+00:00
-- url     : https://prove2.me/submissions/1f4af8cd-4968-4526-a56a-1f9b3ac9e5a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k) := by
  obtain ⟨x, g, hg, rfl⟩ := exists_of_mem_R hr
  refine ⟨(x, ⟨g, hg⟩), rfl, ?_⟩
  rintro ⟨y, h, hh⟩ e
  have hxy : y = x := by
    apply Units.ext
    rw [← toBlocks₁₁_embX_mul x hg, ← toBlocks₁₁_embX_mul y hh]
    exact congrArg (fun u : GL (n ⊕ Fin c) k => u.val.toBlocks₁₁) e.symm
  subst hxy
  have : g = h := mul_left_cancel e
  subst this
  rfl
end GlobalTheory.RootEx.Radical
