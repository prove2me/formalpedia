-- Prove2me | solution 1 for GlobalTheory.QuotInt.block_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:58.818822+00:00
-- url     : https://prove2.me/submissions/ead58626-c50f-4263-838e-537733c811e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.QuotInt
theorem _root_.solution {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) : u.val.toBlocks₁₁ = 1 := by
  have := ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p).1 u).1 hu
  ext i j
  have h := this (Sum.inl i) (Sum.inl j) (le_refl _)
  simp only [toBlocks₁₁, of_apply, h, Matrix.one_apply, Sum.inl.injEq]
end GlobalTheory.QuotInt
