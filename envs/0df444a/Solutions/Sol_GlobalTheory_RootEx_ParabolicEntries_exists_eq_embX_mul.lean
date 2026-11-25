-- Prove2me | solution 1 for GlobalTheory.RootEx.ParabolicEntries.exists_eq_embX_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:38.179826+00:00
-- url     : https://prove2.me/submissions/c1fff8f0-f291-4035-94db-8a7b03736e33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
import Theorems.Thm_GlobalTheory_RootEx_ParabolicEntries_embX_mem
import Theorems.Thm_P2M_GlobalTheory_RootEx_ParabolicEntries_toBlocks___mul_ddd2957152e4
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ParabolicEntries
theorem _root_.solution {L : ℕ} {b : Fin c → ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ parGroup k n L b) :
    ∃ (x : GL n k) (u : GL (n ⊕ Fin c) k), Uni (Sum.elim (fun _ => L) b) u.val ∧ g = embX c x * u := by
  have h1 : ((1 : GL (n ⊕ Fin c) k)).val.toBlocks₁₁ = 1 := by
    ext r s
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  let x : GL n k := ⟨g.val.toBlocks₁₁, (g⁻¹).val.toBlocks₁₁,
    by rw [← toBlocks₁₁_mul hg (inv_mem hg), mul_inv_cancel, h1],
    by rw [← toBlocks₁₁_mul (inv_mem hg) hg, inv_mul_cancel, h1]⟩
  refine ⟨x, embX c x⁻¹ * g, ?_, by rw [map_inv, mul_inv_cancel_left]⟩
  have hm : embX c x⁻¹ * g ∈ parGroup k n L b := mul_mem (embX_mem L b _) hg
  have h11 : (embX c x⁻¹ * g).val.toBlocks₁₁ = 1 := by
    rw [toBlocks₁₁_mul (embX_mem L b _) hg, embX_val, Matrix.toBlocks_fromBlocks₁₁]
    exact x.inv_mul
  intro r s hrs
  by_cases hor : r.isRight ∨ s.isRight
  · exact hm r s hor hrs
  · rcases r with r | r <;> rcases s with s | s
    · have := congrFun (congrFun h11 r) s
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
      rw [this]
      simp [Matrix.one_apply]
    all_goals simp at hor
end GlobalTheory.RootEx.ParabolicEntries
