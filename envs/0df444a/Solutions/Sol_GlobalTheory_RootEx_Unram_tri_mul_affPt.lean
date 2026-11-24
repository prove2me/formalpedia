-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.tri_mul_affPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:15.859068+00:00
-- url     : https://prove2.me/submissions/f9921c57-29f7-49ef-a10b-5bee2297e03d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.Unram
theorem _root_.solution {p : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hM : M.BlockTriangular (lev p))
    (x₀ : Matrix n n' k) (e) (i : Fin c) (r : n ⊕ Fin c) (hr : i.val + 1 ≤ lev p r) :
    (M * affPt (c := c) p x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) r (Sum.inr i.castSucc) = M r (Sum.inr i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)]
  · simp [affPt, basePt, Free]
  · intro s _ hs
    by_cases h : lev p s < lev p r
    · rw [hM h, zero_mul]
    · rcases s with s | s
      · have : ¬ p < i.val + 1 := by simp only [lev, Sum.elim_inl] at h hr; omega
        simp [affPt, basePt, Free, this]
      · have h1 : s.val ≠ i.val := fun e => hs (by rw [Fin.ext e])
        have : ¬ s < i := by
          rw [Fin.lt_def]
          simp only [lev, Sum.elim_inr] at h hr; omega
        simp [affPt, basePt, Free, this, h1]
  · simp
end GlobalTheory.RootEx.Unram
