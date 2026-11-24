-- Prove2me | solution 1 for GlobalTheory.T.relIndex_conj_integralGL_column_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:15.41459+00:00
-- url     : https://prove2.me/submissions/8e20b038-6376-4f53-b4e9-9bc016c1903c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruenceStatement
import Theorems.Thm_GlobalTheory_IndexCol_relIndex_conj_col


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S → ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) → (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) → ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) → ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  first | exact @GlobalTheory.IndexCol.relIndex_conj_col | exact GlobalTheory.IndexCol.relIndex_conj_col | (intros; apply GlobalTheory.IndexCol.relIndex_conj_col <;> assumption)
end _root_.GlobalTheory.T
