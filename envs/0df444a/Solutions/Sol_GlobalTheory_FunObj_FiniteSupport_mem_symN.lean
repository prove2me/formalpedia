-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.mem_symN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:47.346508+00:00
-- url     : https://prove2.me/submissions/d03a5d05-29f6-4b25-be29-b665f093e38e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
import Theorems.Thm_GlobalTheory_RootEx_FJUnipotent_fj_unipotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution (hc : 1 ≤ c) {g : GL (n ⊕ Fin c) k}
    (hg : ∀ r s, symLev c s ≤ symLev c r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) :
    g ∈ symN k n c := by
  unfold symLev at hg
  split_ifs at hg with h
  · obtain ⟨ρ, rfl⟩ := h
    have e1 : (ρ + ρ) / 2 = ρ := by omega
    have e2 : (ρ + ρ + 1) / 2 = ρ := by omega
    rw [e1] at hg
    rw [symN, e1, e2]
    exact ((fj_unipotent k n (ρ + ρ) ρ (by omega) (by omega)).2.1 g).2 hg
  · exact Subgroup.mem_sup_right (Subgroup.subset_closure hg)
end GlobalTheory.FunObj.FiniteSupport
