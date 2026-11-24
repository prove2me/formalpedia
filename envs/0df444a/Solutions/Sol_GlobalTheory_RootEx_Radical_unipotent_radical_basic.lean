-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.unipotent_radical_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:19:13.238922+00:00
-- url     : https://prove2.me/submissions/937609ed-137e-484a-8299-5eb730f642ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_conj
import Theorems.Thm_GlobalTheory_RootEx_Radical_existsUnique_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_Radical_simpleSum_eq_zero
import Theorems.Thm_GlobalTheory_RootEx_Radical_rowE_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_colE_mem

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
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ N k n c p ↔ InN p g) ∧ (∀ g ∈ N k n c p, ∀ h ∈ N k n c p, simpleSum (g * h) = simpleSum g + simpleSum h) ∧ (∀ g ∈ N k n c p, Matrix.GeneralLinearGroup.det g = 1) ∧ (∀ (x : GL n k), ∀ g ∈ N k n c p, embX c x * g * (embX c x)⁻¹ ∈ N k n c p ∧ simpleSum (embX c x * g * (embX c x)⁻¹) = simpleSum g) ∧ (∀ r ∈ R k n c p, ∃! xg : GL n k × N k n c p, r = embX c xg.1 * (xg.2 : GL (n ⊕ Fin c) k)) ∧ (∀ (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k), (∀ r s, lev p s ≤ lev p r → M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) → M.det = 1) ∧ (∀ (l : ℕ) (u : n → k), l < p → rowE c l u ∈ N k n c p ∧ simpleSum (rowE c l u) = 0) ∧ ∀ (i : ℕ) (β : n → k), p < i → colE c i β ∈ N k n c p ∧ simpleSum (colE c i β) = 0 := by
  intro k _ n _ _ c p
  refine ⟨mem_N_iff, fun g hg h hh => simpleSum_mul hg hh, fun g hg => ?_,
    fun x g hg => ⟨conj_mem x hg, simpleSum_conj x g⟩, fun r hr => existsUnique_of_mem_R hr,
    fun M hM => Uni.det (b := lev p) hM,
    fun l u hl => ⟨rowE_mem u hl, simpleSum_eq_zero fun _ _ => rfl⟩,
    fun i β hi => ⟨colE_mem β hi, simpleSum_eq_zero fun _ _ => rfl⟩⟩
  apply Units.ext
  exact Uni.det (b := lev p) ((mem_N_iff g).1 hg)
end GlobalTheory.RootEx.Radical
