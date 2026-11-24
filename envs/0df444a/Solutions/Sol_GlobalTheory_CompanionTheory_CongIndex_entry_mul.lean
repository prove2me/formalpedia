-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CongIndex.entry_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:44.049795+00:00
-- url     : https://prove2.me/submissions/e8af5f67-6794-451c-8adc-cfc088630bfa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ValZpowIff
import Theorems.Thm_GlobalTheory_CompanionTheory_CongIndex_pow_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CongIndex
open ValuativeRel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}
namespace GlobalTheory.CompanionTheory.CongIndex
theorem _root_.solution {ϖ : k} (h1 : valuation k ϖ < 1) {c : Fin N → Fin N → ℕ} {i j : Fin N}
    (hij : i ≠ j) (hc : ∀ l, c i j + 1 ≤ c i l + c l j) {g h : GL (Fin N) k}
    (hg : g ∈ Kset ϖ c) (hh : h ∈ Kset ϖ c) :
    ∃ e : k, valuation k e ≤ valuation k (ϖ ^ (c i j + 1)) ∧
      ((g * h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
        (g : Matrix (Fin N) (Fin N) k) i j + (h : Matrix (Fin N) (Fin N) k) i j + e := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) with hA
  set B : Matrix (Fin N) (Fin N) k := (h : Matrix (Fin N) (Fin N) k) with hB
  refine ⟨((A - 1) * (B - 1)) i j, ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine (valuation k).map_sum_le fun l _ => ?_
    rw [map_mul]
    have e1 : valuation k ((A - 1) i l) ≤ valuation k (ϖ ^ c i l) := hg i l
    have e2 : valuation k ((B - 1) l j) ≤ valuation k (ϖ ^ c l j) := hh l j
    refine (mul_le_mul' e1 e2).trans ?_
    rw [← map_mul, ← pow_add]
    exact pow_le_of_le h1 (hc l)
  · have : ((g * h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = A + B - 1 + (A - 1) * (B - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [this]
    simp [Matrix.one_apply_ne hij]
end GlobalTheory.CompanionTheory.CongIndex
