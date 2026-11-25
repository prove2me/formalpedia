-- Prove2me | solution 1 for GlobalTheory.CoeffExt.descend_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:02.606061+00:00
-- url     : https://prove2.me/submissions/6659d979-eebb-4af0-a6d7-93c0f671bc7d

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemFiniteCocyclesIffBcrisTensorCoboundary
import Theorems.Thm_GlobalTheory_CoeffExt_funCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CoeffExt.funCoord_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffExt
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
namespace GlobalTheory.CoeffExt
theorem _root_.solution {m k f : ℕ∞} {m' k' d : ℕ} (hd : 0 < d) (hf : f ≠ ⊤)
    (hm : (m' : ℕ∞) * f = d * m) (hk : (k' : ℕ∞) * f = d * k) {β : ℝ} (h : (m' : ℝ) ≤ β * k') :
    ∃ a c : ℕ, m = a ∧ k = c ∧ (a : ℝ) ≤ β * c := by
  lift f to ℕ using hf
  have hmt : m ≠ ⊤ := by
    rintro rfl
    have h1 : ((m' * f : ℕ) : ℕ∞) = ⊤ := by
      push_cast
      simpa [ENat.mul_top, hd.ne'] using hm
    exact ENat.natCast_ne_top _ h1
  have hkt : k ≠ ⊤ := by
    rintro rfl
    have h1 : ((k' * f : ℕ) : ℕ∞) = ⊤ := by
      push_cast
      simpa [ENat.mul_top, hd.ne'] using hk
    exact ENat.natCast_ne_top _ h1
  lift m to ℕ using hmt
  lift k to ℕ using hkt
  refine ⟨m, k, rfl, rfl, ?_⟩
  have hm' : (d : ℝ) * m = m' * f := by exact_mod_cast hm.symm
  have hk' : (d : ℝ) * k = k' * f := by exact_mod_cast hk.symm
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd

  have hle : (d : ℝ) * m ≤ d * (β * k) := by
    rw [hm', show (d : ℝ) * (β * k) = β * (d * k) by ring, hk']
    calc (m' : ℝ) * f ≤ (β * k') * f := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg f)
      _ = β * (k' * f) := by ring
  exact le_of_mul_le_mul_left hle hdpos
end GlobalTheory.CoeffExt
