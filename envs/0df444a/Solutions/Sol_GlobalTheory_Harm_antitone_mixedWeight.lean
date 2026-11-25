-- Prove2me | solution 1 for GlobalTheory.Harm.antitone_mixedWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:33.224728+00:00
-- url     : https://prove2.me/submissions/72219037-599b-48f2-b13d-20f7a8bdd5ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
import Theorems.Thm_GlobalTheory_Harm_mixedWeight_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset
namespace GlobalTheory.Harm
namespace _root_.GlobalTheory.Harm
theorem _root_.solution (m : ℕ) {p q : ℕ} {a : Fin p → ℕ} {b : Fin q → ℕ}
    (ha : Antitone a) (hb : Antitone b) : Antitone (_root_.GlobalTheory.Harm.mixedWeight m a b) := by
  intro k l hkl
  have hkl' : (k : ℕ) ≤ l := hkl
  simp only [_root_.GlobalTheory.Harm.mixedWeight_apply]
  have hA : (if h : (l : ℕ) < p then (a ⟨l, h⟩ : ℤ) else 0) ≤
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast ha (Fin.mk_le_mk.mpr hkl')
  have hB : (if h : m - 1 - (k : ℕ) < q then (b ⟨m - 1 - k, h⟩ : ℤ) else 0) ≤
      (if h : m - 1 - (l : ℕ) < q then (b ⟨m - 1 - l, h⟩ : ℤ) else 0) := by
    split_ifs <;> first
      | omega | positivity | exact le_rfl | exact_mod_cast hb (Fin.mk_le_mk.mpr (by omega))
  linarith
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
