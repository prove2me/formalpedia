-- Prove2me | solution 1 for GlobalTheory.MinorGerm.val_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:43.394229+00:00
-- url     : https://prove2.me/submissions/e408e8b2-c154-4547-b763-967a27f82d9a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_val_nat_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
namespace GlobalTheory.MinorGerm
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hv : v (l : C) = 1) {n : ℕ} (hn : ¬ l ∣ n) :
    v (n : C) = 0 := by
  classical
  have hpos := val_nat_nonneg v n
  have hcop : Nat.Coprime n l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hl.one_lt
  have hq : n * a = l * (n * a / l) + 1 := by
    have h := Nat.div_add_mod (n * a) l
    rw [ha] at h
    exact h.symm
  have h01 : (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
  by_contra hne
  have hlt : 0 < v (n : C) := lt_of_le_of_ne hpos (Ne.symm hne)
  have h1 : 0 < v ((n : C) * a) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_nat_nonneg v a))
  have h2 : 0 < v ((l : C) * ((n * a / l : ℕ) : C)) := by
    rw [AddValuation.map_mul, hv]
    exact lt_of_lt_of_le h01 (le_add_of_nonneg_right (val_nat_nonneg v _))
  have hC : (1 : C) = (n : C) * a - (l : C) * ((n * a / l : ℕ) : C) := by
    have h := congrArg (fun x : ℕ => (x : C)) hq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at h
    rw [h]
    ring
  have h3 := AddValuation.map_sub v ((n : C) * a) ((l : C) * ((n * a / l : ℕ) : C))
  rw [← hC, AddValuation.map_one] at h3
  exact absurd h3 (not_le.2 (lt_min h1 h2))
end GlobalTheory.MinorGerm
