-- Prove2me | solution 1 for GeneralCK.eta_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:53:25.308182+00:00
-- url     : https://prove2.me/submissions/1653d0c2-3bc2-41aa-b181-9038f3511e1b

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_H_strictMonoOn
import Theorems.Thm_GeneralCK_entropyInverse_spec
import Theorems.Thm_GeneralCK_eta_eq_profile

open scoped BigOperators
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]











end GeneralCK

namespace GeneralCK



theorem entropyInverse_pos {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    0 < entropyInverse h := by
  obtain ⟨hv, _, heq⟩ := entropyInverse_spec h0.le h1
  apply lt_of_le_of_ne hv
  intro he
  rw [← he, H_zero] at heq
  linarith

theorem entropyInverse_mono {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    entropyInverse a ≤ entropyInverse b := by
  obtain ⟨ha0, ha1, hea⟩ := entropyInverse_spec ha (hab.trans hb)
  obtain ⟨hb0, hb1, heb⟩ := entropyInverse_spec (ha.trans hab) hb
  by_contra hn
  have := H_strictMonoOn ⟨hb0, hb1⟩ ⟨ha0, ha1⟩ (lt_of_not_ge hn)
  rw [hea, heb] at this
  linarith

theorem J_nonneg {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) : 0 ≤ J v := by
  apply div_nonneg _ log_two_pos.le
  apply Real.log_nonneg
  apply (le_div_iff₀ hv).2
  linarith

theorem J_antitone {u v : ℝ} (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u ≤ v) :
    J v ≤ J u := by
  have hv0 : 0 < v := hu.trans_le huv
  apply (div_le_div_iff_of_pos_right log_two_pos).2
  apply Real.log_le_log (div_pos (by linarith) hv0)
  apply (div_le_div_iff₀ hv0 hu).2
  nlinarith





end GeneralCK

open GeneralCK in
theorem solution : AntitoneOn eta (Set.Ioc 0 1) := by
  intro a ha b hb hab
  rw [eta_eq_profile ha.1.le ha.2, eta_eq_profile hb.1.le hb.2]
  have huv := entropyInverse_mono ha.1.le hb.2 hab
  have hu := entropyInverse_pos ha.1 ha.2
  have hv := entropyInverse_pos hb.1 hb.2
  have hu' := (entropyInverse_spec ha.1.le ha.2).2.1
  have hv' := (entropyInverse_spec hb.1.le hb.2).2.1
  exact mul_le_mul (by linarith) (J_antitone hu hv' huv)
    (J_nonneg hv hv') (by linarith)
