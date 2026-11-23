-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.shannonCapacity_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:43.206074+00:00
-- url     : https://prove2.me/submissions/efd8cf38-46fd-44c8-98f0-8dbe7d8f6d5a

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_le_card

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) [Fintype V] :
    BddAbove (Set.range fun m =>
      ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))) := by
  use (Fintype.card V : ℝ)
  intro x ⟨m, hm⟩
  rw [← hm]
  have hexp_pos : (0 : ℝ) ≤ 1 / (m + 1) := by positivity
  have hcard_pos : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hindep_le : ((strongPower G (m + 1)).indepNum : ℝ) ≤
      (Fintype.card (Fin (m + 1) → V) : ℝ) := by
    exact_mod_cast independenceNumber_le_card (strongPower G (m + 1))
  have hcard_eq : Fintype.card (Fin (m + 1) → V) = (Fintype.card V) ^ (m + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
  calc ((strongPower G (m + 1)).indepNum : ℝ) ^ (1 / (m + 1 : ℝ))
      ≤ (Fintype.card (Fin (m + 1) → V) : ℝ) ^ (1 / (m + 1 : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) hindep_le hexp_pos
    _ = ((Fintype.card V : ℝ) ^ (m + 1 : ℕ)) ^ (1 / (m + 1 : ℝ)) := by
        rw [hcard_eq]; norm_cast
    _ = (Fintype.card V : ℝ) ^ ((m + 1 : ℕ) * (1 / (m + 1 : ℝ))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hcard_pos]
    _ = (Fintype.card V : ℝ) ^ (1 : ℝ) := by
        congr 1; push_cast; field_simp
    _ = Fintype.card V := Real.rpow_one _
end GroupTheoreticShannonCapacity
