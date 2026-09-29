-- Prove2me | solution 1 for LovaszSchrijver.OddHole.M_FR_entry_eq_zero_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:57:21.436475+00:00
-- url     : https://prove2.me/submissions/40b1daf5-f7da-4330-a574-d494712211c4

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones

namespace LovaszSchrijver.OddHole

theorem aux_mfr0_Q_nonneg {V : Type} (x : Option V → ℝ) (hx : x ∈ Q V) (k : V) :
    0 ≤ x (some k) := by
  unfold Q at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy.2 k with h | h <;> simp [h]
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply]; linarith
  | smul c a _ ha =>
    rw [Pi.smul_apply]
    change 0 ≤ (c : ℝ) * a (some k)
    exact mul_nonneg c.2 ha

theorem aux_mfr0_single_dual_Q {V : Type} [Fintype V] [DecidableEq V] (k : V) :
    (Pi.single (some k) 1 : Option V → ℝ) ∈ dualCone (Q V) := by
  intro x hx
  rw [single_dotProduct, one_mul]
  exact aux_mfr0_Q_nonneg x hx k

theorem aux_mfr0_single_dual_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : V) : (Pi.single (some k) 1 : Option V → ℝ) ∈ dualCone (FR G) := by
  intro x hx
  rw [single_dotProduct, one_mul]
  exact hx.1 k

theorem aux_mfr0_edge_dual_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (i j : V) (hij : G.Adj i j) :
    (Pi.single none 1 - Pi.single (some i) 1 - Pi.single (some j) 1 : Option V → ℝ)
      ∈ dualCone (FR G) := by
  intro x hx
  rw [sub_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  have := hx.2 i j hij
  linarith

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (Y : Matrix (Option V) (Option V) ℝ) (hY : Y ∈ M (FR G) (Q V))
    (i j : V) (hij : G.Adj i j) :
    Y (some i) (some j) = 0 := by
  obtain ⟨_, hdiag, hpos⟩ := hY
  have h1 := hpos _ (aux_mfr0_edge_dual_FR G i j hij) _ (aux_mfr0_single_dual_Q j)
  have h2 := hpos _ (aux_mfr0_single_dual_FR G i) _ (aux_mfr0_single_dual_Q j)
  rw [Matrix.mulVec_single_one] at h1 h2
  rw [sub_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct,
    single_dotProduct] at h1
  rw [single_dotProduct] at h2
  simp only [Matrix.col_apply, one_mul] at h1 h2
  have hd := hdiag j
  linarith
