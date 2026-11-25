-- Prove2me | solution 1 for NearlySubadditive.lim_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:52.593266+00:00
-- url     : https://prove2.me/submissions/230f9cc3-0fba-4c2f-8381-a6655078a8aa

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window
public import Theorems.Thm_NearlySubadditive_mono

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hbdd : BddBelow (range fun n ↦ u n / n)) {k : ℕ} (hN : N ≤ k) (hk : k ≠ 0) :
    NearlySubadditive.lim N u ≤ u k / k := by
  rw [NearlySubadditive.lim]
  exact csInf_le (hbdd.mono (image_subset_range _ _)) ⟨k, max_le hN (by omega), rfl⟩
end NearlySubadditive
