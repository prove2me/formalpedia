-- Prove2me | solution 1 for NearlySubadditive.add_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:37.927063+00:00
-- url     : https://prove2.me/submissions/e4415b89-b789-4323-aa4f-92c4e82adbf4

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open NearlySubadditive
variable {f g : ℕ → ℝ} {μ ν : ℝ} {N M : ℕ} {u v : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (h : NearlySubadditive f μ N u) (c : ℝ) :
    NearlySubadditive f μ N fun n ↦ u n + c * n := fun m n hm hmn hn ↦ by
  push_cast
  linarith [h hm hmn hn]
end NearlySubadditive
