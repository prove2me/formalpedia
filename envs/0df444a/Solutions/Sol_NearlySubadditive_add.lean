-- Prove2me | solution 1 for NearlySubadditive.add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:36.950828+00:00
-- url     : https://prove2.me/submissions/7c23ad0f-b0c4-4b50-b4e5-4c7f4975baa5

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
theorem _root_.solution (h : NearlySubadditive f μ N u) (h' : NearlySubadditive g μ N v) :
    NearlySubadditive (f + g) μ N (u + v) := fun m n hm hmn hn ↦ by
  simp only [Pi.add_apply]
  linarith [h hm hmn hn, h' hm hmn hn]
end NearlySubadditive
