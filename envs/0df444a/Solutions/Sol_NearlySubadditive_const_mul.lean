-- Prove2me | solution 1 for NearlySubadditive.const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:44.27177+00:00
-- url     : https://prove2.me/submissions/ce71bd49-6f08-4150-b103-38b30c466d02

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
theorem _root_.solution (h : NearlySubadditive f μ N u) {c : ℝ} (hc : 0 ≤ c) :
    NearlySubadditive (fun n ↦ c * f n) μ N fun n ↦ c * u n := fun m n hm hmn hn ↦ by
  linarith [mul_le_mul_of_nonneg_left (h hm hmn hn) hc]
end NearlySubadditive
