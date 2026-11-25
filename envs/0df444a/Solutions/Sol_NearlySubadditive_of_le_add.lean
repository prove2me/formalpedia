-- Prove2me | solution 1 for NearlySubadditive.of_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:27.159797+00:00
-- url     : https://prove2.me/submissions/4b934c72-30b1-4ab9-9e39-d9cedbf5b756

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
theorem _root_.solution (h : ∀ m n, N ≤ m → N ≤ n → u (m + n) ≤ u m + u n + f (m + n)) :
    NearlySubadditive f μ N u := fun m n hm hmn _ ↦ h m n hm (hm.trans hmn)
end NearlySubadditive
