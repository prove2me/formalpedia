-- Prove2me | solution 1 for NearlySubadditive.mono_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:13.690513+00:00
-- url     : https://prove2.me/submissions/74711eec-ac94-4d15-b2a3-abb9a7107542

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
variable {f g : ℕ → ℝ} {μ ν : ℝ} {N M : ℕ} {u v : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (h : NearlySubadditive f μ N u) (hνμ : ν ≤ μ) : NearlySubadditive f ν N u :=
  h.mono le_rfl hνμ le_rfl
end NearlySubadditive
