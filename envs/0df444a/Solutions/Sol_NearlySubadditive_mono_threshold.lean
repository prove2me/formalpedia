-- Prove2me | solution 1 for NearlySubadditive.mono_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:22.080341+00:00
-- url     : https://prove2.me/submissions/92e87023-b2fb-4bce-a1a1-732fb3edf34b

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
theorem _root_.solution (h : NearlySubadditive f μ N u) (hNM : N ≤ M) :
    NearlySubadditive f μ M u :=
  h.mono le_rfl le_rfl hNM
end NearlySubadditive
