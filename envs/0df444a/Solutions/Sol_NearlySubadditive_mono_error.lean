-- Prove2me | solution 1 for NearlySubadditive.mono_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:12.424199+00:00
-- url     : https://prove2.me/submissions/e6cf8f2d-b7ab-428f-948d-1aa45e967aca

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
theorem _root_.solution (h : NearlySubadditive f μ N u) (hfg : f ≤ g) : NearlySubadditive g μ N u :=
  h.mono hfg le_rfl le_rfl
end NearlySubadditive
