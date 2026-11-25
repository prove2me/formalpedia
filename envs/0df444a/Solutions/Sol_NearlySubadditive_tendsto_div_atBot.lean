-- Prove2me | solution 1 for NearlySubadditive.tendsto_div_atBot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:55.145936+00:00
-- url     : https://prove2.me/submissions/bdde397c-33b0-4f3a-9594-4edce9b5e66f

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Definitions.Def_Fekete_Window
public import Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open NearlySubadditive
variable {μ : ℝ} {N : ℕ} {u : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hμ : 1 < μ) (h : NearlySubadditive 0 μ N u)
    (hbdd : ¬ BddBelow (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atBot :=
  (h.tendsto_atBot_or_exists_tendsto hμ).resolve_right fun ⟨_, hL⟩ ↦ hbdd hL.bddBelow_range
end NearlySubadditive
