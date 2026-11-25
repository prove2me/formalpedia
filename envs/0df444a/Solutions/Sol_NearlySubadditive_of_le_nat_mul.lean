-- Prove2me | solution 1 for NearlySubadditive.of_le_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:45.30388+00:00
-- url     : https://prove2.me/submissions/dcb285a7-a94d-4a30-8c6b-0ce1a693dd52

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
theorem _root_.solution {k : ℕ}
    (h : ∀ m n, N ≤ m → m ≤ n → n ≤ k * m → u (m + n) ≤ u m + u n + f (m + n)) :
    NearlySubadditive f k N u := fun m n hm hmn hn ↦ h m n hm hmn (by exact_mod_cast hn)
end NearlySubadditive
