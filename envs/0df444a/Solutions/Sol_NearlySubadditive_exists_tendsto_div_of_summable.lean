-- Prove2me | solution 1 for NearlySubadditive.exists_tendsto_div_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:16.464809+00:00
-- url     : https://prove2.me/submissions/d8a1951f-e0fd-4cdc-a56f-73fc11be7f17

module
public import Definitions.Def_Fekete_Window
public import Mathlib.Analysis.PSeries
public import Definitions.Def_Fekete_DeBruijnErdos
public import Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto_of_summable

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f u : ℕ → ℝ} {μ : ℝ} {N : ℕ}
namespace NearlySubadditive
theorem _root_.solution (hμ : 1 < μ) (h : NearlySubadditive f μ N u)
    (hf : Monotone f) (hfs : Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2)
    (hbdd : BddBelow (Set.range fun n ↦ u n / n)) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) :=
  (h.tendsto_atBot_or_exists_tendsto_of_summable hμ hf hfs).resolve_left
    fun hbot ↦ not_bddBelow_of_tendsto_atBot hbot hbdd
end NearlySubadditive
