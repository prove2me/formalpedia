-- Prove2me | solution 1 for NearlySubadditive.tendsto_witness_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:36.643951+00:00
-- url     : https://prove2.me/submissions/db0a4a0f-d2e8-4db2-bd71-6e69c6d62574

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hf0 : 0 ≤ f)
    (hfs : ¬ Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) :
    Tendsto (fun n ↦ witness f n / n) atTop atTop := by
  have hA : Tendsto (fun n ↦ ∑ i ∈ range n, f i / (i : ℝ) ^ 2) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦ div_nonneg (hf0 n) (sq_nonneg _)).1 hfs
  refine ((tendsto_add_atTop_iff_nat 1).2 hA).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [witness, this]
end NearlySubadditive
