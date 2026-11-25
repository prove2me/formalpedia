-- Prove2me | solution 1 for NearlySubadditive.nearlySubadditive_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:11.869609+00:00
-- url     : https://prove2.me/submissions/5f589b5b-90bb-4243-b173-ca86191a02ea

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
public import Theorems.Thm_NearlySubadditive_witness_le_add
public import Theorems.Thm_NearlySubadditive_of_le_add


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
variable {f : ℕ → ℝ}
namespace NearlySubadditive
theorem _root_.solution (hf0 : 0 ≤ f) (hf : Monotone f) (μ : ℝ) (N : ℕ) :
    NearlySubadditive f μ N (witness f) :=
  .of_le_add fun m n _ _ ↦ witness_le_add hf0 hf m n
end NearlySubadditive
