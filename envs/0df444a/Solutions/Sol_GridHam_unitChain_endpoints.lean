-- Prove2me | solution 1 for GridHam.unitChain_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:22:45.118207+00:00
-- url     : https://prove2.me/submissions/123a73f2-e11d-470e-85fd-5f1c48b66585

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
public import Theorems.Thm_GridHam_unitChain_head_extreme
public import Theorems.Thm_GridHam_unitChain_last_of_head_min
public import Theorems.Thm_GridHam_unitChain_last_of_head_max

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (a : ℕ) (rest : List ℕ) (k : ℕ)
    (hnd : (a :: rest).Nodup) (hch : unitStepChain (a :: rest) = true)
    (hcov : ∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) :
    (a = k ∧ (a :: rest).getLast? = some (k + rest.length)) ∨
    (a = k + rest.length ∧ (a :: rest).getLast? = some k) := by
  rcases unitChain_head_extreme a rest k hnd hch hcov with h | h
  · exact Or.inl ⟨h, unitChain_last_of_head_min rest a k hnd hch hcov h⟩
  · exact Or.inr ⟨h, unitChain_last_of_head_max rest a k hnd hch hcov h⟩
end GridHam
