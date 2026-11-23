-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.prod_of_fixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:18.332805+00:00
-- url     : https://prove2.me/submissions/63569808-fdba-4c15-b0bb-d461444650c8

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_orderEmbOfFin_fixingPermEquiv

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (hfix : ∀ i ∈ Sᶜ, σ i = i) :
    ∏ i ∈ S, M (σ i) i =
    ∏ j : Fin S.card, (principalSubmatrix n M S)
      (fixingPermEquiv n S ⟨σ, hfix⟩ j) j := by
  -- Unfold the submatrix definition and use the key relation
  unfold principalSubmatrix
  simp only [Matrix.submatrix_apply]
  -- Now goal is: ∏ i ∈ S, M (σ i) i = ∏ j, M (emb (τ j)) (emb j)
  -- Using orderEmbOfFin_fixingPermEquiv: emb (τ j) = σ (emb j)
  conv_rhs =>
    arg 2
    ext j
    rw [orderEmbOfFin_fixingPermEquiv n σ S hfix j]
  -- Now goal is: ∏ i ∈ S, M (σ i) i = ∏ j, M (σ (emb j)) (emb j)
  -- This is a reindexing along the bijection emb : Fin S.card → S
  symm
  rw [← S.prod_coe_sort (fun i => M (σ i) i)]
  -- Goal: ∏ j, M (σ (emb j)) (emb j) = ∏ i : S, M (σ i) i
  apply Fintype.prod_equiv (S.orderIsoOfFin rfl).toEquiv
  intro j
  -- Goal: M (σ (emb j)) (emb j) = M (σ (iso j).val) (iso j).val
  -- But emb j = (iso j).val by definition
  rfl
end GroupTheoreticShannonCapacity.P0Matrix
