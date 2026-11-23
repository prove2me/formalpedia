-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.prod_ite_sigma_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:40:46.853875+00:00
-- url     : https://prove2.me/submissions/7f9102d3-3d1a-494b-a9a0-99a2b1a97597

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (∏ i ∈ Sᶜ, if σ i = i then (1 : ℝ) else 0) = if ∀ i ∈ Sᶜ, σ i = i then 1 else 0 := by
  by_cases h : ∀ i ∈ Sᶜ, σ i = i
  · simp only [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h i hi]
  · simp only [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    apply Finset.prod_eq_zero hi
    simp [hne]
end GroupTheoreticShannonCapacity.P0Matrix
