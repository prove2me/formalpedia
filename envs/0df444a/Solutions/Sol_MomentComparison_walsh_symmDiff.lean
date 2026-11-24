-- Prove2me | solution 1 for MomentComparison.walsh_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:21:06.349118+00:00
-- url     : https://prove2.me/submissions/53091d55-5574-415e-a130-d1166f6bdbf4

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_empty
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (s t : Finset (Fin n)) (x : Cube n) :
    walsh (s ∆ t) x = walsh s x * walsh t x := by
  change (∏ i ∈ (s \ t) ∪ (t \ s), cubeSign x i) = _
  rw [prod_union (disjoint_sdiff_sdiff : Disjoint (s \ t) (t \ s))]
  unfold walsh
  have hs := prod_inter_mul_prod_sdiff s t (cubeSign x)
  have ht := prod_inter_mul_prod_sdiff t s (cubeSign x)
  rw [inter_comm t s] at ht
  rw [← hs, ← ht]
  have h : (∏ i ∈ s ∩ t, cubeSign x i) * (∏ i ∈ s ∩ t, cubeSign x i) = 1 := by
    rw [← prod_mul_distrib]
    simp only [cubeSign_mul_self, prod_const_one]
  calc
    _ = (∏ i ∈ s \ t, cubeSign x i) * (∏ i ∈ t \ s, cubeSign x i) * 1 := by rw [mul_one]
    _ = _ := by rw [← h]; ring
end MomentComparison
