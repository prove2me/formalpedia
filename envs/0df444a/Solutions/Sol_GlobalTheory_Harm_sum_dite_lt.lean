-- Prove2me | solution 1 for GlobalTheory.Harm.sum_dite_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:33.976804+00:00
-- url     : https://prove2.me/submissions/79e2974e-e1b3-4710-9f59-835458f4dadc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset
namespace GlobalTheory.Harm
namespace _root_.GlobalTheory.Harm
theorem _root_.solution {m p : ℕ} (hp : p ≤ m) (f : Fin p → ℤ) :
    ∑ k : Fin m, (if h : (k : ℕ) < p then f ⟨k, h⟩ else 0) = ∑ k, f k := by
  have hfin := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) m
  have hfin' := Fin.sum_univ_eq_sum_range (fun j => if h : j < p then f ⟨j, h⟩ else 0) p
  beta_reduce at hfin
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at hfin'
  rw [hfin, hfin']
  symm
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [Finset.mem_range] at hj
    simp [hj]
end _root_.GlobalTheory.Harm
end GlobalTheory.Harm
