-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:39:07.135919+00:00
-- url     : https://prove2.me/submissions/06ee776f-eca7-4f37-ab51-de4488555ddd

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_scalarMulMap_injective
import Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_scalarMulMap_isCohom
import Theorems.Thm_GroupTheoreticShannonCapacity_addSubgroupShannonCapacity_mono_of_addHom_cohom


set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {p' q' p q : ℕ} [NeZero p'] (hq' : 0 < q')
    (hp : p ≠ 0) (hq : 0 < q) (hle : (p' : ℚ) / q' ≤ (p : ℚ) / q) :
    ∃ (a b : ℕ) (_ : NeZero a) (_ : 0 < b), (a : ℚ) / b = (p : ℚ) / q ∧
      addSubgroupShannonCapacity (fractionGraph a b) ≥
        addSubgroupShannonCapacity (fractionGraph p' q') := by
  have hp' : p' ≠ 0 := NeZero.ne p'
  have hp'_pos : 0 < p' := Nat.pos_of_ne_zero hp'
  have hp_pos : 0 < p := Nat.pos_of_ne_zero hp
  haveI : NeZero (p' * p) := ⟨Nat.mul_ne_zero hp' hp⟩
  refine ⟨p' * p, p' * q, ⟨Nat.mul_ne_zero hp' hp⟩, Nat.mul_pos hp'_pos hq, ?_, ?_⟩
  · -- (p' * p) / (p' * q) = p / q as rationals
    have hq_ne : (q : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
    have hp'q_ne : (p' * q : ℚ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hp' (Nat.ne_of_gt hq)
    field_simp
    -- Goal: ↑(p' * p) * ↑q = ↑(p' * q) * ↑p
    push_cast
    ring
  · -- Use the transfer lemma with the scalar multiplication map
    have hpq_ineq : p' * q ≤ p * q' := by
      rw [div_le_div_iff₀ (by positivity : (0:ℚ) < q') (by positivity : (0:ℚ) < q)] at hle
      exact_mod_cast hle
    exact addSubgroupShannonCapacity_mono_of_addHom_cohom
      (fractionGraph p' q') (fractionGraph (p' * p) (p' * q))
      (fractionGraph_scalarMulMap p' p)
      (fractionGraph_scalarMulMap_injective p' p)
      (fractionGraph_scalarMulMap_isCohom p' q' p q hpq_ineq)
end GroupTheoreticShannonCapacity
