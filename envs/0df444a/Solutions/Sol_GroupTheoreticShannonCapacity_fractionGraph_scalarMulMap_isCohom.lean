-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.fractionGraph_scalarMulMap_isCohom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:46.223868+00:00
-- url     : https://prove2.me/submissions/fd12eab8-60e5-4198-a0f0-d7e2d7435e39

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_fractionGraph_scalarMulMap_injective

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p' q' p q : ℕ) [NeZero p'] [NeZero (p' * p)]
    (hpq_ineq : p' * q ≤ p * q') :
    ∀ u v, u ≠ v → ¬(fractionGraph p' q').Adj u v →
      fractionGraph_scalarMulMap p' p u ≠ fractionGraph_scalarMulMap p' p v ∧
      ¬(fractionGraph (p' * p) (p' * q)).Adj
        (fractionGraph_scalarMulMap p' p u) (fractionGraph_scalarMulMap p' p v) := by
  have hp'_pos : 0 < p' := NeZero.pos p'
  have hp_pos := p_pos_of_neZero_prod p' p
  let f := fractionGraph_scalarMulMap p' p
  have hf_val : ∀ x : ZMod p', (f x).val = p * x.val := by
    intro x
    have hlt : p * x.val < p' * p := by
      calc p * x.val < p * p' := Nat.mul_lt_mul_of_pos_left x.val_lt hp_pos
        _ = p' * p := Nat.mul_comm p p'
    simp only [f, fractionGraph_scalarMulMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact ZMod.val_cast_of_lt hlt
  -- Key: distMod (p' * p) (f u) (f v) = p * distMod p' u v
  have hf_sub_val : ∀ u v : ZMod p', (f u - f v).val = p * (u - v).val := by
    intro u v
    have huv_lt : (u - v).val < p' := (u - v).val_lt
    have hp_uv_lt : p * (u - v).val < p' * p := by
      calc p * (u - v).val < p * p' := Nat.mul_lt_mul_of_pos_left huv_lt hp_pos
        _ = p' * p := Nat.mul_comm p p'
    have hf_sub : f (u - v) = f u - f v := f.map_sub u v
    rw [← hf_sub, hf_val]
  have hdistMod_scale : ∀ u v : ZMod p', distMod (p' * p) (f u) (f v) = p * distMod p' u v := by
    intro u v
    simp only [distMod, hf_sub_val]
    have huv_lt : (u - v).val < p' := (u - v).val_lt
    by_cases huv_zero : (u - v).val = 0
    · simp [huv_zero]
    · have h_factor : p' * p - p * (u - v).val = p * (p' - (u - v).val) := by
        calc p' * p - p * (u - v).val
            = p' * p - (u - v).val * p := by rw [Nat.mul_comm p (u - v).val]
          _ = (p' - (u - v).val) * p := (Nat.sub_mul p' (u - v).val p).symm
          _ = p * (p' - (u - v).val) := Nat.mul_comm _ _
      rw [h_factor, ← Nat.mul_min_mul_left]
  intro u v huv hnadj
  constructor
  · exact fun h => huv (fractionGraph_scalarMulMap_injective p' p h)
  · simp only [fractionGraph, not_and, not_lt] at hnadj ⊢
    intro _
    calc distMod (p' * p) (f u) (f v) = p * distMod p' u v := hdistMod_scale u v
      _ ≥ p * q' := Nat.mul_le_mul_left p (hnadj huv)
      _ ≥ p' * q := hpq_ineq
end GroupTheoreticShannonCapacity
