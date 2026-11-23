-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.addSubgroupShannonCapacity_ge_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:10.701438+00:00
-- url     : https://prove2.me/submissions/5dc01240-d799-496f-8e2b-6d21f3bab247

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution {G : Type*} [AddGroup G] [Fintype G]
    (Γ : SimpleGraph G) (n : ℕ) (hn : n ≥ 1) :
    addSubgroupShannonCapacity Γ ≥
      (addSubgroupIndependenceNumber (strongPower Γ n) : ℝ) ^ (1 / (n : ℝ)) := by
  simp only [addSubgroupShannonCapacity]
  -- The supremum is bounded above
  have hbdd : BddAbove (Set.range fun m =>
      (addSubgroupIndependenceNumber (strongPower Γ (m + 1)) : ℝ) ^ (1 / (m + 1 : ℝ))) := by
    use (Fintype.card G : ℝ)
    intro x ⟨m, hm⟩
    rw [← hm]
    have hexp_pos : (0 : ℝ) ≤ 1 / (m + 1) := by positivity
    have hcard_pos : (0 : ℝ) ≤ Fintype.card G := by positivity
    -- addSubgroupIndependenceNumber ≤ |V| since any subgroup has size ≤ |G|
    have hindep_le : (addSubgroupIndependenceNumber (strongPower Γ (m + 1)) : ℝ) ≤
        (Fintype.card (Fin (m + 1) → G) : ℝ) := by
      simp only [addSubgroupIndependenceNumber]
      -- First show this as a statement about ℕ, then cast
      have hnat : sSup { n | ∃ H : AddSubgroup (Fin (m + 1) → G),
          (strongPower Γ (m + 1)).IsIndepSet (H : Set (Fin (m + 1) → G)) ∧ Nat.card ↥H = n } ≤
          Fintype.card (Fin (m + 1) → G) := by
        apply csSup_le
        · use 1, ⊥
          constructor
          · intro u hu v hv huv
            simp only [SetLike.mem_coe, AddSubgroup.mem_bot] at hu hv
            rw [hu, hv] at huv
            exact (huv rfl).elim
          · exact AddSubgroup.card_bot
        · intro x ⟨H, _, hcard⟩
          rw [← hcard]
          haveI : Fintype H := Fintype.ofFinite H
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      exact_mod_cast hnat
    have hcard_eq : Fintype.card (Fin (m + 1) → G) = (Fintype.card G) ^ (m + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    calc (addSubgroupIndependenceNumber (strongPower Γ (m + 1)) : ℝ) ^ (1 / (m + 1 : ℝ))
        ≤ (Fintype.card (Fin (m + 1) → G) : ℝ) ^ (1 / (m + 1 : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity) hindep_le hexp_pos
      _ = ((Fintype.card G : ℝ) ^ (m + 1 : ℕ)) ^ (1 / (m + 1 : ℝ)) := by
          rw [hcard_eq]; norm_cast
      _ = (Fintype.card G : ℝ) ^ ((m + 1 : ℕ) * (1 / (m + 1 : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hcard_pos]
      _ = (Fintype.card G : ℝ) ^ (1 : ℝ) := by
          congr 1; push_cast; field_simp
      _ = Fintype.card G := Real.rpow_one _
  apply le_ciSup_of_le hbdd (n - 1)
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
  -- Need to show: ... ^ (1 / n) ≤ ... ^ (1 / ((n-1) + 1))
  -- Rewrite n - 1 + 1 to n and show reflexivity
  conv_rhs => rw [hn1]; rw [Nat.cast_sub hn, Nat.cast_one]; ring_nf
  ring_nf
  exact le_refl _
end GroupTheoreticShannonCapacity
