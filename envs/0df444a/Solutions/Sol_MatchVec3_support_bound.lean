-- Prove2me | solution 1 for MatchVec3.support_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:14:57.657198+00:00
-- url     : https://prove2.me/submissions/0f66bbc9-29cb-43e2-8727-a1ef1dd1748d

import Mathlib
import Definitions.Def_MatchVec3_minEntropy

namespace MatchVec3.Aux_MV

open MatchVec3

theorem part1 {α : Type*} (X : PMF α) (hS : X.support.Finite) :
    minEntropy X ≤ Real.log X.support.ncard := by
  classical
  set F := hS.toFinset with hF
  set p := ⨆ x, X x with hp
  have hle : ∀ x, X x ≤ p := fun x => le_iSup (fun x => X x) x
  have hp1 : p ≤ 1 := iSup_le fun x => PMF.coe_le_one X x
  have hptop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hsum : ∑ x ∈ F, X x = 1 := by
    rw [← X.tsum_coe]
    symm
    apply tsum_eq_sum
    intro x hx
    rw [hF, Set.Finite.mem_toFinset] at hx
    exact (PMF.apply_eq_zero_iff X x).mpr hx
  have hk : (X.support.ncard : ENNReal) = F.card := by
    rw [Set.ncard_eq_toFinset_card X.support hS]
  have h1 : (1 : ENNReal) ≤ (X.support.ncard : ENNReal) * p := by
    rw [← hsum, hk]
    calc ∑ x ∈ F, X x ≤ ∑ _x ∈ F, p := Finset.sum_le_sum fun x _ => hle x
      _ = F.card * p := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : (1 : ℝ) ≤ (X.support.ncard : ℝ) * p.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hptop) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at this
  have hk0 : (0 : ℝ) < X.support.ncard := by
    have : 0 < X.support.ncard := (Set.ncard_pos hS).mpr X.support_nonempty
    exact_mod_cast this
  have hq0 : 0 < p.toReal := by
    by_contra h
    push_neg at h
    have : p.toReal = 0 := le_antisymm h ENNReal.toReal_nonneg
    rw [this, mul_zero] at h2
    linarith
  unfold minEntropy
  rw [← hp]
  have hlog : 0 ≤ Real.log ((X.support.ncard : ℝ) * p.toReal) := Real.log_nonneg h2
  rw [Real.log_mul hk0.ne' hq0.ne'] at hlog
  linarith

end MatchVec3.Aux_MV

open MatchVec3 MatchVec3.Aux_MV in
theorem solution.{u} :
    (∀ {α : Type u} (X : PMF α), X.support.Finite → minEntropy X ≤ Real.log X.support.ncard) ∧
    (∀ {m n : ℕ}, m ≠ 0 → ∀ X : PMF (Fin n → ZMod m), minEntropy X ≤ n * Real.log m) := by
  refine ⟨fun X hS => part1 X hS, ?_⟩
  intro m n hm X
  haveI : NeZero m := ⟨hm⟩
  have hS : X.support.Finite := Set.toFinite _
  have h1 := part1 X hS
  have hk : 0 < X.support.ncard := (Set.ncard_pos hS).mpr X.support_nonempty
  have hle : X.support.ncard ≤ m ^ n := by
    have := Set.ncard_le_card X.support
    simpa [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] using this
  have h2 : Real.log X.support.ncard ≤ Real.log ((m : ℝ) ^ n) := by
    apply Real.log_le_log (by exact_mod_cast hk)
    exact_mod_cast hle
  rw [Real.log_pow] at h2
  linarith
