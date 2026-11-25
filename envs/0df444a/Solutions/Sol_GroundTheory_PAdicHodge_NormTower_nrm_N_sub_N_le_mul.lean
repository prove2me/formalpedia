-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.nrm_N_sub_N_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:16.764722+00:00
-- url     : https://prove2.me/submissions/30c8767f-4884-44f8-aefe-6f108e813dfa

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_mul
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sub_comm
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_div
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_sub_le_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_algEquiv
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_prod_sub_prod_le
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one_add_pow_sub_one_le
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___nonneg_2e425604b7b3
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_mul
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue


attribute [local simp] GroundTheory.PAdicHodge.nrm_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)
open GroundTheory.PAdicHodge.NormTower
variable {K Ω p} (t : NormTower K Ω p)
namespace GroundTheory.PAdicHodge.NormTower
theorem _root_.solution (n : ℕ) (hk : t.k n ≠ 0) {a b : Ω} (ha : a ∈ t.E (n + 1))
    (hb : b ∈ t.E (n + 1)) (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ)
    (hab : nrm K (a - b) ≤ s) : nrm K (t.N n a - t.N n b) ≤ t.ρ * s := by
  have hp1 := t.prime.one_lt
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans hab
  have hρ1 := t.ρ_lt_one
  have hρ0 := t.ρ_nonneg
  set d := p ^ t.k n with hd
  have hdp : p ≤ d := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ t.k n := Nat.pow_le_pow_right t.prime.pos (Nat.one_le_iff_ne_zero.mpr hk)

  have hsp : s ^ (p - 1) ≤ t.ρ := by
    calc s ^ (p - 1) ≤ t.ρ ^ (p - 1) := pow_le_pow_left₀ hs0 hs _
      _ ≤ t.ρ ^ 1 := pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
      _ = t.ρ := pow_one _

  have main : ∀ {a b : Ω}, a ∈ t.E (n + 1) → b ∈ t.E (n + 1) → nrm K a ≤ 1 → nrm K b ≤ 1 →
      nrm K (a - b) ≤ s → nrm K b ≤ nrm K a → nrm K (t.N n a - t.N n b) ≤ t.ρ * s := by
    intro a b ha hb ha1 hb1 hab hba
    by_cases hsmall : nrm K a ≤ s
    · have hsmallpow : ∀ {x : Ω}, nrm K x ≤ s → nrm K (t.N n x) ≤ t.ρ * s := by
        intro x hx
        rw [nrm_N]
        have hx0 := nrm_nonneg (K := K) x
        calc nrm K x ^ d ≤ s ^ d := pow_le_pow_left₀ hx0 hx _
          _ = s ^ (p - 1) * s ^ (d - (p - 1)) := by rw [← pow_add]; congr 1; omega
          _ ≤ t.ρ * s ^ 1 := by
            refine mul_le_mul hsp (pow_le_pow_of_le_one hs0 (hs.trans hρ1.le) (by omega))
              (pow_nonneg hs0 _) hρ0
          _ = t.ρ * s := by rw [pow_one]
      exact nrm_sub_le_of_le (hsmallpow hsmall) (hsmallpow (hba.trans hsmall))
    · push Not at hsmall
      have ha0 : a ≠ 0 := nrm_pos.mp (hs0.trans_lt hsmall)
      have hna0 : 0 < nrm K a := hs0.trans_lt hsmall
      set w := (b - a) / a with hw
      have hwE : w ∈ t.E (n + 1) := div_mem (sub_mem hb ha) ha
      have hbw : b = a * (1 + w) := by rw [hw]; field_simp; ring
      have hnw : nrm K w * nrm K a = nrm K (b - a) := by
        rw [hw, nrm_div, div_mul_cancel₀ _ hna0.ne']
      have hw1 : nrm K w ≤ 1 := by
        rw [hw, nrm_div, div_le_one hna0, nrm_sub_comm]
        exact hab.trans hsmall.le
      have h1w : nrm K (1 + w) ≤ 1 := nrm_add_le_one (by simp) hw1

      have hN1 : nrm K (t.N n (1 + w) - 1) ≤
          nrm K w * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1))) := by
        have e : t.N n (1 + w) - 1 = (t.N n (1 + w) - (1 + w) ^ d) + ((1 + w) ^ d - 1) := by ring
        rw [e]
        refine nrm_add_le_of_le ?_ ?_
        · rw [hd, ← t.card_alt n, ← Finset.prod_const, N]
          refine nrm_prod_sub_prod_le _ _ _ (mul_nonneg (nrm_nonneg _) (le_max_of_le_left t.c_nonneg))
            (fun σ _ ↦ by rwa [nrm_algEquiv]) (fun _ _ ↦ h1w) fun σ hσ ↦ ?_
          have : σ (1 + w) - (1 + w) = σ w - w := by rw [map_add, map_one]; ring
          rw [this]
          refine (t.step n σ hσ w hwE).trans ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (nrm_nonneg _)
        · refine (nrm_one_add_pow_sub_one_le t.prime hw1 hk).trans ?_
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (nrm_nonneg _)
      have hNb : t.N n b - t.N n a = t.N n a * (t.N n (1 + w) - 1) := by
        rw [hbw, t.N_mul]; ring
      rw [← nrm_sub_comm, hNb, nrm_mul, nrm_N]

      have hd1 : nrm K a ^ d = nrm K a ^ (d - 1) * nrm K a := by
        rw [← pow_succ]; congr 1; have := t.prime.pos; omega
      have hM : nrm K a ^ (d - 1) * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1))) ≤ t.ρ := by
        have hpow : nrm K a ^ (d - 1) ≤ nrm K a ^ (p - 1) :=
          pow_le_pow_of_le_one (nrm_nonneg _) ha1 (by omega)
        have hpow1 : nrm K a ^ (d - 1) ≤ 1 := pow_le_one₀ (nrm_nonneg _) ha1
        have hpow0 : 0 ≤ nrm K a ^ (d - 1) := pow_nonneg (nrm_nonneg _) _
        rcases le_total (max t.c (nrm K (p : Ω))) (nrm K w ^ (p - 1)) with h | h
        · rw [← max_assoc, max_eq_right h]
          calc nrm K a ^ (d - 1) * nrm K w ^ (p - 1) ≤ nrm K a ^ (p - 1) * nrm K w ^ (p - 1) :=
                mul_le_mul_of_nonneg_right hpow (pow_nonneg (nrm_nonneg _) _)
            _ = (nrm K w * nrm K a) ^ (p - 1) := by rw [mul_pow, mul_comm]
            _ ≤ s ^ (p - 1) := by
                rw [hnw, nrm_sub_comm]
                exact pow_le_pow_left₀ (nrm_nonneg _) hab _
            _ ≤ t.ρ := hsp
        · rw [← max_assoc, max_eq_left h]
          calc nrm K a ^ (d - 1) * max t.c (nrm K (p : Ω)) ≤ 1 * t.ρ :=
                mul_le_mul hpow1 le_rfl (le_max_of_le_left t.c_nonneg) zero_le_one
            _ = t.ρ := one_mul _
      calc nrm K a ^ d * nrm K (t.N n (1 + w) - 1)
          ≤ nrm K a ^ d * (nrm K w * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1)))) :=
            mul_le_mul_of_nonneg_left hN1 (pow_nonneg (nrm_nonneg _) _)
        _ = (nrm K a ^ (d - 1) * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1)))) *
            (nrm K w * nrm K a) := by rw [hd1]; ring
        _ ≤ t.ρ * s := by
            rw [hnw, nrm_sub_comm]
            exact mul_le_mul hM hab (nrm_nonneg _) hρ0
  rcases le_total (nrm K b) (nrm K a) with h | h
  · exact main ha hb ha1 hb1 hab h
  · rw [nrm_sub_comm]
    exact main hb ha hb1 ha1 (by rwa [nrm_sub_comm]) h
end GroundTheory.PAdicHodge.NormTower
