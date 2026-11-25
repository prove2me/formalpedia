-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.Plus.nrm_add_val_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:21:31.615016+00:00
-- url     : https://prove2.me/submissions/a81091a4-781a-4911-a6fb-beb2ed871548

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsRing
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsField
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_Plus_pow_max_max_le_max_pow
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_D_pos
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_add_le_max
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___nonneg_2e425604b7b3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_one
attribute [local simp] GroundTheory.PAdicHodge.NormTower.N_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_eq_zero
attribute [local simp] GroundTheory.PAdicHodge.nrm_neg
attribute [local simp] GroundTheory.PAdicHodge.nrm_one
attribute [local simp] GroundTheory.PAdicHodge.nrm_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.LocalField ValuativeRel Filter Topology
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] {p : ℕ}
open GroundTheory.PAdicHodge.NormTower
variable (t : NormTower K Ω p)
open GroundTheory.PAdicHodge.NormTower.Plus
variable {t}
namespace GroundTheory.PAdicHodge.NormTower.Plus
theorem _root_.solution (x y : t.Plus) :
    nrm K ((x + y).1 0) ≤ max (nrm K (x.1 0)) (nrm K (y.1 0)) := by
  have hle : ∀ j, nrm K ((x + y).1 0) ≤ max (max (nrm K (x.1 0)) (nrm K (y.1 0))) (t.ρ ^ t.D 0 j) := by
    intro j
    rw [nrm_val_zero (x + y) j, nrm_val_zero x j, nrm_val_zero y j]
    have h1 : nrm K ((x + y).1 j) ≤ max (max (nrm K (x.1 j)) (nrm K (y.1 j))) t.ρ := by
      have : (x + y).1 j = ((x + y).1 j - (x.1 j + y.1 j)) + (x.1 j + y.1 j) := by ring
      rw [this]
      refine (nrm_add_le_max _ _).trans (max_le (le_max_of_le_right (add_cong x y j)) ?_)
      exact le_max_of_le_left (nrm_add_le_max _ _)
    have hD := t.D_pos 0 j
    calc nrm K ((x + y).1 j) ^ t.D 0 j ≤ (max (max (nrm K (x.1 j)) (nrm K (y.1 j))) t.ρ) ^ t.D 0 j :=
          pow_le_pow_left₀ (nrm_nonneg _) h1 _
      _ ≤ max (max (nrm K (x.1 j) ^ t.D 0 j) (nrm K (y.1 j) ^ t.D 0 j)) (t.ρ ^ t.D 0 j) :=
          pow_max_max_le_max_pow _

  have hDj : ∀ M : ℕ, ∃ j, M ≤ t.D 0 j := by
    intro M
    obtain ⟨j, hj⟩ := t.exists_le_cnt 0 M
    refine ⟨j, hj.trans ?_⟩

    clear hj
    induction j with
    | zero => simp [cnt, D]
    | succ j ih =>
      rw [cnt_succ, D_succ]
      split_ifs with hk
      · have h2 : 2 ≤ p ^ t.k (0 + j) :=
          (t.prime.two_le).trans (Nat.le_self_pow hk _)
        have := t.D_pos 0 j
        nlinarith
      · have := Nat.one_le_pow (t.k (0 + j)) p t.prime.pos
        nlinarith
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε t.ρ_lt_one
  obtain ⟨j, hj⟩ := hDj M
  have h := hle j
  have hρj : t.ρ ^ t.D 0 j ≤ t.ρ ^ M := pow_le_pow_of_le_one t.ρ_nonneg t.ρ_lt_one.le hj
  rcases le_total (max (nrm K (x.1 0)) (nrm K (y.1 0))) (t.ρ ^ t.D 0 j) with h' | h'
  · rw [max_eq_right h'] at h
    linarith [le_max_left (nrm K (x.1 0)) (nrm K (y.1 0)), nrm_nonneg (K := K) (x.1 0)]
  · rw [max_eq_left h'] at h
    linarith
end GroundTheory.PAdicHodge.NormTower.Plus
