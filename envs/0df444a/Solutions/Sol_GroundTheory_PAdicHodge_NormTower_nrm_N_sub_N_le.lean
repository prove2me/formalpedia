-- Prove2me | solution 1 for GroundTheory.PAdicHodge.NormTower.nrm_N_sub_N_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:39.368965+00:00
-- url     : https://prove2.me/submissions/486dcade-e586-494f-af92-5e12be59fd9d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_PAdicHodge_FieldOfNormsTower
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_one
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_neg
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_nrm_algEquiv
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_NormTower___lt_one_de857b87b125
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_one
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_N_zero
import Theorems.Thm_GroundTheory_PAdicHodge_NormTower_nrm_N_sub_N_le_mul
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
theorem _root_.solution (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ) (hab : nrm K (a - b) ≤ s) :
    nrm K (t.N n a - t.N n b) ≤ s := by
  by_cases hk : t.k n = 0
  · obtain ⟨σ, hT⟩ : ∃ σ, t.T n = {σ} := Finset.card_eq_one.mp (by rw [t.card_alt, hk, pow_zero])
    simp only [N, hT, Finset.prod_singleton]
    rw [← map_sub, nrm_algEquiv]; exact hab
  · refine (t.nrm_N_sub_N_le_mul n hk ha hb ha1 hb1 hs hab).trans ?_
    have hs0 : 0 ≤ s := (nrm_nonneg _).trans hab
    calc t.ρ * s ≤ 1 * s := mul_le_mul_of_nonneg_right t.ρ_lt_one.le hs0
      _ = s := one_mul s
end GroundTheory.PAdicHodge.NormTower
