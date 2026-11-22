-- Prove2me | solution 1 for Lean4LPD.PauliString.row_sum_norm_layerJumpMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:46:36.947949+00:00
-- url     : https://prove2.me/submissions/3778c92f-ca57-4130-a28c-d439a97e34b1

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiLayer
public import Theorems.Thm_Lean4LPD_PauliString_layerAntiCount_partner
public import Theorems.Thm_Lean4LPD_PauliString_norm_stayAct_apply_le
public import Theorems.Thm_Lean4LPD_PauliString_norm_jumpAct_apply_le
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_or_one
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_wt_cls
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_rungWeight_one
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.cls_fst
attribute [local simp] Lean4LPD.PauliString.cls_herm
attribute [local simp] Lean4LPD.PauliString.cls_snd
attribute [local simp] Lean4LPD.PauliString.coeffVec_apply
attribute [local simp] Lean4LPD.PauliString.cover_nil
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_highSet
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.pauliNorm_sq
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.reachable_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.restr_apply
attribute [local simp] Lean4LPD.PauliString.restr_univ
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.wt_cls
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.norm_iPow
attribute [local simp] Lean4LPD.rungWeight_one
attribute [local simp] Lean4LPD.star_negOnePow


attribute [local simp] Lean4LPD.PauliString.stayAct_apply
attribute [local simp] Lean4LPD.PauliString.jumpAct_apply
attribute [local simp] Lean4LPD.PauliString.stayAct_zero
attribute [local simp] Lean4LPD.PauliString.jumpAct_zero
attribute [local simp] Lean4LPD.PauliString.mem_antiLayer

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}
namespace Lean4LPD.PauliString
theorem _root_.solution (L : List (PauliString n × ℝ))
    (hcomm : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ)
    (j : ℕ) (p : PauliIndex n) :
    ∑ q, ‖layerJumpMatrix L j p q‖
      ≤ ((layerAntiCount (L.map Prod.fst) p).choose j : ℝ) * σ ^ j := by
  classical
  induction L generalizing j p with
  | nil =>
    cases j with
    | zero => simp [layerJumpMatrix, layerJump, layerAntiCount, apply_ite]
    | succ j => simp [layerJumpMatrix, layerJump, layerAntiCount]
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    have hcL : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0 :=
      fun g hg h hh => hcomm g (by simp [hg]) h (by simp [hh])
    have hsL : ∀ g ∈ L, |Real.sin g.2| ≤ σ := fun g hg => hsin g (by simp [hg])
    have hs : |Real.sin θ| ≤ σ := hsin (G, θ) (by simp)
    cases j with
    | zero =>
      calc ∑ q, ‖layerJumpMatrix ((G, θ) :: L) 0 p q‖
          ≤ ∑ q, ‖layerJumpMatrix L 0 p q‖ :=
            Finset.sum_le_sum fun q _ => norm_stayAct_apply_le G θ _ p
        _ ≤ _ := by simpa using ih hcL hsL 0 p
    | succ j =>
      by_cases hp : sympForm G (herm p) = 0
      · have hcount : layerAntiCount (((G, θ) :: L).map Prod.fst) p
            = layerAntiCount (L.map Prod.fst) p := by simp [layerAntiCount, hp]
        rw [hcount]
        simpa [layerJumpMatrix, layerJump, stayAct_apply, jumpAct_apply, hp]
          using ih hcL hsL (j + 1) p
      · have hp1 : sympForm G (herm p) = 1 :=
          (sympForm_eq_zero_or_one G (herm p)).resolve_left hp
        have hcount : layerAntiCount (((G, θ) :: L).map Prod.fst) p
            = layerAntiCount (L.map Prod.fst) p + 1 := by simp [layerAntiCount, hp1]
        have hpart : layerAntiCount (L.map Prod.fst) (partner G p)
            = layerAntiCount (L.map Prod.fst) p := by
          apply layerAntiCount_partner
          intro H hH
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hH
          exact hcomm g (by simp [hg]) (G, θ) (by simp)
        have hprev := ih hcL hsL j (partner G p)
        rw [hpart] at hprev
        rw [hcount]
        calc ∑ q, ‖layerJumpMatrix ((G, θ) :: L) (j + 1) p q‖
            ≤ ∑ q, (‖layerJumpMatrix L (j + 1) p q‖
                + |Real.sin θ| * ‖layerJumpMatrix L j (partner G p) q‖) := by
              apply Finset.sum_le_sum
              intro q _
              exact (norm_add_le _ _).trans
                (add_le_add (norm_stayAct_apply_le G θ _ p)
                  (norm_jumpAct_apply_le G θ _ p))
          _ = (∑ q, ‖layerJumpMatrix L (j + 1) p q‖)
                + |Real.sin θ| * ∑ q, ‖layerJumpMatrix L j (partner G p) q‖ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ ((layerAntiCount (L.map Prod.fst) p).choose (j + 1) : ℝ) * σ ^ (j + 1)
                + σ * (((layerAntiCount (L.map Prod.fst) p).choose j : ℝ) * σ ^ j) :=
              add_le_add (ih hcL hsL (j + 1) p)
                (mul_le_mul hs hprev (Finset.sum_nonneg fun _ _ => norm_nonneg _) hσ)
          _ = _ := by rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]; ring
end Lean4LPD.PauliString
