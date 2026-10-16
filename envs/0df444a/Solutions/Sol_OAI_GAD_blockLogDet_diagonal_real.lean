-- Prove2me | solution 1 for OAI.GAD.blockLogDet_diagonal_real
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:40:29.277673+00:00
-- url     : https://prove2.me/submissions/19ce16ec-3090-4dfd-b394-4c8cf019485a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/GramMatrices.lean:L133-L163
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.blockLogDet_diagonal_real. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices

-- ---- from OAI.InformationTheory.AmplitudeDamping.GramMatrices ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} {μ : Type u_3} {ν : Type u_4} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

end GAD
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

theorem log_norm_det_diagonal_real (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    Real.log ‖(Matrix.diagonal (fun i ↦ (d i : ℂ))).det‖ = ∑ i, Real.log (d i) := by
  rw [Matrix.det_diagonal, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hd _)]
  exact Real.log_prod (fun i _ ↦ (hd i).ne')

theorem blockLogDet_diagonal_real (z d e : ι → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i) :
    blockLogDet (Matrix.diagonal (fun i ↦ (z i : ℂ)))
      (Matrix.diagonal (fun i ↦ (d i : ℂ))) (Matrix.diagonal (fun i ↦ (e i : ℂ))) =
      ∑ i, Real.log (1+(z i)^2/(d i*e i)) := by
  have hinv : (Matrix.diagonal (fun i ↦ (e i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i ↦ ((e i)⁻¹ : ℂ)) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have heq : (fun i ↦ (e i : ℂ) * ((e i)⁻¹ : ℂ)) = fun _ ↦ (1 : ℂ) := by
      ext i
      simp [Complex.ofReal_ne_zero.mpr (he i).ne']
    rw [heq, Matrix.diagonal_one]
  have hmat : Matrix.diagonal (fun i ↦ (d i : ℂ)) +
      Matrix.diagonal (fun i ↦ (z i : ℂ)) *
      (Matrix.diagonal (fun i ↦ (e i : ℂ)))⁻¹ *
      (Matrix.diagonal (fun i ↦ (z i : ℂ)))ᴴ =
      Matrix.diagonal (fun i ↦ ((d i+(z i)^2/e i : ℝ) : ℂ)) := by
    rw [hinv, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1
    ext i
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_comm]
  have hp (i : ι) : 0 < d i+(z i)^2/e i := add_pos_of_pos_of_nonneg (hd i)
    (div_nonneg (sq_nonneg _) (he i).le)
  unfold blockLogDet
  rw [hmat, log_norm_det_diagonal_real _ hp, log_norm_det_diagonal_real _ hd, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.log_div (hp i).ne' (hd i).ne']
  congr 1
  field_simp [(hd i).ne', (he i).ne']

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.blockLogDet_diagonal_real := @_root_.OAI.GAD.blockLogDet_diagonal_real
