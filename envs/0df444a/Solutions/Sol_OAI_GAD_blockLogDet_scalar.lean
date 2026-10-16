-- Prove2me | solution 1 for OAI.GAD.blockLogDet_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:33.823191+00:00
-- url     : https://prove2.me/submissions/488971f8-2d45-4bcc-b628-19818868c9b9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean:L108-L134
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.blockLogDet_scalar. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit

-- ---- from OAI.InformationTheory.AmplitudeDamping.ScalarDeficit ----
namespace OAI

universe u_1 u_2

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

open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

/-- Scalar specialization of the noncommutative logdet function. -/
theorem blockLogDet_scalar {q d e : ℝ} (hq : 0 ≤ q) (hd : 0 < d) (he : 0 < e) :
    blockLogDet (Matrix.diagonal (fun _ : Fin 1 ↦ (Real.sqrt q : ℂ)))
      (Matrix.diagonal (fun _ ↦ (d : ℂ))) (Matrix.diagonal (fun _ ↦ (e : ℂ))) =
      Real.log (1 + q/(d*e)) := by
  have hs : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hq
  have ht : 0 < d + q/e := add_pos_of_pos_of_nonneg hd (div_nonneg hq he.le)
  have heq : d + q/e = d*(1+q/(d*e)) := by field_simp
  have hinv : Ring.inverse (fun _ : Fin 1 ↦ (e : ℂ)) = fun _ ↦ (e : ℂ)⁻¹ := by
    let u : (Fin 1 → ℂ)ˣ := ⟨fun _ ↦ (e : ℂ), fun _ ↦ (e : ℂ)⁻¹,
      by ext; simp [he.ne'], by ext; simp [he.ne']⟩
    exact Ring.inverse_unit u
  simp only [blockLogDet, Matrix.inv_diagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.det_fin_one, Matrix.add_apply,
    Matrix.diagonal_apply_eq, hinv, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  have hc : (d : ℂ) + (Real.sqrt q : ℂ) * (e : ℂ)⁻¹ * (Real.sqrt q : ℂ) =
      ((d+q/e : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
    calc
      _ = (d : ℂ) + ((Real.sqrt q : ℂ)*(Real.sqrt q : ℂ)) * (e : ℂ)⁻¹ := by ring
      _ = _ := by rw [hs]
  rw [hc]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hd]
  rw [heq, Real.log_mul hd.ne' (ne_of_gt (by positivity : 0 < 1+q/(d*e)))]
  ring

end GAD
open scoped BigOperators ComplexOrder
open Matrix Set
namespace GAD

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
open scoped BigOperators ComplexOrder
open Matrix Set


theorem solution : type_of% @_root_.OAI.GAD.blockLogDet_scalar := @_root_.OAI.GAD.blockLogDet_scalar
