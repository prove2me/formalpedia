-- Prove2me | solution 1 for OAI.GAD.logDetShift_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:37:29.669186+00:00
-- url     : https://prove2.me/submissions/2144de63-e643-47f9-bcc7-4da19e3a435e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean:L113-L137
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.logDetShift_eq_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetEntropy ----
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
namespace GAD

end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

theorem det_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).det = A.det := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  rw [Matrix.det_mul, Matrix.det_one] at hu
  calc
    _ = ((U : Matrix ι ι ℂ).det * (star U : Matrix ι ι ℂ).det) * A.det := by ring
    _ = A.det := by simp only [← Unitary.coe_star, hu, one_mul]

theorem logDetShift_eq_sum {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) :
    logDetShift r A = ∑ i, Real.log (1 + r * hA.isHermitian.eigenvalues i) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have he : 1 + r • A = φ (Matrix.diagonal
      (fun i ↦ ((1 + r * hA.isHermitian.eigenvalues i : ℝ) : ℂ))) := by
    have hd : Matrix.diagonal (fun i ↦ ((1 + r * hA.isHermitian.eigenvalues i : ℝ) : ℂ)) =
        1 + r • Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [hd, map_add, map_one]
    have hm : φ (r • Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ))) =
        r • φ (Matrix.diagonal (fun i ↦ (hA.isHermitian.eigenvalues i : ℂ))) :=
      (φ.toAlgEquiv.toLinearEquiv.restrictScalars ℝ).map_smul _ _
    rw [hm]
    congr 2
    exact hA.isHermitian.spectral_theorem
  unfold logDetShift
  rw [he, det_unitary_conj, Matrix.det_diagonal, norm_prod]
  have hp (i : ι) : 0 < 1 + r * hA.isHermitian.eigenvalues i :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr (hA.eigenvalues_nonneg i))
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hp _)]
  exact Real.log_prod (fun i _ ↦ (hp i).ne')

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
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.logDetShift_eq_sum := @_root_.OAI.GAD.logDetShift_eq_sum
