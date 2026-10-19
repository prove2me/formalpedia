-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.exists_kernel_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:19:54.98192+00:00
-- url     : https://prove2.me/submissions/264cb16d-313c-4e23-8148-6603989d3c67

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Support.lean:L95-L145
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.exists_kernel_projection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support

-- ---- from OAI.Analysis.TriangularHilbert.Support ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma exists_kernel_projection {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧
      (P + Q).PosDef := by
  let ev := hP.isHermitian.eigenvalues
  let U := hP.isHermitian.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (ev i : ℂ))
  let q : Matrix ι ι ℂ := Matrix.diagonal (fun i => if ev i = 0 then 1 else 0)
  let Q := f q
  have hD : f D = P := hP.isHermitian.spectral_theorem.symm
  have hq : q.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ (if ev i = 0 then (1 : ℂ) else 0)
    split_ifs <;> simp
  have hQ : Q.PosSemidef := by
    simpa only [Q, f, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hq.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  have hqq : q * q = q := by
    simp only [q, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  have hQQ : Q * Q = Q := by exact (map_mul f q q).symm.trans (congrArg f hqq)
  have hDq : D * q = 0 := by
    simp only [D, q, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_zero]
    congr 1
    ext i
    split_ifs with hi <;> simp [hi]
  have hPQ : P * Q = 0 := by
    rw [← hD]
    change f D * f q = 0
    rw [← map_mul, hDq, map_zero]
  have hQP : Q * P = 0 := by
    simpa only [Matrix.conjTranspose_mul, hQ.isHermitian.eq, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hPQ
  have hpos : (D + q).PosDef := by
    simp only [D, q, Matrix.diagonal_add]
    apply Matrix.PosDef.diagonal
    intro i
    change 0 < (ev i : ℂ) + (if ev i = 0 then 1 else 0)
    by_cases hi : ev i = 0
    · simp [hi]
    · simp only [hi, ite_false, add_zero]
      exact_mod_cast lt_of_le_of_ne (hP.eigenvalues_nonneg i) (Ne.symm hi)
  have hu : IsUnit (P + Q) := by
    have hh := hpos.isUnit.map f.toMonoidHom
    change IsUnit (f (D + q)) at hh
    simpa only [map_add, hD] using hh
  exact ⟨Q, hQ, hQQ, hPQ, hQP, (hP.add hQ).posDef_iff_isUnit.mpr hu⟩

end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.exists_kernel_projection.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.exists_kernel_projection.{uι}
