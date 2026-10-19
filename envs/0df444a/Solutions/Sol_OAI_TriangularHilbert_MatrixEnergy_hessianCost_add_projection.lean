-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.hessianCost_add_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:18:19.252981+00:00
-- url     : https://prove2.me/submissions/f8f5e360-4383-48e8-98b2-665bc4cb77ec

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Support.lean:L59-L93
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.hessianCost_add_projection. The node keeps its source
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
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_rootCost_eq_of_solution

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

variable [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrtInverse_solves {P : Matrix ι ι ℂ} (hP : P.PosDef) (K : Matrix ι ι ℂ) :
    sylv (CFC.sqrt P) (sqrtInverse hP K) = K := by
  exact (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).apply_symm_apply K

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Support ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sqrt_mul_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hPQ : P * Q = 0) : CFC.sqrt P * Q = 0 := by
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  change (CFC.sqrt P * Q)ᴴ * (CFC.sqrt P * Q) = 0
  rw [Matrix.conjTranspose_mul, hs.eq, ← Matrix.mul_assoc,
    Matrix.mul_assoc Qᴴ, CFC.sqrt_mul_sqrt_self P hP.nonneg,
    Matrix.mul_assoc, hPQ, mul_zero]

lemma mul_sqrt_eq_zero_of_mul_eq_zero {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQP : Q * P = 0) : Q * CFC.sqrt P = 0 := by
  have ht : P * Qᴴ = 0 := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hQP
  have hz := sqrt_mul_eq_zero_of_mul_eq_zero hP ht
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  simpa only [Matrix.conjTranspose_mul, hs.eq, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hz

lemma sqrt_add_projection {P Q : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    CFC.sqrt (P + Q) = CFC.sqrt P + Q := by
  apply CFC.sqrt_unique
  · have hsQ := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
    have hQs := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
    simp only [add_mul, mul_add, hsQ, hQs, hQQ,
      CFC.sqrt_mul_sqrt_self P hP.nonneg, add_zero, zero_add]
  · exact add_nonneg (CFC.sqrt_nonneg P) hQ.nonneg

lemma hessianCost_add_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianCost (P + Q) K = hessianCost P K := by
  let A := CFC.sqrt P
  let E := 1 - Q
  let Y := sqrtInverse hPD K
  let Z := E * Y * E
  have hAQ : A * Q = 0 := sqrt_mul_eq_zero_of_mul_eq_zero hP hPQ
  have hQA : Q * A = 0 := mul_sqrt_eq_zero_of_mul_eq_zero hP hQP
  have hQE : Q * E = 0 := by simp [E, mul_sub, hQQ]
  have hEQ : E * Q = 0 := by simp [E, sub_mul, hQQ]
  have hAE : A * E = A := by simp [E, mul_sub, hAQ]
  have hEA : E * A = A := by simp [E, sub_mul, hQA]
  have hKE : K * E = K := by simp [E, mul_sub, hKQ]
  have hEK : E * K = K := by simp [E, sub_mul, hQK]
  have hY : sylv (A + Q) Y = K := by
    simpa only [sqrt_add_projection hP hQ hQQ hPQ hQP] using sqrtInverse_solves hPD K
  have hZ : sylv A Z = K := by
    have hm := congrArg (fun B => E * B * E) hY
    simp only [sylv, add_mul, mul_add, Matrix.mul_assoc] at hm ⊢
    simp only [← Matrix.mul_assoc E A, hEA, ← Matrix.mul_assoc E Q, hEQ,
      zero_mul, add_zero, hQE, mul_zero,
      hEK, hKE] at hm
    simpa only [Z, Matrix.mul_assoc, ← Matrix.mul_assoc A E, hAE,
      ← Matrix.mul_assoc E A, hEA] using hm
  have hQZ : Q * Z = 0 := by simp only [Z, ← Matrix.mul_assoc, hQE, zero_mul]
  have hZQ : Z * Q = 0 := by simp only [Z, Matrix.mul_assoc, hEQ, mul_zero]
  have hZ' : sylv (CFC.sqrt (P + Q)) Z = K := by
    rw [sqrt_add_projection hP hQ hQQ hPQ hQP]
    change sylv (A + Q) Z = K
    simpa [sylv, add_mul, mul_add, hQZ, hZQ] using hZ
  exact (rootCost_eq_of_solution
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P + Q))) hZ').trans
    (rootCost_eq_of_solution (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)) hZ).symm

end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter Unitary


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.hessianCost_add_projection.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.hessianCost_add_projection.{uι}
