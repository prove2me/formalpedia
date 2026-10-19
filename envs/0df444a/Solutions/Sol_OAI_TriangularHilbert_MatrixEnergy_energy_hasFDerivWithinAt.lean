-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.energy_hasFDerivWithinAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:07:43.037483+00:00
-- url     : https://prove2.me/submissions/847346f6-e49f-4e8e-b8e8-5444412911dc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean:L682-L703
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.energy_hasFDerivWithinAt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_sqrt_smoothWithin_posDef

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

theorem traceReal_mul_comm (A B : Matrix ι ι ℂ) : traceReal (A * B) = traceReal (B * A) := by
  unfold traceReal; rw [Matrix.trace_mul_comm]
theorem traceReal_mul_cycle (A B C : Matrix ι ι ℂ) :
    traceReal (A * B * C) = traceReal (C * A * B) := by
  unfold traceReal; rw [Matrix.trace_mul_cycle]
variable [DecidableEq ι]

theorem traceReal_mul_sylv (A Y : Matrix ι ι ℂ) :
    traceReal (A * sylv A Y) = 2 * traceReal (A * A * Y) := by
  simp only [sylv, mul_add, traceReal_add]
  simp only [← Matrix.mul_assoc]
  rw [traceReal_mul_cycle A Y A]
  ring

theorem energy_hasFDerivWithinAt {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    HasFDerivWithinAt energy (energyGradient P)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by
  let A := CFC.sqrt P
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive)
  let e := sylvEquiv hA
  have hd := (sqrt_smoothWithin_posDef hP).2
  change HasFDerivWithinAt CFC.sqrt (e.symm : _ →L[ℝ] _) _ P at hd
  have hmul := (hasFDerivWithinAt_id (s := {Q : Matrix ι ι ℂ | 0 ≤ Q})
    P (𝕜 := ℝ)).mul' hd
  have h := traceRealCLM.hasFDerivAt.comp_hasFDerivWithinAt P hmul
  apply h.congr_fderiv
  ext K
  change traceReal (P * e.symm K + K * A) =
    (3 / 2 : ℝ) * traceReal (A * K)
  have he : sylv A (e.symm K) = K := e.apply_symm_apply K
  have hp : A * A = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have ht := traceReal_mul_sylv A (e.symm K)
  rw [he, hp] at ht
  rw [traceReal_add, traceReal_mul_comm K A]
  linarith

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

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped BigOperators
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_hasFDerivWithinAt.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.energy_hasFDerivWithinAt.{uι}
