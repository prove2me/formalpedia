-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.sqrt_smoothWithin_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:05:59.402774+00:00
-- url     : https://prove2.me/submissions/4a7160b7-9076-4104-ac1e-5c175597e4e0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean:L627-L655
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.sqrt_smoothWithin_posDef. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport

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

theorem hasFDerivAt_square {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => X * X) (sylvEquiv hA : _ →L[ℝ] _) A := by
  convert! (hasFDerivAt_id A (𝕜 := ℝ)).mul' (hasFDerivAt_id A (𝕜 := ℝ)) using 1

theorem contDiff_square {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun X : Matrix ι ι ℂ => X * X) := contDiff_id.mul contDiff_id

theorem sqrt_smoothWithin_posDef {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ContDiffWithinAt ℝ ∞ CFC.sqrt {Q : Matrix ι ι ℂ | 0 ≤ Q} P ∧
    HasFDerivWithinAt CFC.sqrt
      ((sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
        (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm : _ →L[ℝ] _)
      {Q : Matrix ι ι ℂ | 0 ≤ Q} P := by
  let A := CFC.sqrt P
  have hA : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive)
  let f : Matrix ι ι ℂ → Matrix ι ι ℂ := fun X => X * X
  have hc : ContDiffAt ℝ ∞ f A := contDiff_square.contDiffAt
  have hd : HasFDerivAt f (sylvEquiv hA : _ →L[ℝ] _) A := hasFDerivAt_square hA
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let g := hc.localInverse hd hn
  have hstrict := hc.hasStrictFDerivAt' hd hn
  have hAP : f A = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hgC : ContDiffAt ℝ ∞ g P := hAP ▸ hc.to_localInverse hd hn
  have hgD : HasFDerivAt g ((sylvEquiv hA).symm : _ →L[ℝ] _) P :=
    hAP ▸ hstrict.to_localInverse.hasFDerivAt
  have heq : g =ᶠ[nhdsWithin P {Q : Matrix ι ι ℂ | 0 ≤ Q}] CFC.sqrt := by
    have ht := (CFC.continuousOn_sqrt P hP.posSemidef.nonneg).eventually
      hstrict.eventually_left_inverse
    filter_upwards [ht, self_mem_nhdsWithin] with Q hQ hQpos
    change g (CFC.sqrt Q * CFC.sqrt Q) = CFC.sqrt Q at hQ
    rwa [CFC.sqrt_mul_sqrt_self Q hQpos] at hQ
  refine ⟨hgC.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq.symm
    hP.posSemidef.nonneg, ?_⟩
  exact hgD.hasFDerivWithinAt.congr_of_eventuallyEq heq.symm
    (heq.symm.self_of_nhdsWithin hP.posSemidef.nonneg)

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


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.sqrt_smoothWithin_posDef.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.sqrt_smoothWithin_posDef.{uι}
