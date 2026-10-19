-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.continuous_heatMask
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:43:34.833425+00:00
-- url     : https://prove2.me/submissions/d34b6446-92b4-4ac0-9b92-a32cd5bfac65

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatContinuous.lean:L54-L67
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.continuous_heatMask. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv

-- ---- from OAI.Analysis.TriangularHilbert.HeatInsert ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma heatMask_eq_diagonal (d : Three → ι → ℝ) :
    heatMask d = Matrix.diagonal (fun a : BlockSpace ι => (d a.1 a.2 : ℂ)) := by
  ext ⟨v,i⟩ ⟨w,j⟩
  by_cases hv : v = w <;> by_cases hi : i = j <;>
    simp [heatMask, blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatContinuous ----
namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma continuous_heatMask {E : Type uE} [TopologicalSpace E] {r : E → Three → ι → ℝ}
    (hr : ∀ w j, Continuous (fun x => r x w j)) : Continuous (fun x => heatMask (r x)) := by
  simp only [heatMask_eq_diagonal]
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (hr a.1 a.2)
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology


theorem solution.{uι,uE} : type_of% @_root_.OAI.TriangularHilbert.Heat.continuous_heatMask.{uι,uE} := @_root_.OAI.TriangularHilbert.Heat.continuous_heatMask.{uι,uE}
