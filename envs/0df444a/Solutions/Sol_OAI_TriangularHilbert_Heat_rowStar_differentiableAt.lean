-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.rowStar_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:41:54.008773+00:00
-- url     : https://prove2.me/submissions/c9669bce-acb0-4e60-8fbb-2c6646aa457c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatTime.lean:L87-L100
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.rowStar_differentiableAt. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.HeatTime ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uν uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma triangleBlocks_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v w : Three) : DifferentiableAt ℝ (fun y => triangleBlocks (W y) v w) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have he v i j := (differentiableAt_pi.mp (differentiableAt_pi.mp (hW v) i) j)
  fin_cases v <;> fin_cases w <;> simp only [triangleBlocks]
  all_goals first | exact differentiableAt_const _ | exact he _ _ _ | exact (he _ _ _).star

lemma rowStar_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v : Three) : DifferentiableAt ℝ (fun y => rowStar (W y) v) x := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  simp only [rowStar_apply]
  by_cases ha : a.1 = v
  · simp only [ite_eq_left ha]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp
      (triangleBlocks_differentiableAt hW a.1 b.1) a.2) b.2
  · simp only [ite_eq_right ha]
    exact differentiableAt_const _

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter


theorem solution.{uι,uE} : type_of% @_root_.OAI.TriangularHilbert.Heat.rowStar_differentiableAt.{uι,uE} := @_root_.OAI.TriangularHilbert.Heat.rowStar_differentiableAt.{uι,uE}
