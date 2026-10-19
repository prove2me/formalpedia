-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.continuous_heatRow_param
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:14:09.991886+00:00
-- url     : https://prove2.me/submissions/52232d38-aa9f-4133-9cf0-865641f5307f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/JointHeat.lean:L45-L63
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.continuous_heatRow_param. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

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

-- ---- from OAI.Analysis.TriangularHilbert.JointHeat ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_weight_param {E : Type uE} [TopologicalSpace E] (h u : ℝ)
    {p σ : E → ℝ} (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ t, 0 < σ t) :
    Continuous (fun t => weight h u (p t) (σ t)) := by
  unfold weight density
  have hden : ∀ t, Real.sqrt (2*Real.pi*σ t) ≠ 0 := fun t => (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hpos t))).ne'
  apply continuous_const.mul
  apply Continuous.mul
  · exact (Real.continuous_sqrt.comp (continuous_const.mul hσ)).inv₀ hden
  · apply Real.continuous_exp.comp
    exact ((continuous_const.sub hp).pow 2 |>.neg).div (continuous_const.mul hσ) (fun t => (mul_pos (by norm_num) (hpos t)).ne')

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_heatArray_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => heatArray A h u (p t) (σ t) v) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hw (w : Three) (k : ι) : Continuous (fun t => (Real.sqrt (heatWeights h u (p t) (σ t) w k) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_weight_param h (u k) ((continuous_apply w).comp hp) ((continuous_apply w).comp hσ) (hpos · w)))
  exact ((hw v i).mul continuous_const).mul (hw (v+1) j)

lemma continuous_heatRow_param {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => rowStar (heatArray A h u (p t) (σ t)) v) := by
  have he := continuous_heatArray_param A h u hp hσ hpos
  have hb (a b : Three) : Continuous (fun t => triangleBlocks (heatArray A h u (p t) (σ t)) a b) := by
    unfold triangleBlocks
    split_ifs <;> first | exact continuous_const | exact he _ | exact (he _).star
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rowStar_apply]
  by_cases hv : a.1 = v
  · simp only [ite_eq_left hv]
    exact (continuous_apply b.2).comp ((continuous_apply a.2).comp (hb a.1 b.1))
  · simp only [ite_eq_right hv]
    exact continuous_const
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology


theorem solution.{uι,uE} : type_of% @_root_.OAI.TriangularHilbert.Heat.continuous_heatRow_param.{uι,uE} := @_root_.OAI.TriangularHilbert.Heat.continuous_heatRow_param.{uι,uE}
