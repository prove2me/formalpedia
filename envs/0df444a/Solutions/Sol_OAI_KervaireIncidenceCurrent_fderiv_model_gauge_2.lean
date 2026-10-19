-- Prove2me | solution 2 for OAI.KervaireIncidenceCurrent.fderiv_model_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:23:58.536808+00:00
-- url     : https://prove2.me/submissions/7acfd690-40c5-4e84-8c96-1acd9ab179f5

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/UnitaryHomotopy.lean:L265-L294
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.fderiv_model_gauge. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_incidence

-- ---- from OAI.GroupTheory.Kervaire.UnitaryHomotopy ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff

namespace KervaireUnitaryHomotopy
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]

variable {B C}

section Differential
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
attribute [local instance] OAI.KervaireUnitaryHomotopy.instNormedAlgebraRat_oAI
end Differential

end KervaireUnitaryHomotopy

namespace KervaireIncidenceCurrent

section
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

end

variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

lemma contDiff_model : ContDiff ℝ ∞ (model (K := K) (R := R)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × Mat K ↦ diag p.2 (-1))
  simp only [diag_eq_corner]
  exact ((in11 (K := K) (R := R)).contDiff.comp contDiff_snd).add contDiff_const

lemma fderiv_model (p v : ℝ × Mat K) :
    fderiv ℝ (model (K := K) (R := R)) p v = in11 v.2 := by
  have hd := (((in11 (K := K) (R := R)).hasFDerivAt).comp p
    hasFDerivAt_snd).add (hasFDerivAt_const (in22 (K := K) (R := R) (-1)) p)
  have he : (fun x : ℝ × Mat K ↦ in11 (K := K) (R := R) x.2 + in22 (-1)) = model := by
    funext x
    exact (diag_eq_corner _ _).symm
  change HasFDerivAt (fun x : ℝ × Mat K ↦ in11 (K := K) (R := R) x.2 + in22 (-1)) _ p at hd
  rw [he] at hd
  rw [hd.fderiv]
  simp

lemma fderiv_model_gauge (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R))
    (h : Horizontal K R) :
    fderiv ℝ (incidence model) (t,(gaugePoint U V : Alg K R))
      (0,(gaugePoint U V : Alg K R)*(direction h : Alg K R)) =
      (modelHorizontalEquiv U V h : Mat (K ⊕ R)) := by
  rw [fderiv_incidence contDiff_model, fderiv_model]
  change in11 (1*(h.1 : Mat K)) * diag (U : Mat K) (V : Mat R) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)) +
    diag 1 (-1) * (diag (U : Mat K) (V : Mat R)*off h.2.2) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)) +
    diag 1 (-1) * diag (U : Mat K) (V : Mat R) * in22 (star ((-1 : Mat R)*(h.2.1 : Mat R))) *
    star (diag (U : Mat K) (V : Mat R)) +
    diag 1 (-1) * diag (U : Mat K) (V : Mat R) * diag 1 (star (-1 : Mat R)) *
    star (diag (U : Mat K) (V : Mat R)*off h.2.2) = _
  have hb : star (h.2.1 : Mat R) = -(h.2.1 : Mat R) := h.2.1.property
  simp only [star_mul,star_neg,star_one,diag_star,off_skew,one_mul,neg_one_mul,hb,neg_neg]
  change _ = star (star (diag (U : Mat K) (V : Mat R))) *
    KervaireFixedSpace.derivativeMatrix 1 (skewConj U h.1) h.2.1 h.2.2 *
      star (diag (U : Mat K) (V : Mat R))
  rw [star_star,diag_star]
  have hi11 (A : Mat K) : in11 (R := R) A = fromBlocks A 0 0 0 := rfl
  have hi22 (B : Mat R) : in22 (K := K) B = fromBlocks 0 0 0 B := rfl
  simp only [hi11,hi22,diag,off,KervaireFixedSpace.derivativeMatrix,one_smul,
    skewConj,fromBlocks_multiply,fromBlocks_neg,
    Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,Matrix.one_mul,Matrix.mul_one]
  have hu : (U : Mat K)*(star (U : Mat K)*(h.1 : Mat K)) = h.1 := by
    rw [← mul_assoc,U.property.2,one_mul]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks,Matrix.mul_assoc,U.property.2,hu,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_neg,Matrix.neg_mul,two_smul]

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireIncidenceCurrent
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.fderiv_model_gauge := @_root_.OAI.KervaireIncidenceCurrent.fderiv_model_gauge
