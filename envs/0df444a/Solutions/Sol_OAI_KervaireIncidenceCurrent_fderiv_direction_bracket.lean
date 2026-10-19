-- Prove2me | solution 1 for OAI.KervaireIncidenceCurrent.fderiv_direction_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:17:54.829481+00:00
-- url     : https://prove2.me/submissions/0de31b48-c0ad-41ad-ad51-1d54b56ee72e

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean:L146-L177
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireIncidenceCurrent.fderiv_direction_bracket. The node keeps its source
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
import Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_frame_diagonal

-- ---- from OAI.GroupTheory.Kervaire.IncidenceSpaces ----
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

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
lemma off_bracket (Z Y : Matrix R K ℂ) :
    off Z * off Y - off Y * off Z =
      diag (-Zᴴ*Y+Yᴴ*Z) (-Z*Yᴴ+Y*Zᴴ) := by
  simp only [off, diag, fromBlocks_multiply, mul_zero, zero_add, add_zero]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, sub_eq_add_neg]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.IncidenceTangent ----
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

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
lemma direction_bracket (h g : Horizontal K R) :
    ((direction h : Alg K R)*(direction g : Alg K R)-
      (direction g : Alg K R)*(direction h : Alg K R)) =
    (direction (KervaireSkewTrace.bracket h.1 g.1,
      KervaireSkewTrace.bracket h.2.1 g.2.1,0) : Alg K R) +
    (0,diag (rectBracket h.2.2ᴴ g.2.2ᴴ : Mat K) (rectBracket h.2.2 g.2.2 : Mat R),0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [direction, KervaireSkewTrace.bracket]
  · change off h.2.2 * off g.2.2-off g.2.2*off h.2.2 = _
    rw [off_bracket]
    simp [direction, off, rectBracket]
  · simp [direction, KervaireSkewTrace.bracket]

/-- The differential of a bracket is in the span of horizontal directions,
with the explicitly computed coefficients. -/
lemma fderiv_direction_bracket {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (p : unitary (Alg K R)) (h g : Horizontal K R) :
    fderiv ℝ (incidence f) (t,(p : Alg K R))
      (0,(p : Alg K R)*((direction h : Alg K R)*(direction g : Alg K R)-
        (direction g : Alg K R)*(direction h : Alg K R))) =
    fderiv ℝ (incidence f) (t,(p : Alg K R))
      (0,(p : Alg K R)*(direction (effectiveBracket ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩ h g) : Alg K R)) := by
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  let b : Horizontal K R := (KervaireSkewTrace.bracket h.1 g.1,
    KervaireSkewTrace.bracket h.2.1 g.2.1,0)
  let c : Horizontal K R := (0,compensated T (rectBracket h.2.2 g.2.2),0)
  have he : effectiveBracket T h g = b+c := by simp [effectiveBracket,b,c]
  have hb : ((0 : ℝ),(p : Alg K R)*((direction h : Alg K R)*(direction g : Alg K R)-
        (direction g : Alg K R)*(direction h : Alg K R))) =
      (0,(p : Alg K R)*(direction b : Alg K R))+
      (0,0,p.val.2.1*diag (rectBracket h.2.2ᴴ g.2.2ᴴ : Mat K) (rectBracket h.2.2 g.2.2 : Mat R),0) := by
    rw [direction_bracket, mul_add]
    simp only [Prod.mul_def, mul_zero, Prod.add_def, add_zero]
    rfl
  rw [hb,map_add, fderiv_frame_diagonal hf t p.val.1 p.val.2.1 T
    (rectBracket h.2.2ᴴ g.2.2ᴴ) (rectBracket h.2.2 g.2.2)]
  have hc : ((0 : ℝ),0,0,p.val.2.2*(compensated T (rectBracket h.2.2 g.2.2) : Mat R)) =
      (0,(p : Alg K R)*(direction c : Alg K R)) := by
    simp [c,direction,off,Prod.mul_def]
  change _ = fderiv ℝ (incidence f) (t,(p : Alg K R))
    (0,(p : Alg K R)*(direction (effectiveBracket T h g) : Alg K R))
  rw [hc]
  change horizontalDifferential f t p b + horizontalDifferential f t p c =
    horizontalDifferential f t p (effectiveBracket T h g)
  rw [he,map_add]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
end KervaireFixedSpace
namespace KervaireIncidenceCurrent
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

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


theorem solution : type_of% @_root_.OAI.KervaireIncidenceCurrent.fderiv_direction_bracket := @_root_.OAI.KervaireIncidenceCurrent.fderiv_direction_bracket
