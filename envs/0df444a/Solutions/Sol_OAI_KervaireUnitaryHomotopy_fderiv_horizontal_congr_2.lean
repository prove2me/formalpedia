-- Prove2me | solution 2 for OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:22:18.623715+00:00
-- url     : https://prove2.me/submissions/7bc3b50a-1f68-4df8-ba9c-272c895382ab

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/UnitaryHomotopy.lean:L69-L97
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr. The node keeps its source
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
/-- Horizontal derivatives depend only on the restriction to the unitary group.
This is essential: homotopies cancel X X* only on that group, not on all matrices. -/
lemma fderiv_horizontal_congr {f g : ℝ × E → D}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t s : ℝ)
    (heq : ∀ x : unitary E, f (t,(x : E)) = g (s,(x : E)))
    (x : unitary E) (a : skewAdjoint.submodule ℝ E) :
    fderiv ℝ f (t,(x : E)) (0,(x : E)*(a : E)) =
      fderiv ℝ g (s,(x : E)) (0,(x : E)*(a : E)) := by
  let c : ℝ → E := fun r ↦ (x : E)*NormedSpace.exp (r • (a : E))
  have hc0 : c 0 = (x : E) := by simp [c]
  have hcd : HasDerivAt c ((x : E)*(a : E)) 0 := by
    have he : HasDerivAt (fun r : ℝ ↦ NormedSpace.exp (r • (a : E))) (a : E) 0 := by
      simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
        hasDerivAt_exp_smul_const (a : E) (0 : ℝ)
    exact he.const_mul (x : E)
  have hcu (r : ℝ) : c r ∈ unitary E := by
    apply (unitary E).mul_mem x.property
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (r • (a : E)) = -(r • (a : E))
    rw [star_smul,star_trivial,a.property,smul_neg]
  have hd₀ := ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0 : ℝ) t).prodMk hcd))
  have hd₁ := ((hg.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0 : ℝ) s).prodMk hcd))
  have he : (fun r ↦ f (t,c r)) = fun r ↦ g (s,c r) := funext fun r ↦ heq ⟨c r,hcu r⟩
  change HasDerivAt (fun r ↦ f (t,c r)) _ 0 at hd₀
  change HasDerivAt (fun r ↦ g (s,c r)) _ 0 at hd₁
  rw [he] at hd₀
  simpa only [hc0] using hd₀.unique hd₁

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

end KervaireIncidenceCurrent

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireUnitaryHomotopy
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
attribute [local instance] OAI.KervaireUnitaryHomotopy.instNormedAlgebraRat_oAI


theorem solution : type_of% @_root_.OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr := @_root_.OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr
