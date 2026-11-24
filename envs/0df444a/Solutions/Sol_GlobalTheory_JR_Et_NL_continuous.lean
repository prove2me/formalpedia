-- Prove2me | solution 1 for GlobalTheory.JR.Et.NL_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:57:29.667687+00:00
-- url     : https://prove2.me/submissions/c94cb65d-34eb-4879-9f4b-54dbb5e677ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwap
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.Et
theorem _root_.solution [Unram F E] (A : Et F E) : Continuous A.NL := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [this]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hlin : Continuous (((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F) :=
    IsModuleTopology.continuous_of_linearMap _
  convert hlin using 1
  funext y
  simp [Algebra.leftMulMatrix_eq_repr_mul]
end GlobalTheory.JR.Et
