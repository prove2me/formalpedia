-- Prove2me | solution 1 for GlobalTheory.JR.Et.absK_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:57.277799+00:00
-- url     : https://prove2.me/submissions/75712091-f399-4184-946e-b22f3040a4b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMultiplicativeUnitOneHaarScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)
namespace GlobalTheory.JR.Et
theorem _root_.solution (x : A.Kˣ) : A.absK (x : A.K) = (distribHaarChar A.K x : ℝ) := by
  unfold absK
  rw [dif_pos x.isUnit]
  congr 2
  ext; rfl
end GlobalTheory.JR.Et
