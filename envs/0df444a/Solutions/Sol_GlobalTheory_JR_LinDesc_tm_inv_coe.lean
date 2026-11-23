-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.tm_inv_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:08.511386+00:00
-- url     : https://prove2.me/submissions/8164dad6-08b6-4551-9c55-2c4284b97acf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution (hG : A.IsGen τ p) (t : A.Kˣ) :
    (((tm A hG t)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Algebra.leftMulMatrix (bas A hG) ((t⁻¹ : A.Kˣ) : A.K) := by
  rw [← map_inv]; rfl
end GlobalTheory.JR.LinDesc
