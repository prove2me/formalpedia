-- Prove2me | solution 1 for GlobalTheory.UnitaryTransitive.star_snocZeroLastCoordinate_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:17.142106+00:00
-- url     : https://prove2.me/submissions/7cdbbcfb-2439-44e3-a853-7f48da60caea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_castSucc
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_castSucc
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_last

set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitaryTransitive
variable {E : Type} [NormedField E] [StarRing E]
namespace GlobalTheory.UnitaryTransitive
theorem _root_.solution {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    star (ext0 x) ⬝ᵥ f = star x ⬝ᵥ (fun j => f j.castSucc) := by
  simp [dotProduct, Fin.sum_univ_castSucc]
end GlobalTheory.UnitaryTransitive
