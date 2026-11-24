-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mom_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:33:45.806251+00:00
-- url     : https://prove2.me/submissions/ef9111bd-f626-4525-aad5-6145a047118b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_form_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (X : Hn r F E) (k : ℕ) : star (mom X.toGl k) = mom X.toGl k := by
  show star (star X.2.1 ⬝ᵥ (X.1.1 ^ k *ᵥ X.2.1)) = star X.2.1 ⬝ᵥ (X.1.1 ^ k *ᵥ X.2.1)
  conv_lhs => rw [star_dotProduct, star_star]
  rw [form_pow X.1.1 X.1.2]
end GlobalTheory.JR.HermInv
