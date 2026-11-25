-- Prove2me | solution 1 for GlobalTheory.ThetaPow.blockEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:45:59.562129+00:00
-- url     : https://prove2.me/submissions/a4e3c473-6e0c-4a28-9e64-27fc35d1f89e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaPow
variable {j g G : ℕ}
namespace GlobalTheory.ThetaPow
theorem _root_.solution (e : Fin j × Fin g ≃ Fin G) (m : Fin G → ℤ) (i : Fin j) (k : Fin g) :
    blockEquiv e m i k = m (e (i, k)) := rfl
end GlobalTheory.ThetaPow
