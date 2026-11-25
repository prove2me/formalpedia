-- Prove2me | solution 1 for GlobalTheory.ThetaPow.dotProduct_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:15.802969+00:00
-- url     : https://prove2.me/submissions/b7202c36-684a-46d2-824a-3e8221b66717

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
theorem _root_.solution {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G) (x y : Fin G → R) :
    x ⬝ᵥ y = ∑ i : Fin j, (fun k => x (e (i, k))) ⬝ᵥ (fun k => y (e (i, k))) := by
  unfold dotProduct
  rw [← e.sum_comp, Fintype.sum_prod_type]
end GlobalTheory.ThetaPow
