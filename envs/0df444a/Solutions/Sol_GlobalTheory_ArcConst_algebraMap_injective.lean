-- Prove2me | solution 1 for GlobalTheory.ArcConst.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:11.403044+00:00
-- url     : https://prove2.me/submissions/40e34f8f-64d4-4493-83a3-c6e67d577560

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_arcDet_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.ArcConst
theorem _root_.solution (Dw : Datum H) (K : Type) [Field K] :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) :=
  IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) (S := ArcS Dw K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (arcDet_ne_zero Dw K))
end GlobalTheory.ArcConst
