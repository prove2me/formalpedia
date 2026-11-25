-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.extend_coeI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:23:40.44497+00:00
-- url     : https://prove2.me/submissions/3d03a13b-2b39-4e75-ae37-b187edce69f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_span_image_ideal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E F : Type} [Field E] [Field F] (φ : E →+* F)
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution (𝔞 : Ideal (𝓞 E)) :
    extend φ (coeI E 𝔞) = coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  rw [← span_image_ideal]
  change Submodule.span (𝓞 F) (φ '' (algebraMap (𝓞 E) E '' (𝔞 : Set (𝓞 E)))) = _
  rw [Set.image_image]
  rfl
end GlobalTheory.LatticeBetaCompare
