-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.span_image_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:57:41.089148+00:00
-- url     : https://prove2.me/submissions/86b9413b-eb6c-4f19-aaa6-1d534536c1c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate

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
    Submodule.span (𝓞 F) (φ.comp (algebraMap (𝓞 E) E) '' (𝔞 : Set (𝓞 E))) =
      coeI F (𝔞.map (RingOfIntegers.mapRingHom φ)) := by
  change _ = IsLocalization.coeSubmodule F (Ideal.span _)
  rw [IsLocalization.coeSubmodule_span, Set.image_image]
  rfl
end GlobalTheory.LatticeBetaCompare
