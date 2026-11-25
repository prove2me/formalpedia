-- Prove2me | solution 1 for GroundTheory.Global.eventually_residue_j_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:53.552223+00:00
-- url     : https://prove2.me/submissions/6106b3db-e8f9-4737-9dd7-3e0db5c80251

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Theorems.Thm_GroundTheory_Global_algebraMap_j_of_map_eq
import Theorems.Thm_GroundTheory_Global_eventually_isUnit_localizationAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {E E' : WeierstrassCurve L} [E.IsElliptic] [E'.IsElliptic]
    (hj : E.j ≠ E'.j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E →
          W'.map (algebraMap (localizationAt L v) L) = E' →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
  filter_upwards [eventually_isUnit_localizationAt (sub_ne_zero.mpr hj)] with v ⟨hmem, hu⟩
    W W' _ _ h h'
  have hsub : W.j - W'.j = ⟨E.j - E'.j, hmem⟩ :=
    Subtype.ext (congrArg₂ (· - ·) (algebraMap_j_of_map_eq h) (algebraMap_j_of_map_eq h'))
  intro heq
  refine (residue_ne_zero_iff_isUnit (W.j - W'.j)).mpr (hsub ▸ hu) ?_
  rw [map_sub, heq, sub_self]
end GroundTheory.Global
