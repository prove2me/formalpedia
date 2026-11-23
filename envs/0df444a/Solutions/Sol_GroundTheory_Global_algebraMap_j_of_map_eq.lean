-- Prove2me | solution 1 for GroundTheory.Global.algebraMap_j_of_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:20.891959+00:00
-- url     : https://prove2.me/submissions/c22dd4ec-43e7-4a0a-bf7d-02acb653877b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L}
    [E.IsElliptic] {W : WeierstrassCurve (localizationAt L v)} [W.IsElliptic]
    (h : W.map (algebraMap (localizationAt L v) L) = E) :
    algebraMap (localizationAt L v) L W.j = E.j := by
  subst h
  exact (W.map_j _).symm
end GroundTheory.Global
